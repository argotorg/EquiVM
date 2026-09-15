import Benchmarks.Auction.InitializerStorage
import Benchmarks.Auction.SetterSource

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Auction

def initializeTop (evm : EVM.State) : Bool :=
  decide (initializingWord evm.accountMap evm.executionEnv = ⟨0⟩)

-- LIBRARY CANDIDATE: bool loads accept every nonzero storage byte.
theorem wordToElemBool (word : UInt256) :
    wordToElem .bool word = .bool (!decide (word = ⟨0⟩)) := by
  by_cases hw : word = ⟨0⟩
  · subst word; rfl
  · have hv : (word.val == 0) = false := by
      rw [beq_eq_false_iff_ne]
      intro he
      apply hw
      exact u256_inj (congrArg Fin.val he)
    simp [wordToElem, hw, hv]

theorem readInitializing (evm : EVM.State) (locals : Store)
    (hbase : locals.get? "_initializing" = none) :
    evalExpr? auctionConfig { contract := auctionContract, locals := locals } evm
      (.storage initializingRef) = .ok (.bool (!initializeTop evm)) := by
  rw [initializingRef, scalarRead evm locals "_initializing" .bool (auctionBoolLocAt ⟨0⟩ 1)
    hbase (by native_decide) rfl, loadBoolAt, wordToElemBool]
  rfl

theorem readNotInitializing (evm : EVM.State) (locals : Store)
    (hbase : locals.get? "_initializing" = none) :
    evalExpr? auctionConfig { contract := auctionContract, locals := locals } evm
      (.unary .not (.storage initializingRef)) = .ok (.bool (initializeTop evm)) := by
  simp only [evalExpr?, readInitializing evm locals hbase, EvalResult.bind, bind,
    evalUnaryOp?, EvalResult.ofOption, Bool.not_not]

theorem readInitialized (evm : EVM.State) (locals : Store)
    (hbase : locals.get? "_initialized" = none) :
    evalExpr? auctionConfig { contract := auctionContract, locals := locals } evm
      (.storage initializedRef) =
      .ok (.bool (!decide (initializedWord evm.accountMap evm.executionEnv = ⟨0⟩))) := by
  rw [initializedRef, scalarRead evm locals "_initialized" .bool (auctionBoolLoc ⟨0⟩)
    hbase (by native_decide) rfl, loadBool, wordToElemBool]
  rfl

theorem evalInitializerGuardTrue (evm : EVM.State) (locals : Store)
    (hi : locals.get? "_initializing" = none) (hz : locals.get? "_initialized" = none)
    (hg : initializingWord evm.accountMap evm.executionEnv ≠ ⟨0⟩ ∨
      initializedWord evm.accountMap evm.executionEnv = ⟨0⟩) :
    evalExpr? auctionConfig { contract := auctionContract, locals := locals } evm
      (.binary .or (.storage initializingRef) (.unary .not (.storage initializedRef))) =
      .ok (.bool true) := by
  by_cases ht : initializingWord evm.accountMap evm.executionEnv = ⟨0⟩
  · have hzero := hg.resolve_left (not_not_intro ht)
    simp only [evalExpr?, readInitializing evm locals hi, readInitialized evm locals hz,
      initializeTop, ht, hzero, decide_true, Bool.not_true, EvalResult.bind, bind,
      evalUnaryOp?, EvalResult.ofOption, Bool.not_false, pure]
  · simp only [evalExpr?, readInitializing evm locals hi, initializeTop, ht, decide_false,
      Bool.not_false, EvalResult.bind, bind, pure]

theorem evalInitializerGuardFalse (evm : EVM.State) (locals : Store)
    (hi : locals.get? "_initializing" = none) (hz : locals.get? "_initialized" = none)
    (ht : initializingWord evm.accountMap evm.executionEnv = ⟨0⟩)
    (hd : initializedWord evm.accountMap evm.executionEnv ≠ ⟨0⟩) :
    evalExpr? auctionConfig { contract := auctionContract, locals := locals } evm
      (.binary .or (.storage initializingRef) (.unary .not (.storage initializedRef))) =
      .ok (.bool false) := by
  simp only [evalExpr?, readInitializing evm locals hi, readInitialized evm locals hz,
    initializeTop, ht, hd, decide_true, decide_false, Bool.not_true, Bool.not_false,
    EvalResult.bind, bind, evalUnaryOp?, EvalResult.ofOption, pure]

def setInitializingState (evm : EVM.State) (value : Bool) : EVM.State :=
  Solm.EVM.storageStore evm evm.executionEnv.codeOwner ⟨0⟩
    (setInitializingWord (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨0⟩) value)

def setInitializedState (evm : EVM.State) : EVM.State :=
  Solm.EVM.storageStore evm evm.executionEnv.codeOwner ⟨0⟩
    (UInt256.lor (UInt256.land (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨0⟩)
      (UInt256.lnot ⟨255⟩)) ⟨1⟩)

def initializerEnteredState (evm : EVM.State) : EVM.State :=
  if initializeTop evm then setInitializedState (setInitializingState evm true) else evm

theorem assignInitializing (evm : EVM.State) (locals : Store) (value : Bool)
    (hbase : locals.get? "_initializing" = none) :
    assignStorageRef? auctionConfig { contract := auctionContract, locals := locals } evm
      .storage initializingRef (.bool value) =
      .ok ({ contract := auctionContract, locals := locals }, setInitializingState evm value) :=
  scalarWrite evm _ locals "_initializing" (.elem .bool) (auctionBoolLocAt ⟨0⟩ 1) _
    hbase (by native_decide) rfl (by trivial) (storageLocStore_initializing evm ⟨0⟩ value)

theorem assignInitialized (evm : EVM.State) (locals : Store)
    (hbase : locals.get? "_initialized" = none) :
    assignStorageRef? auctionConfig { contract := auctionContract, locals := locals } evm
      .storage initializedRef (.bool true) =
      .ok ({ contract := auctionContract, locals := locals }, setInitializedState evm) :=
  scalarWrite evm _ locals "_initialized" (.elem .bool) (auctionBoolLoc ⟨0⟩) _
    hbase (by native_decide) rfl (by trivial) (storageLocStore_bool_true_offset0 evm ⟨0⟩)

theorem initializerBeginSource (evm : EVM.State) (locals : Store)
    (hi : locals.get? "_initializing" = none) (hz : locals.get? "_initialized" = none)
    (ht : locals.get? "isTopLevelCall" = some (.bool (initializeTop evm))) :
    ExecStmt auctionConfig { contract := auctionContract, locals := locals } evm
      (.ite (.var "isTopLevelCall")
        [.assign .storage initializingRef (.boolLit true),
          .assign .storage initializedRef (.boolLit true)] [])
      (.ok { contract := auctionContract, locals := locals } (initializerEnteredState evm)) := by
  by_cases hb : initializeTop evm = true
  · rw [initializerEnteredState, if_pos hb]
    apply ExecStmt.iteTrue
    · simp only [evalExpr?, ht, hb, EvalResult.ofOption]
    · apply ExecBlock.consNormal (ExecStmt.assign (by simp [evalExpr?, pure])
        (assignInitializing evm locals true hi))
      exact assignStorageBlock (by simp [evalExpr?, pure])
        (assignInitialized (setInitializingState evm true) locals hz)
  · rw [initializerEnteredState, if_neg hb]
    apply ExecStmt.iteFalse
    · have hf : initializeTop evm = false := Bool.eq_false_iff.mpr hb
      simp only [evalExpr?, ht, hf, EvalResult.ofOption]
    · exact ExecBlock.nil

end Auction
