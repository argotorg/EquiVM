import Reasoning.SolmArithmetic
import Benchmarks.UniswapV3.Pool.Routines
import Benchmarks.UniswapV3.Pool.Slot0Storage
import Benchmarks.UniswapV3.Pool.FactoryOwner
import Benchmarks.UniswapV3.Pool.SourceExpressions

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables Benchmarks.UniswapV3.Pool.Immutables

namespace Benchmarks.UniswapV3.Pool
set_option maxRecDepth 10000

def setFeeProtocolLocals (fp0 fp1 : UInt256) : Store :=
  ((∅ : Store).insert "feeProtocol0" (.int (Int.ofNat fp0.toNat))).insert
    "feeProtocol1" (.int (Int.ofNat fp1.toNat))

def setFeeProtocolFrame (v : UniswapV3PoolImmutables) (fp0 fp1 : UInt256) : Frame :=
  { contract := contract, locals := setFeeProtocolLocals fp0 fp1, immutables := immStore v }

theorem evalSetFeeProtocolUnlocked (v : UniswapV3PoolImmutables) (evm : EVM.State)
    (fp0 fp1 : UInt256) :
    evalExpr? config (setFeeProtocolFrame v fp0 fp1) evm
      (.storage ⟨"slot0", [.field "unlocked"]⟩) =
      .ok (.bool (!decide (slot0FieldWord 30 1 evm.accountMap evm.executionEnv = ⟨0⟩))) := by
  rw [← wordToElemBool]
  exact evalSlot0Unlocked _ _ _ (by simp [setFeeProtocolLocals])

theorem setFeeProtocolRevertsLocked (v : UniswapV3PoolImmutables) (evm : EVM.State)
    (fp0 fp1 : UInt256) (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hlocked : slot0FieldWord 30 1 evm.accountMap evm.executionEnv = ⟨0⟩) :
    ExecTransitionBody config contract evm (setFeeProtocolLocals fp0 fp1)
      setFeeProtocolTransition.body .reverted (immStore v) := by
  apply ExecFuncBody.execBlockRevert
  apply (ABlock.start.requireStep (evalCallvalueEq_true hwv)).requireRevert
  simpa only [hlocked, decide_true, Bool.not_true] using evalSetFeeProtocolUnlocked v evm fp0 fp1

theorem setFeeProtocolAssignLock (v : UniswapV3PoolImmutables) (evm : EVM.State)
    (fp0 fp1 : UInt256) :
    ExecStmt config (setFeeProtocolFrame v fp0 fp1) evm
      (.assign .storage ⟨"slot0", [.field "unlocked"]⟩ (.boolLit false))
      (.ok (setFeeProtocolFrame v fp0 fp1) (storeSlot0Unlocked evm false)) := by
  exact ExecStmt.assign (by simp only [evalExpr?, pure])
    (assignSlot0Unlocked evm _ _ false (by simp [setFeeProtocolLocals]))

theorem setFeeProtocolLockPrefix (v : UniswapV3PoolImmutables) (evm : EVM.State)
    (fp0 fp1 : UInt256) (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hunlocked : slot0FieldWord 30 1 evm.accountMap evm.executionEnv ≠ ⟨0⟩) :
    ExecBlock config (setFeeProtocolFrame v fp0 fp1) evm (setFeeProtocolTransition.body.take 3)
      (.ok (setFeeProtocolFrame v fp0 fp1) (storeSlot0Unlocked evm false)) := by
  apply (ABlock.start.requireStep (evalCallvalueEq_true hwv)).run
  refine ExecBlock.consNormal (ExecStmt.requireTrue ?_) ?_
  · simpa only [hunlocked, decide_false, Bool.not_false] using
      evalSetFeeProtocolUnlocked v evm fp0 fp1
  · exact ExecBlock.consNormal (setFeeProtocolAssignLock v evm fp0 fp1) ExecBlock.nil

theorem setFeeProtocolStatic (v : UniswapV3PoolImmutables) (evm : EVM.State)
    (fp0 fp1 : UInt256) (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hunlocked : slot0FieldWord 30 1 evm.accountMap evm.executionEnv ≠ ⟨0⟩)
    (hperm : evm.executionEnv.perm = false) :
    ExecTransitionBody config contract evm (setFeeProtocolLocals fp0 fp1)
      setFeeProtocolTransition.body .staticViolation (immStore v) := by
  apply ExecFuncBody.execBlockStatic
  apply (ABlock.start.requireStep (evalCallvalueEq_true hwv)).run
  refine ExecBlock.consNormal (ExecStmt.requireTrue ?_) ?_
  · simpa only [hunlocked, decide_false, Bool.not_false] using
      evalSetFeeProtocolUnlocked v evm fp0 fp1
  · exact ExecBlock.consStatic (execStmt_assign_static
      (setFeeProtocolAssignLock v evm fp0 fp1) hperm)

theorem setFeeProtocolFactoryReverts (v : UniswapV3PoolImmutables) (evm : EVM.State)
    (fp0 fp1 : UInt256) (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hunlocked : slot0FieldWord 30 1 evm.accountMap evm.executionEnv ≠ ⟨0⟩)
    (hfactory : ExecFuncBody config
      { contract := contract, locals := ∅, immutables := immStore v }
      (storeSlot0Unlocked evm false) factoryOwnerFunction.body .reverted) :
    ExecTransitionBody config contract evm (setFeeProtocolLocals fp0 fp1)
      setFeeProtocolTransition.body .reverted (immStore v) := by
  apply ExecFuncBody.execBlockRevert
  rw [← List.take_append_drop 3 setFeeProtocolTransition.body]
  apply execBlock_append_ok (setFeeProtocolLockPrefix v evm fp0 fp1 hwv hunlocked)
  apply ExecBlock.consRevert
  exact internalCallFunctionRevert (argVals := []) (locals := ∅)
    (by simp only [evalExprs?, pure]) factoryOwnerLookup rfl hfactory

def feeProtocolValid (word : UInt256) : Bool :=
  decide (word.toNat = 0 ∨ 4 ≤ word.toNat ∧ word.toNat ≤ 10)

def feeProtocolValidExpr (name : Ident) : Expr :=
  .binary .or (.binary .eq (.var name) (.intLit 0))
    (.binary .and (.binary .ge (.var name) (.intLit 4))
      (.binary .le (.var name) (.intLit 10)))

theorem evalFeeProtocolValid {cfg : Config} {frame : Frame} {evm : EVM.State}
    (name : Ident) (word : UInt256)
    (hword : frame.locals.get? name = some (.int (Int.ofNat word.toNat))) :
    evalExpr? cfg frame evm (feeProtocolValidExpr name) = .ok (.bool (feeProtocolValid word)) := by
  have hv := evalExpr_var_get (cfg := cfg) (evm := evm) hword
  have heq : evalExpr? cfg frame evm (.binary .eq (.var name) (.intLit 0)) =
      .ok (.bool (decide (word.toNat = 0))) := evalExpr_nat_eq_zero hv
  have hge : evalExpr? cfg frame evm (.binary .ge (.var name) (.intLit 4)) =
      .ok (.bool (decide (4 ≤ word.toNat))) := by
    simp [evalExpr?, hv, evalBinaryOp?, bind, EvalResult.bind, pure]
  have hle : evalExpr? cfg frame evm (.binary .le (.var name) (.intLit 10)) =
      .ok (.bool (decide (word.toNat ≤ 10))) := by
    simp [evalExpr?, hv, evalBinaryOp?, bind, EvalResult.bind, pure]
  simpa only [feeProtocolValid, feeProtocolValidExpr, Bool.decide_or, Bool.decide_and] using
    evalExpr_bool_or heq (evalExpr_bool_and hge hle)

def setFeeProtocolOwnerFrame (v : UniswapV3PoolImmutables) (fp0 fp1 : UInt256)
    (owner : AccountAddress) : Frame :=
  { (setFeeProtocolFrame v fp0 fp1) with
    locals := (setFeeProtocolLocals fp0 fp1).insert "__c0" (.address owner) }

theorem setFeeProtocolCallOwner (v : UniswapV3PoolImmutables) (evm evm' : EVM.State)
    (fp0 fp1 : UInt256) (owner : AccountAddress) (calleeFrame : Frame)
    (hfactory : ExecFuncBody config
      { contract := contract, locals := ∅, immutables := immStore v }
      (storeSlot0Unlocked evm false) factoryOwnerFunction.body
      (.returned calleeFrame evm' (some [.address owner]))) :
    ExecStmt config (setFeeProtocolFrame v fp0 fp1) (storeSlot0Unlocked evm false)
      (.internalCall "factoryOwner" [] "__c0")
      (.ok (setFeeProtocolOwnerFrame v fp0 fp1 owner) evm') := by
  exact internalCallFunctionReturn (args := []) (argVals := []) (locals := ∅)
    (caller := setFeeProtocolFrame v fp0 fp1) (retVar := "__c0")
    (by simp only [evalExprs?, pure]) factoryOwnerLookup rfl hfactory

theorem evalSetFeeProtocolOwner (v : UniswapV3PoolImmutables) (evm : EVM.State)
    (fp0 fp1 : UInt256) (owner : AccountAddress) :
    evalExpr? config (setFeeProtocolOwnerFrame v fp0 fp1 owner) evm
      (.binary .eq (.env .caller) (.var "__c0")) =
      .ok (.bool (decide (evm.executionEnv.source = owner))) := by
  have hv : evalExpr? config (setFeeProtocolOwnerFrame v fp0 fp1 owner) evm (.var "__c0") =
      .ok (.address owner) := evalExpr_var_get (by simp [setFeeProtocolOwnerFrame])
  simp [evalExpr?, hv, bind, EvalResult.bind, pure, evalBinaryOp?, envValue]
  apply Bool.eq_iff_iff.mpr
  simp

theorem setFeeProtocolRevertsOwner (v : UniswapV3PoolImmutables) (evm evm' : EVM.State)
    (fp0 fp1 : UInt256) (owner : AccountAddress) (calleeFrame : Frame)
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hunlocked : slot0FieldWord 30 1 evm.accountMap evm.executionEnv ≠ ⟨0⟩)
    (hfactory : ExecFuncBody config
      { contract := contract, locals := ∅, immutables := immStore v }
      (storeSlot0Unlocked evm false) factoryOwnerFunction.body
      (.returned calleeFrame evm' (some [.address owner])))
    (howner : evm'.executionEnv.source ≠ owner) :
    ExecTransitionBody config contract evm (setFeeProtocolLocals fp0 fp1)
      setFeeProtocolTransition.body .reverted (immStore v) := by
  apply ExecFuncBody.execBlockRevert
  rw [← List.take_append_drop 3 setFeeProtocolTransition.body]
  apply execBlock_append_ok (setFeeProtocolLockPrefix v evm fp0 fp1 hwv hunlocked)
  apply ExecBlock.consNormal (setFeeProtocolCallOwner v evm evm' fp0 fp1 owner calleeFrame hfactory)
  apply ExecBlock.consRevert
  apply ExecStmt.requireFalse
  simpa only [howner, decide_false] using evalSetFeeProtocolOwner v evm' fp0 fp1 owner

theorem setFeeProtocolOwnerPrefix (v : UniswapV3PoolImmutables) (evm evm' : EVM.State)
    (fp0 fp1 : UInt256) (owner : AccountAddress) (calleeFrame : Frame)
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hunlocked : slot0FieldWord 30 1 evm.accountMap evm.executionEnv ≠ ⟨0⟩)
    (hfactory : ExecFuncBody config
      { contract := contract, locals := ∅, immutables := immStore v }
      (storeSlot0Unlocked evm false) factoryOwnerFunction.body
      (.returned calleeFrame evm' (some [.address owner])))
    (howner : evm'.executionEnv.source = owner) :
    ExecBlock config (setFeeProtocolFrame v fp0 fp1) evm (setFeeProtocolTransition.body.take 5)
      (.ok (setFeeProtocolOwnerFrame v fp0 fp1 owner) evm') := by
  change ExecBlock _ _ _ (setFeeProtocolTransition.body.take 3 ++
    [.internalCall "factoryOwner" [] "__c0",
     .require (.binary .eq (.env .caller) (.var "__c0"))]) _
  apply execBlock_append_ok (setFeeProtocolLockPrefix v evm fp0 fp1 hwv hunlocked)
  apply ExecBlock.consNormal (setFeeProtocolCallOwner v evm evm' fp0 fp1 owner calleeFrame hfactory)
  refine ExecBlock.consNormal (ExecStmt.requireTrue ?_) ExecBlock.nil
  simpa only [howner, decide_true] using evalSetFeeProtocolOwner v evm' fp0 fp1 owner

theorem evalSetFeeProtocolValid (v : UniswapV3PoolImmutables) (evm : EVM.State)
    (fp0 fp1 : UInt256) (owner : AccountAddress) :
    evalExpr? config (setFeeProtocolOwnerFrame v fp0 fp1 owner) evm
      (.binary .and (feeProtocolValidExpr "feeProtocol0") (feeProtocolValidExpr "feeProtocol1")) =
      .ok (.bool (feeProtocolValid fp0 && feeProtocolValid fp1)) := by
  exact evalExpr_bool_and
    (evalFeeProtocolValid "feeProtocol0" fp0 (by
      simp [setFeeProtocolOwnerFrame, setFeeProtocolLocals, Std.HashMap.getElem_insert]))
    (evalFeeProtocolValid "feeProtocol1" fp1 (by
      simp [setFeeProtocolOwnerFrame, setFeeProtocolLocals, Std.HashMap.getElem_insert]))

theorem setFeeProtocolRevertsInvalid (v : UniswapV3PoolImmutables) (evm evm' : EVM.State)
    (fp0 fp1 : UInt256) (owner : AccountAddress) (calleeFrame : Frame)
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hunlocked : slot0FieldWord 30 1 evm.accountMap evm.executionEnv ≠ ⟨0⟩)
    (hfactory : ExecFuncBody config
      { contract := contract, locals := ∅, immutables := immStore v }
      (storeSlot0Unlocked evm false) factoryOwnerFunction.body
      (.returned calleeFrame evm' (some [.address owner])))
    (howner : evm'.executionEnv.source = owner)
    (hvalid : (feeProtocolValid fp0 && feeProtocolValid fp1) = false) :
    ExecTransitionBody config contract evm (setFeeProtocolLocals fp0 fp1)
      setFeeProtocolTransition.body .reverted (immStore v) := by
  apply ExecFuncBody.execBlockRevert
  rw [← List.take_append_drop 5 setFeeProtocolTransition.body]
  apply execBlock_append_ok
    (setFeeProtocolOwnerPrefix v evm evm' fp0 fp1 owner calleeFrame hwv hunlocked hfactory howner)
  apply ExecBlock.consRevert
  apply ExecStmt.requireFalse
  simpa only [hvalid] using evalSetFeeProtocolValid v evm' fp0 fp1 owner

def setFeeProtocolValue (fp0 fp1 : UInt256) : UInt256 :=
  UInt256.ofNat (fp0.toNat + 16 * fp1.toNat)

def setFeeProtocolFinalFrame (v : UniswapV3PoolImmutables) (fp0 fp1 old : UInt256)
    (owner : AccountAddress) : Frame :=
  { (setFeeProtocolOwnerFrame v fp0 fp1 owner) with
    locals := (setFeeProtocolOwnerFrame v fp0 fp1 owner).locals.insert
      "feeProtocolOld" (.int (Int.ofNat old.toNat)) }

theorem feeProtocolValid_le (word : UInt256) (h : feeProtocolValid word = true) :
    word.toNat ≤ 10 := by
  simp only [feeProtocolValid, decide_eq_true_eq] at h
  omega

theorem setFeeProtocolValue_toNat (fp0 fp1 : UInt256)
    (h0 : fp0.toNat ≤ 10) (h1 : fp1.toNat ≤ 10) :
    (setFeeProtocolValue fp0 fp1).toNat = fp0.toNat + 16 * fp1.toNat := by
  apply ulit_toNat'
  change _ < 2 ^ 256
  omega

theorem evalSetFeeProtocolValue (v : UniswapV3PoolImmutables) (evm : EVM.State)
    (fp0 fp1 old : UInt256) (owner : AccountAddress)
    (h0 : fp0.toNat ≤ 10) (h1 : fp1.toNat ≤ 10) :
    evalExpr? config (setFeeProtocolFinalFrame v fp0 fp1 old owner) evm
      (.cast (.binary .add (.var "feeProtocol0")
        (.binary (.shl (.uint ⟨8, by decide⟩)) (.var "feeProtocol1") (.intLit 4)))
        (.elem (.int (.uint ⟨8, by decide⟩)))) =
      .ok (.int (Int.ofNat (setFeeProtocolValue fp0 fp1).toNat)) := by
  have he0 : evalExpr? config (setFeeProtocolFinalFrame v fp0 fp1 old owner) evm
      (.var "feeProtocol0") = .ok (.int (Int.ofNat fp0.toNat)) :=
    evalExpr_var_get (by simp [setFeeProtocolFinalFrame, setFeeProtocolOwnerFrame,
      setFeeProtocolLocals, Std.HashMap.getElem_insert])
  have he1 : evalExpr? config (setFeeProtocolFinalFrame v fp0 fp1 old owner) evm
      (.var "feeProtocol1") = .ok (.int (Int.ofNat fp1.toNat)) :=
    evalExpr_var_get (by simp [setFeeProtocolFinalFrame, setFeeProtocolOwnerFrame,
      setFeeProtocolLocals, Std.HashMap.getElem_insert])
  have hs := evalExpr_uintShiftLeft ⟨8, by decide⟩ fp1.toNat 4 he1 (by decide) (by change fp1.toNat * 16 < 256; omega)
  have hc := evalExpr_intCast (.uint ⟨8, by decide⟩) (naturalAddSource he0 hs)
  rw [setFeeProtocolValue_toNat fp0 fp1 h0 h1]
  have hnorm : normalizeInt (.uint ⟨8, by decide⟩)
      (Int.ofNat (fp0.toNat + fp1.toNat * 2 ^ 4)) =
      Int.ofNat (fp0.toNat + 16 * fp1.toNat) := by
    rw [normalizeInt_uint_eq_self ⟨8, by decide⟩
      (Int.ofNat (fp0.toNat + fp1.toNat * 2 ^ 4)) (by simp only [Int.ofNat_eq_natCast]; positivity) (by
      change Int.ofNat (fp0.toNat + fp1.toNat * 16) < 256
      simp only [Int.ofNat_eq_natCast, Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat]
      omega)]
    simp [Nat.mul_comm]
  simpa only [hnorm] using hc


theorem evalSetFeeProtocolEvent (v : UniswapV3PoolImmutables) (evm : EVM.State)
    (fp0 fp1 old : UInt256) (owner : AccountAddress) :
    ∃ vals, evalExprs? config (setFeeProtocolFinalFrame v fp0 fp1 old owner) evm
      [.binary .mod (.var "feeProtocolOld") (.intLit 16),
       .binary (.shr (.uint ⟨8, by decide⟩)) (.var "feeProtocolOld") (.intLit 4),
       .var "feeProtocol0", .var "feeProtocol1"] = .ok vals := by
  have heOld : evalExpr? config (setFeeProtocolFinalFrame v fp0 fp1 old owner) evm
      (.var "feeProtocolOld") = .ok (.int (Int.ofNat old.toNat)) :=
    evalExpr_var_get (by simp [setFeeProtocolFinalFrame])
  have he0 : evalExpr? config (setFeeProtocolFinalFrame v fp0 fp1 old owner) evm
      (.var "feeProtocol0") = .ok (.int (Int.ofNat fp0.toNat)) :=
    evalExpr_var_get (by simp [setFeeProtocolFinalFrame, setFeeProtocolOwnerFrame,
      setFeeProtocolLocals, Std.HashMap.getElem_insert])
  have he1 : evalExpr? config (setFeeProtocolFinalFrame v fp0 fp1 old owner) evm
      (.var "feeProtocol1") = .ok (.int (Int.ofNat fp1.toNat)) :=
    evalExpr_var_get (by simp [setFeeProtocolFinalFrame, setFeeProtocolOwnerFrame,
      setFeeProtocolLocals, Std.HashMap.getElem_insert])
  have hm := evalExpr_mod_intLit (modulus := 16) heOld (by decide)
  have hs := evalExpr_uintShiftRight ⟨8, by decide⟩ old.toNat 4 heOld (by decide)
  simp only [show Int.ofNat 4 = (4 : Int) from rfl] at hs
  refine ⟨[.int (Int.ofNat old.toNat % 16),
    .int (normalizeInt (.uint ⟨8, by decide⟩) (Int.ofNat old.toNat) / Int.ofNat (2 ^ 4)),
    .int (Int.ofNat fp0.toNat), .int (Int.ofNat fp1.toNat)], ?_⟩
  simp only [evalExprs?, hm, hs, he0, he1, bind, EvalResult.bind, pure]

theorem setFeeProtocolReturns (v : UniswapV3PoolImmutables) (evm evm' : EVM.State)
    (fp0 fp1 : UInt256) (owner : AccountAddress) (calleeFrame : Frame)
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hunlocked : slot0FieldWord 30 1 evm.accountMap evm.executionEnv ≠ ⟨0⟩)
    (hfactory : ExecFuncBody config
      { contract := contract, locals := ∅, immutables := immStore v }
      (storeSlot0Unlocked evm false) factoryOwnerFunction.body
      (.returned calleeFrame evm' (some [.address owner])))
    (howner : evm'.executionEnv.source = owner)
    (hvalid : (feeProtocolValid fp0 && feeProtocolValid fp1) = true) :
    ExecTransitionBody config contract evm (setFeeProtocolLocals fp0 fp1)
      setFeeProtocolTransition.body
      (.returned (setFeeProtocolFinalFrame v fp0 fp1
        (slot0FieldWord 29 1 evm'.accountMap evm'.executionEnv) owner)
        (storeSlot0Unlocked (storeSlot0FeeProtocol evm' (setFeeProtocolValue fp0 fp1)) true) none)
      (immStore v) := by
  have hvalids := Bool.and_eq_true_iff.mp hvalid
  have h0 := feeProtocolValid_le fp0 hvalids.1
  have h1 := feeProtocolValid_le fp1 hvalids.2
  apply ExecFuncBody.execBlockOK
  rw [← List.take_append_drop 5 setFeeProtocolTransition.body]
  apply execBlock_append_ok
    (setFeeProtocolOwnerPrefix v evm evm' fp0 fp1 owner calleeFrame hwv hunlocked hfactory howner)
  refine ExecBlock.consNormal (ExecStmt.requireTrue ?_) ?_
  · simpa only [hvalid] using evalSetFeeProtocolValid v evm' fp0 fp1 owner
  have hbase : (setFeeProtocolOwnerFrame v fp0 fp1 owner).locals.get? "slot0" = none := by
    simp [setFeeProtocolOwnerFrame, setFeeProtocolLocals]
  apply ExecBlock.consNormal (ExecStmt.letDecl (evalSlot0FeeProtocol _ _ _ hbase))
  change ExecBlock config
    (setFeeProtocolFinalFrame v fp0 fp1 (slot0FieldWord 29 1 evm'.accountMap evm'.executionEnv) owner)
    evm' _ _
  have hbase' : (setFeeProtocolFinalFrame v fp0 fp1
      (slot0FieldWord 29 1 evm'.accountMap evm'.executionEnv) owner).locals.get? "slot0" = none := by
    simp [setFeeProtocolFinalFrame, setFeeProtocolOwnerFrame, setFeeProtocolLocals]
  apply ExecBlock.consNormal (ExecStmt.assign (evalSetFeeProtocolValue v evm' fp0 fp1 _ owner h0 h1)
    (assignSlot0FeeProtocol evm' _ _ (setFeeProtocolValue fp0 fp1) hbase'))
  obtain ⟨vals, hemit⟩ := evalSetFeeProtocolEvent v
    (storeSlot0FeeProtocol evm' (setFeeProtocolValue fp0 fp1)) fp0 fp1
    (slot0FieldWord 29 1 evm'.accountMap evm'.executionEnv) owner
  apply ExecBlock.consNormal (ExecStmt.emit hemit)
  refine ExecBlock.consNormal (ExecStmt.assign ?_ (assignSlot0Unlocked _ _ _ true hbase')) ExecBlock.nil
  simp only [evalExpr?, pure]

end Benchmarks.UniswapV3.Pool
