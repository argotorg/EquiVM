import Solm.Benchmarks.Auction.SetterSource

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Auction

def pausedWord (σ : AccountMap) (I : ExecutionEnv) : UInt256 :=
  UInt256.land (storedWord σ I ⟨51⟩) ⟨255⟩

def pauseWord (old : UInt256) : UInt256 :=
  UInt256.lor (UInt256.land old (UInt256.lnot ⟨255⟩)) ⟨1⟩

theorem pausedWord_equiv {σ₁ σ₂ : AccountMap} (h : accountMapEquiv σ₁ σ₂)
    (I : ExecutionEnv) : pausedWord σ₁ I = pausedWord σ₂ I := by
  rw [pausedWord, pausedWord, storedWord_equiv h]

theorem readPausedFalse (evm : EVM.State) (locals : Store)
    (hbase : locals.get? "_paused" = none)
    (hp : pausedWord evm.accountMap evm.executionEnv = ⟨0⟩) :
    evalExpr? auctionConfig { contract := auctionContract, locals := locals } evm
      (.storage pausedRef) = .ok (.bool false) := by
  rw [pausedRef, scalarRead evm locals "_paused" .bool (auctionBoolLoc ⟨51⟩)
    hbase (by native_decide) rfl]
  exact congrArg EvalResult.ok (storageLocLoad_bool_offset0_false evm ⟨51⟩ hp)

theorem readPausedTrue (evm : EVM.State) (locals : Store)
    (hbase : locals.get? "_paused" = none)
    (hp : pausedWord evm.accountMap evm.executionEnv ≠ ⟨0⟩) :
    evalExpr? auctionConfig { contract := auctionContract, locals := locals } evm
      (.storage pausedRef) = .ok (.bool true) := by
  rw [pausedRef, scalarRead evm locals "_paused" .bool (auctionBoolLoc ⟨51⟩)
    hbase (by native_decide) rfl]
  exact congrArg EvalResult.ok (storageLocLoad_bool_offset0_true evm ⟨51⟩ hp)

theorem readNotPausedTrue (evm : EVM.State) (locals : Store)
    (hbase : locals.get? "_paused" = none)
    (hp : pausedWord evm.accountMap evm.executionEnv = ⟨0⟩) :
    evalExpr? auctionConfig { contract := auctionContract, locals := locals } evm
      (.unary .not (.storage pausedRef)) = .ok (.bool true) := by
  simp only [evalExpr?, readPausedFalse evm locals hbase hp, EvalResult.bind, bind,
    evalUnaryOp?, EvalResult.ofOption, Bool.not_false]

theorem readNotPausedFalse (evm : EVM.State) (locals : Store)
    (hbase : locals.get? "_paused" = none)
    (hp : pausedWord evm.accountMap evm.executionEnv ≠ ⟨0⟩) :
    evalExpr? auctionConfig { contract := auctionContract, locals := locals } evm
      (.unary .not (.storage pausedRef)) = .ok (.bool false) := by
  simp only [evalExpr?, readPausedTrue evm locals hbase hp, EvalResult.bind, bind,
    evalUnaryOp?, EvalResult.ofOption, Bool.not_true]

theorem pauseBlock (evm : EVM.State) (locals : Store)
    (hbase : locals.get? "_paused" = none)
    (hp : pausedWord evm.accountMap evm.executionEnv = ⟨0⟩) :
    ExecBlock auctionConfig { contract := auctionContract, locals := locals } evm
      [.require (.unary .not (.storage pausedRef)), .assign .storage pausedRef (.boolLit true)]
      (.ok { contract := auctionContract, locals := locals }
        (Solm.EVM.storageStore evm evm.executionEnv.codeOwner ⟨51⟩
          (pauseWord (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨51⟩)))) := by
  apply ExecBlock.consNormal (ExecStmt.requireTrue (readNotPausedTrue evm locals hbase hp))
  exact assignStorageBlock (by simp [evalExpr?, pure])
    (scalarWrite evm _ locals "_paused" (.elem .bool) (auctionBoolLoc ⟨51⟩) (.bool true)
      hbase (by native_decide) rfl (by trivial) (storageLocStore_bool_true_offset0 evm ⟨51⟩))

theorem pauseBlockReverts (evm : EVM.State) (locals : Store)
    (hbase : locals.get? "_paused" = none)
    (hp : pausedWord evm.accountMap evm.executionEnv ≠ ⟨0⟩) :
    ExecBlock auctionConfig { contract := auctionContract, locals := locals } evm
      [.require (.unary .not (.storage pausedRef)), .assign .storage pausedRef (.boolLit true)]
      .reverted :=
  ExecBlock.consRevert (ExecStmt.requireFalse (readNotPausedFalse evm locals hbase hp))

end Auction
