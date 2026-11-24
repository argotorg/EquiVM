import Benchmarks.Auction.SetterSource

variable {fork : Ethereum.Fork}

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Auction

def pausedWord (σ : AccountMap) (I : ExecutionEnv) : UInt256 :=
  UInt256.land (solcSlotWord σ I ⟨51⟩) ⟨255⟩

def pauseWord (old : UInt256) : UInt256 :=
  UInt256.lor (UInt256.land old (UInt256.lnot ⟨255⟩)) ⟨1⟩

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

theorem pauseBlockSplit (evm : EVM.State) (locals : Store)
    (hbase : locals.get? "_paused" = none)
    (hp : pausedWord evm.accountMap evm.executionEnv = ⟨0⟩) :
    (evm.executionEnv.perm = true → ExecBlock fork auctionConfig { contract := auctionContract, locals := locals } evm
      [.require (.unary .not (.storage pausedRef)), .assign .storage pausedRef (.boolLit true)]
      (.ok { contract := auctionContract, locals := locals }
        (Stele.EVM.storageStore evm evm.executionEnv.codeOwner ⟨51⟩
          (pauseWord (Stele.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨51⟩))))) ∧
      (evm.executionEnv.perm = false →
        ExecBlock fork auctionConfig { contract := auctionContract, locals := locals } evm
        [.require (.unary .not (.storage pausedRef)), .assign .storage pausedRef (.boolLit true)]
        .staticViolation) := by
  have hguard := readNotPausedTrue evm locals hbase hp
  have hvalue : evalExpr? auctionConfig { contract := auctionContract, locals := locals }
      evm (.boolLit true) = .ok (.bool true) := by simp only [evalExpr?, pure]
  have hassign := scalarWrite evm _ locals "_paused" (.elem .bool)
    (auctionBoolLoc ⟨51⟩) (.bool true) hbase (by native_decide) rfl (by exact Or.inl ⟨_, rfl⟩)
    (storageLocStore_bool_true_offset0 evm ⟨51⟩)
  constructor
  · intro hperm
    exact ExecBlock.consNormal (ExecStmt.requireTrue hguard) (assignStorageBlock hvalue hassign hperm)
  · intro hperm
    exact ExecBlock.consNormal (ExecStmt.requireTrue hguard)
      (ExecBlock.consStatic (ExecStmt.assignStatic hvalue hassign hperm))

theorem pauseBlock (evm : EVM.State) (locals : Store)
    (hbase : locals.get? "_paused" = none)
    (hp : pausedWord evm.accountMap evm.executionEnv = ⟨0⟩)
    (hperm : evm.executionEnv.perm = true) :
    ExecBlock fork auctionConfig { contract := auctionContract, locals := locals } evm
      [.require (.unary .not (.storage pausedRef)), .assign .storage pausedRef (.boolLit true)]
      (.ok { contract := auctionContract, locals := locals }
        (Stele.EVM.storageStore evm evm.executionEnv.codeOwner ⟨51⟩
          (pauseWord (Stele.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨51⟩)))) :=
  (pauseBlockSplit evm locals hbase hp).1 hperm

theorem pauseBlockReverts (evm : EVM.State) (locals : Store)
    (hbase : locals.get? "_paused" = none)
    (hp : pausedWord evm.accountMap evm.executionEnv ≠ ⟨0⟩) :
    ExecBlock fork auctionConfig { contract := auctionContract, locals := locals } evm
      [.require (.unary .not (.storage pausedRef)), .assign .storage pausedRef (.boolLit true)]
      .reverted :=
  ExecBlock.consRevert (ExecStmt.requireFalse (readNotPausedFalse evm locals hbase hp))

end Auction
