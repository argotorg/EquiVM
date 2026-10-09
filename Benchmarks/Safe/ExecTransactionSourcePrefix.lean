import Benchmarks.Safe.ExecTransactionContext
import Benchmarks.Safe.OwnerStorage
import Benchmarks.Safe.Operation
import Benchmarks.Safe.ModuleCallerSource

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Safe

set_option maxRecDepth 100000

theorem safeExecTransactionChecks (p : ExecTransactionInput) (evm : EVM.State)
    {result : ExecResult} (hn : p.signatures.size ≤ 2 ^ 64 - 192)
    (ho : p.tx.operation.toNat < 2)
    (ht : ExecBlock config p.frame evm (exectransactionTransition.body.drop 2) result) :
    ExecBlock config p.frame evm exectransactionTransition.body result :=
  .consNormal (.requireTrue ((evalLocalBytesLengthLe (cfg := config)
    (frame := p.frame) (evm := evm) (2 ^ 64 - 192)
    (ExecTransactionLocals.initial p).signatures).trans (by congr 2; exact decide_eq_true hn)))
    (.consNormal (.requireTrue ((evalValidOperation (cfg := config) (frame := p.frame) (evm := evm)
      (ExecTransactionLocals.initial p).tx.operation).trans
        (by congr 2; exact decide_eq_true ho))) ht)

theorem safeExecTransactionLargeSignatures (p : ExecTransactionInput) (evm : EVM.State)
    (hn : ¬p.signatures.size ≤ 2 ^ 64 - 192) :
    ExecBlock config p.frame evm exectransactionTransition.body .reverted :=
  .consRevert (.requireFalse ((evalLocalBytesLengthLe (cfg := config)
    (frame := p.frame) (evm := evm) (2 ^ 64 - 192)
    (ExecTransactionLocals.initial p).signatures).trans (by congr 2; exact decide_eq_false hn)))

theorem safeExecTransactionInvalidOperation (p : ExecTransactionInput) (evm : EVM.State)
    (ho : ¬p.tx.operation.toNat < 2) :
    ExecBlock config p.frame evm exectransactionTransition.body .reverted := by
  by_cases hn : p.signatures.size ≤ 2 ^ 64 - 192
  swap
  · exact safeExecTransactionLargeSignatures p evm hn
  exact .consNormal (.requireTrue ((evalLocalBytesLengthLe (cfg := config)
    (frame := p.frame) (evm := evm) (2 ^ 64 - 192)
    (ExecTransactionLocals.initial p).signatures).trans (by congr 2; exact decide_eq_true hn)))
    (.consRevert (.requireFalse ((evalValidOperation (cfg := config) (frame := p.frame) (evm := evm)
      (ExecTransactionLocals.initial p).tx.operation).trans
        (by congr 2; exact decide_eq_false ho))))

theorem safeEvalExecNonce (evm : EVM.State) (locals : Store) (hn : locals["nonce"]? = none) :
    evalExpr? config { contract := contract, locals := locals } evm (.storage nonceRef) =
      .ok (uint256Value (execNonce evm)) := by
  apply evalExpr_storage_scalar_value (er := { base := "nonce" }) (loc := uint256Loc ⟨5⟩)
  · exact hn
  · simp [evalStorageRef, evalStorageRefSteps, nonceRef, EvalResult.bind, bind, pure]
  · rfl
  · rfl
  · rfl
  · exact storageLocLoad_uint256 evm ⟨5⟩

theorem safeAssignExecNonce (evm : EVM.State) (locals : Store) (value : UInt256)
    (hn : locals["nonce"]? = none) :
    assignStorageRef? config { contract := contract, locals := locals } evm .storage nonceRef
      (uint256Value value) = .ok ({ contract := contract, locals := locals },
        Solm.EVM.storageStore evm evm.executionEnv.codeOwner ⟨5⟩ value) := by
  apply assignStorageRef_storage_scalar_value (er := { base := "nonce" }) (loc := uint256Loc ⟨5⟩)
  · exact hn
  · simp [evalStorageRef, evalStorageRefSteps, nonceRef, EvalResult.bind, bind, pure]
  · rfl
  · rfl
  · rfl
  · exact .inl ⟨_, rfl⟩
  · exact storageLocStore_uint256 evm ⟨5⟩ value

theorem execNonceLocal (p : ExecTransactionInput) (evm : EVM.State) :
    (execNonceFrame p evm).locals["nonceBefore"]? = some (uint256Value (execNonce evm)) := by
  simp [execNonceFrame, Std.HashMap.getElem_insert]

theorem safeExecTransactionNonceOverflow (p : ExecTransactionInput) (evm : EVM.State)
    (hn : p.signatures.size ≤ 2 ^ 64 - 192) (ho : p.tx.operation.toNat < 2)
    (hno : ¬(execNonce evm).toNat + 1 < UInt256.size) :
    ExecBlock config p.frame evm exectransactionTransition.body .reverted := by
  apply safeExecTransactionChecks p evm hn ho
  exact .consNormal (.letDecl (safeEvalExecNonce evm p.args
    (by simp [ExecTransactionInput.args, Std.HashMap.getElem_insert])))
      (.consRevert (.assignExprRevert (checkedAddSourceOverflow
        (evalLocalValue (execNonceLocal p evm)) (b := ⟨1⟩) (by simp [evalExpr?]; rfl)
        (by change UInt256.size ≤ _ + 1; omega))))

theorem safeExecTransactionNonceStatic (p : ExecTransactionInput) (evm : EVM.State)
    (hn : p.signatures.size ≤ 2 ^ 64 - 192) (ho : p.tx.operation.toNat < 2)
    (hno : (execNonce evm).toNat + 1 < UInt256.size) (hp : evm.executionEnv.perm = false) :
    ExecBlock config p.frame evm exectransactionTransition.body .staticViolation := by
  apply safeExecTransactionChecks p evm hn ho
  exact .consNormal (.letDecl (safeEvalExecNonce evm p.args
    (by simp [ExecTransactionInput.args, Std.HashMap.getElem_insert])))
      (.consStatic (.assignStatic
        (checkedAddSourceOk (evalLocalValue (execNonceLocal p evm)) (b := ⟨1⟩)
          (by simp [evalExpr?]; rfl) hno)
        (safeAssignExecNonce evm (execNonceFrame p evm).locals _
          (by simp [execNonceFrame, ExecTransactionInput.args, Std.HashMap.getElem_insert])) hp))

theorem safeExecTransactionNoncePrefix (p : ExecTransactionInput) (evm : EVM.State)
    {result : ExecResult} (hn : p.signatures.size ≤ 2 ^ 64 - 192)
    (ho : p.tx.operation.toNat < 2) (hno : (execNonce evm).toNat + 1 < UInt256.size)
    (ht : ExecBlock config (execNonceFrame p evm) (execNonceState evm)
      (exectransactionTransition.body.drop 4) result) :
    ExecBlock config p.frame evm exectransactionTransition.body result := by
  apply safeExecTransactionChecks p evm hn ho
  exact .consNormal (.letDecl (safeEvalExecNonce evm p.args
    (by simp [ExecTransactionInput.args, Std.HashMap.getElem_insert])))
      (.consNormal (.assign
        (checkedAddSourceOk (evalLocalValue (execNonceLocal p evm)) (b := ⟨1⟩)
          (by simp [evalExpr?]; rfl) hno)
        (safeAssignExecNonce evm (execNonceFrame p evm).locals _
          (by simp [execNonceFrame, ExecTransactionInput.args, Std.HashMap.getElem_insert]))) ht)

theorem safeExecTransactionHashLet (p : ExecTransactionInput) (evm : EVM.State) :
    ExecStmt config (execNonceFrame p evm) (execNonceState evm)
      (.letDecl "txHash" (some bytes32) (transactionHashExpr (.var "nonceBefore")))
      (.ok (execHashFrame p evm) (execNonceState evm)) := by
  apply ExecStmt.letDecl
  have he := evalTransactionHash (cfg := config) (evm := execNonceState evm)
    ((execNonceFrame_locals p evm).withNonce (execNonce evm))
    (evalLocalValue (execNonceLocal p evm))
  simpa only [execNonceState, storageStore_executionEnv, execTransactionHash] using he

end Benchmarks.Safe
