import Benchmarks.EAS.EAS.WordExpr
import Benchmarks.EAS.EAS.Storage

variable {fork : Ethereum.Fork}
open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.EAS.EAS

def nonceExprRef (key : Expr) : StorageRef := {base := "_nonces",steps := [.mindex key]}
def nonceStore (evm : EVM.State) (a : AccountAddress) : EVM.State :=
  EVM.storageStore evm evm.executionEnv.codeOwner (nonceSlot a) (nonceWord evm a + UInt256.ofNat 1)

theorem nonceExpr_evalRef {evm : EVM.State} {L imms : Store} {a : AccountAddress} {key : Expr}
    (he : evalExpr? config {contract := contract,locals := L,immutables := imms} evm key = .ok (.address a)) :
    evalStorageRef config {contract := contract,locals := L,immutables := imms} evm (nonceExprRef key) =
      .ok {base := "_nonces",steps := [.mindex (.address a)]} := by
  simp only [evalStorageRef,nonceExprRef,evalStorageRefSteps,evalStorageRefStep,he,
    valueToKey?,EvalResult.ofOption,pure,bind,EvalResult.bind]

theorem nonceExpr_read {evm : EVM.State} {L imms : Store} {a : AccountAddress} {key : Expr}
    (hn : L.get? "_nonces" = none)
    (he : evalExpr? config {contract := contract,locals := L,immutables := imms} evm key = .ok (.address a)) :
    evalExpr? config {contract := contract,locals := L,immutables := imms} evm (.storage (nonceExprRef key)) =
      .ok (.int (Int.ofNat (nonceWord evm a).toNat)) := by
  exact evalExpr_storage_scalar_value (t := .int (.uint ⟨256,by decide⟩)) (loc := uint256Loc (nonceSlot a))
    hn (nonceExpr_evalRef he) rfl rfl rfl (storageLocLoad_uint256 evm (nonceSlot a))

theorem nonceExpr_write {evm : EVM.State} {L imms : Store} {a : AccountAddress} {key : Expr}
    (hn : L.get? "_nonces" = none)
    (he : evalExpr? config {contract := contract,locals := L,immutables := imms} evm key = .ok (.address a)) :
    assignStorageRef? config {contract := contract,locals := L,immutables := imms} evm .storage
      (nonceExprRef key) (.int (Int.ofNat (nonceWord evm a + UInt256.ofNat 1).toNat)) =
      .ok ({contract := contract,locals := L,immutables := imms},nonceStore evm a) := by
  exact assignStorageRef_storage_scalar_value (loc := uint256Loc (nonceSlot a))
    (ty := .elem (.int (.uint ⟨256,by decide⟩))) hn (nonceExpr_evalRef he) rfl easStorageBackend rfl
    (Or.inl ⟨_,rfl⟩) (storageLocStore_uint256 evm (nonceSlot a) (nonceWord evm a + UInt256.ofNat 1))

def nonceReadBlock (key : Expr) : Body := [
  .letDecl "nonce" (some (.elem (.int (.uint ⟨256,by decide⟩)))) (.intLit 0),
  .assign .localVar {base := "nonce"} (.storage (nonceExprRef key))]
def nonceWrite (key : Expr) : Stmt := .assign .storage (nonceExprRef key)
  (.cast (.binary .add (.var "nonce") (.intLit 1)) (.elem (.int (.uint ⟨256,by decide⟩))))
def nonceLocals (L : Store) (word : UInt256) : Store :=
  (L.insert "nonce" (.int 0)).insert "nonce" (.int (Int.ofNat word.toNat))

theorem nonceReadSource {evm : EVM.State} {L imms : Store} {a : AccountAddress} {key : Expr}
    (hn : L.get? "_nonces" = none)
    (he : evalExpr? config {contract := contract,locals := L.insert "nonce" (.int 0),immutables := imms} evm key = .ok (.address a)) :
    ExecBlock fork config {contract := contract,locals := L,immutables := imms} evm (nonceReadBlock key)
      (.ok {contract := contract,locals := nonceLocals L (nonceWord evm a),immutables := imms} evm) := by
  refine ExecBlock.consNormal (ExecStmt.letDecl (value := .int 0) (by simp only [evalExpr?,pure])) ?_
  refine ExecBlock.consNormal (ExecStmt.assign (fork := fork) (hperm := Or.inl rfl) (nonceExpr_read (by simpa (disch := decide) only [store_get_ne] using hn) he) ?_) ExecBlock.nil
  simp only [assignStorageRef?,updateLocalPath?,store_get_self,EvalResult.bind,bind,pure,nonceLocals]

theorem nonceWrite_eval {evm : EVM.State} {L imms : Store} {word : UInt256}
    (hn : L.get? "nonce" = some (.int (Int.ofNat word.toNat))) :
    evalExpr? config {contract := contract,locals := L,immutables := imms} evm
      (.cast (.binary .add (.var "nonce") (.intLit 1)) (.elem (.int (.uint ⟨256,by decide⟩)))) =
      .ok (.int (Int.ofNat (word + UInt256.ofNat 1).toNat)) := by
  simpa only [uadd_toNat,show (UInt256.ofNat 1).toNat = 1 from rfl] using
    evalCastUint256Add (by simp only [evalExpr?,hn,EvalResult.ofOption])
      (show evalExpr? config {contract := contract,locals := L,immutables := imms} evm (.intLit 1) = .ok (.int (Int.ofNat 1)) by simp only [evalExpr?,pure]; rfl)

theorem nonceWriteSource {evm : EVM.State} {L imms : Store} {a : AccountAddress} {key : Expr}
    (hn : L.get? "_nonces" = none) (hw : L.get? "nonce" = some (.int (Int.ofNat (nonceWord evm a).toNat)))
    (he : evalExpr? config {contract := contract,locals := L,immutables := imms} evm key = .ok (.address a))
    (hperm : evm.executionEnv.perm = true) :
    ExecStmt fork config {contract := contract,locals := L,immutables := imms} evm (nonceWrite key)
      (.ok {contract := contract,locals := L,immutables := imms} (nonceStore evm a)) :=
  ExecStmt.assign (hperm := Or.inr hperm) (nonceWrite_eval hw) (nonceExpr_write hn he)

theorem nonceWriteStatic {evm : EVM.State} {L imms : Store} {a : AccountAddress} {key : Expr}
    (hn : L.get? "_nonces" = none) (hw : L.get? "nonce" = some (.int (Int.ofNat (nonceWord evm a).toNat)))
    (he : evalExpr? config {contract := contract,locals := L,immutables := imms} evm key = .ok (.address a))
    (hp : evm.executionEnv.perm = false) :
    ExecStmt fork config {contract := contract,locals := L,immutables := imms} evm (nonceWrite key) .staticViolation :=
  ExecStmt.assignStatic (nonceWrite_eval hw) (nonceExpr_write hn he) hp

end Benchmarks.EAS.EAS
