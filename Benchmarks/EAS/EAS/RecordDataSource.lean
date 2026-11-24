import Benchmarks.EAS.EAS.StoredBytesWrite
import Benchmarks.EAS.EAS.AttestationWriteStatements

variable {fork : Ethereum.Fork}
open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.EAS.EAS

theorem recordDataAssign {L imms : Store} {evm : EVM.State} {word : UInt256} {bytes : ByteArray}
    (hd : L.get? "_db" = none) (hu : L.get? "uid" = some (wordBytes32Value word)) :
    assignStorageRef? config {contract := contract,locals := L,immutables := imms} evm
      .storage (attestationFieldRef "data") (.bytes bytes) =
      if storedBytesValid (attestationHeader evm word) then
        .ok ({contract := contract,locals := L,immutables := imms},
          bytesWriteState evm (dbSlot word+⟨6⟩) bytes (storedBytesLengthWord (attestationHeader evm word)).toNat)
      else .revert := by
  have hr := resolveStorageRef?_ok (cfg := config) (stele := {contract := contract,locals := L,immutables := imms})
    (evm := evm) hd (attestationField_evalRef hu "data")
    (show storageTypeAt? contract.storage (attestationFieldER word "data") = some .bytes from rfl)
  simp only [assignStorageRef?,hr,EvalResult.bind,bind,
    storedBytesWrite bytes easStorageBackend (attestation_data_layout word)]
  by_cases hv : storedBytesValid (attestationHeader evm word) <;>
    simp only [attestationHeader] at hv ⊢ <;> simp only [hv,if_true,if_false,EvalResult.bind,pure]

theorem recordDataSource {L imms : Store} {evm : EVM.State} {word : UInt256} {a : AttestationRecord}
    (hd : L.get? "_db" = none) (hu : L.get? "uid" = some (wordBytes32Value word))
    (ha : L.get? "attestation" = some a.value)
    (hperm : evm.executionEnv.perm = true) :
    if storedBytesValid (attestationHeader evm word) then
      ExecStmt fork config {contract := contract,locals := L,immutables := imms} evm (attestationWriteStmt "data")
        (.ok {contract := contract,locals := L,immutables := imms}
          (bytesWriteState evm (dbSlot word+⟨6⟩) a.data (storedBytesLengthWord (attestationHeader evm word)).toNat))
    else ExecStmt fork config {contract := contract,locals := L,immutables := imms} evm
      (attestationWriteStmt "data") .reverted := by
  have he := attestationRecord_field (cfg := config) (evm := evm)
    (frame := {contract := contract,locals := L,immutables := imms}) ha "data" (.bytes a.data) rfl
  have hw := recordDataAssign (imms := imms) (evm := evm) (bytes := a.data) hd hu
  split at hw
  · rename_i hv
    rw [if_pos hv]
    exact ExecStmt.assign (hperm := Or.inr hperm) he hw
  · rename_i hv
    rw [if_neg hv]
    exact ExecStmt.assignStoreRevert he hw

end Benchmarks.EAS.EAS
