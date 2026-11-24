import Benchmarks.EAS.EAS.RevokeSource
import Benchmarks.EAS.EAS.LocalArrayStore

variable {fork : Ethereum.Fork}
open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.EAS.EAS

def revokeUpdateLocals (L : Store) (ats : List AttestationRecord) (values : List UInt256)
    (a : AttestationRecord) (value : UInt256) (i : Nat) : Store :=
  ((L.insert "attestations" (.array ((ats.set i a).map AttestationRecord.value))).insert
    "values" (.array ((values.set i value).map (fun w => Value.int (Int.ofNat w.toNat))))).insert
    "i" (.int (Int.ofNat (i+1)))

theorem revokeUpdateSource {L imms : Store} {evm : EVM.State} {ats : List AttestationRecord}
    {values : List UInt256} {a : AttestationRecord} {r : RevocationRequestRecord} {revoker : AccountAddress} {i : Nat}
    (hc : L.get? "copied" = some a.value)
    (ha : L.get? "attestation" = some (.storageRef (attestationER r.uid) attestationType))
    (hr : L.get? "request" = some r.struct) (hi : L.get? "i" = some (.int (Int.ofNat i)))
    (hats : L.get? "attestations" = some (.array (ats.map AttestationRecord.value)))
    (hvalues : L.get? "values" = some (.array (values.map (fun w => Value.int (Int.ofNat w.toNat)))))
    (hrevoker : L.get? "revoker" = some (.address revoker))
    (hia : i < ats.length) (hiv : i < values.length) (hb : i+1 < UInt256.size)
    (hperm : evm.executionEnv.perm = true) :
    ExecBlock fork config {contract := contract,locals := L,immutables := imms} evm revokeUpdateBody
      (.ok {contract := contract,locals := revokeUpdateLocals L ats values a r.value i,immutables := imms} evm) := by
  let L1 := L.insert "attestations" (.array ((ats.set i a).map AttestationRecord.value))
  let L2 := L1.insert "values" (.array ((values.set i r.value).map (fun w => Value.int (Int.ofNat w.toNat))))
  have hi1 : L1.get? "i" = some (.int (Int.ofNat i)) := (store_get_ne _ _ (by decide)).trans hi
  have hs1 : assignStorageRef? config {contract := contract,locals := L,immutables := imms} evm .localVar
      {base := "attestations",steps := [.aindex (.var "i")]} a.value =
      .ok ({contract := contract,locals := L1,immutables := imms},evm) := by
    simpa only [L1,List.map_set] using assignLocalArrayIndex hats hi (by simpa only [List.length_map] using hia)
  have hv1 : L1.get? "values" = some (.array (values.map (fun w => Value.int (Int.ofNat w.toNat)))) :=
    (store_get_ne _ _ (by decide)).trans hvalues
  have hs2 : assignStorageRef? config {contract := contract,locals := L1,immutables := imms} evm .localVar
      {base := "values",steps := [.aindex (.var "i")]} (.int (Int.ofNat r.value.toNat)) =
      .ok ({contract := contract,locals := L2,immutables := imms},evm) := by
    simpa only [L2,List.map_set] using assignLocalArrayIndex hv1 hi1 (by simpa only [List.length_map] using hiv)
  have hr1 : L1.get? "request" = some r.struct := (store_get_ne _ _ (by decide)).trans hr
  have he : evalExpr? config {contract := contract,locals := L1,immutables := imms} evm
      (.field (.var "request") "value") = .ok (.int (Int.ofNat r.value.toNat)) :=
    revokeRequestField_eval (cfg := config) (frame := {contract := contract,locals := L1,immutables := imms}) (evm := evm) (r := r) hr1 "value" _ rfl
  refine ExecBlock.consNormal (ExecStmt.assign (fork := fork) (hperm := by first | exact Or.inl rfl | assumption | exact Or.inr ‹_›) (evalLocalValue hc) hs1)
    (ExecBlock.consNormal (ExecStmt.assign (fork := fork) (hperm := by first | exact Or.inl rfl | assumption | exact Or.inr ‹_›) he hs2) ?_)
  have ha2 : L2.get? "attestation" = some (.storageRef (attestationER r.uid) attestationType) :=
    (store_get_ne _ _ (by decide)).trans ((store_get_ne _ _ (by decide)).trans ha)
  have hr2 : L2.get? "request" = some r.struct :=
    (store_get_ne _ _ (by decide)).trans hr1
  have hv2 : L2.get? "revoker" = some (.address revoker) :=
    (store_get_ne _ _ (by decide)).trans ((store_get_ne _ _ (by decide)).trans hrevoker)
  have hi2 : L2.get? "i" = some (.int (Int.ofNat i)) := (store_get_ne _ _ (by decide)).trans hi1
  have hrecipient : evalExpr? config {contract := contract,locals := L2,immutables := imms} evm
      (.storage (attestationAliasRef "recipient")) = .ok (.address (storedAttestationRecord evm r.uid).recipient) :=
    attestationAlias_scalar ha2 (f := attestationAddressWrite "recipient" (dbSlot r.uid+⟨4⟩) (storedAttestationRecord evm r.uid).recipient)
      (by simp only [attestationScalarWrites,List.mem_cons]; tauto)
  have hschema : evalExpr? config {contract := contract,locals := L2,immutables := imms} evm
      (.storage (attestationAliasRef "schema")) = .ok (wordBytes32Value (storedAttestationRecord evm r.uid).schema) :=
    attestationAlias_scalar ha2 (f := attestationWordWrite "schema" (dbSlot r.uid+⟨1⟩) (storedAttestationRecord evm r.uid).schema)
      (by simp only [attestationScalarWrites,List.mem_cons]; tauto)
  have huid : evalExpr? config {contract := contract,locals := L2,immutables := imms} evm
      (.field (.var "request") "uid") = .ok (wordBytes32Value r.uid) := revokeRequestField_eval (cfg := config) (frame := {contract := contract,locals := L2,immutables := imms}) (evm := evm) (r := r) hr2 "uid" _ rfl
  refine ExecBlock.consNormal (ExecStmt.emit (fork := fork) (hperm := hperm) (vals := [.address (storedAttestationRecord evm r.uid).recipient,
      .address revoker,wordBytes32Value r.uid,wordBytes32Value (storedAttestationRecord evm r.uid).schema]) ?_)
      (ExecBlock.consNormal (execLocalCastIncrement hi2 hb) ExecBlock.nil)
  simp only [evalExprs?,hrecipient,hschema,huid,evalExpr?,hv2,EvalResult.ofOption,EvalResult.bind,bind,pure]

end Benchmarks.EAS.EAS
