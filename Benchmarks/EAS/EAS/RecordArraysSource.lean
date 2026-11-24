import Benchmarks.EAS.EAS.LocalArrayStore
import Benchmarks.EAS.EAS.AttestationRequest

variable {fork : Ethereum.Fork}
open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.EAS.EAS

def attestationsResultValue (uids : List UInt256) (used : UInt256) : Value := .struct "AttestationsResult" [
  ("usedValue",.int (Int.ofNat used.toNat)),("uids",.array (uids.map wordBytes32Value))]
def recordArraysBody : Body := [
  .assign .localVar {base := "attestations",steps := [.aindex (.var "i")]} (.var "attestation"),
  .assign .localVar {base := "values",steps := [.aindex (.var "i")]} (.field (.var "request") "value"),
  .assign .localVar {base := "res",steps := [.field "uids",.aindex (.var "i")]} (.var "uid")]
def recordArraysLocals (L : Store) (ats : List AttestationRecord) (values uids : List UInt256)
    (used : UInt256) (a : AttestationRecord) (value uid : UInt256) (i : Nat) : Store :=
  ((L.insert "attestations" (.array ((ats.set i a).map AttestationRecord.value))).insert
    "values" (.array ((values.set i value).map (fun w => Value.int (Int.ofNat w.toNat))))).insert
    "res" (attestationsResultValue (uids.set i uid) used)

theorem recordArraysSource {L imms : Store} {evm : EVM.State} {ats : List AttestationRecord}
    {values uids : List UInt256} {used uid : UInt256} {a : AttestationRecord} {r : AttestationRequestRecord} {i : Nat}
    (ha : L.get? "attestation" = some a.value) (hr : L.get? "request" = some r.struct)
    (hu : L.get? "uid" = some (wordBytes32Value uid)) (hi : L.get? "i" = some (.int (Int.ofNat i)))
    (hats : L.get? "attestations" = some (.array (ats.map AttestationRecord.value)))
    (hvalues : L.get? "values" = some (.array (values.map (fun w => Value.int (Int.ofNat w.toNat)))))
    (huids : L.get? "res" = some (attestationsResultValue uids used))
    (hia : i < ats.length) (hiv : i < values.length) (hiu : i < uids.length) :
    ExecBlock fork config {contract := contract,locals := L,immutables := imms} evm recordArraysBody
      (.ok {contract := contract,locals := recordArraysLocals L ats values uids used a r.value uid i,immutables := imms} evm) := by
  let L1 := L.insert "attestations" (.array ((ats.set i a).map AttestationRecord.value))
  let L2 := L1.insert "values" (.array ((values.set i r.value).map (fun w => Value.int (Int.ofNat w.toNat))))
  have hi1 : L1.get? "i" = some (.int (Int.ofNat i)) := (store_get_ne _ _ (by decide)).trans hi
  have hi2 : L2.get? "i" = some (.int (Int.ofNat i)) := (store_get_ne _ _ (by decide)).trans hi1
  have hs1 : assignStorageRef? config {contract := contract,locals := L,immutables := imms} evm .localVar
      {base := "attestations",steps := [.aindex (.var "i")]} a.value =
      .ok ({contract := contract,locals := L1,immutables := imms},evm) := by
    simpa only [L1,List.map_set] using assignLocalArrayExpr hats
      (show evalExpr? config {contract := contract,locals := L,immutables := imms} evm (.var "i") = .ok (.int (Int.ofNat i)) by
        simp only [evalExpr?,hi,EvalResult.ofOption]) (by simpa only [List.length_map] using hia)
  refine ExecBlock.consNormal (ExecStmt.assign (fork := fork) (hperm := by first | exact Or.inl rfl | assumption | exact Or.inr ‹_›) (by simp only [evalExpr?,ha,EvalResult.ofOption]) hs1) ?_
  have hv1 : L1.get? "values" = some (.array (values.map (fun w => Value.int (Int.ofNat w.toNat)))) :=
    (store_get_ne _ _ (by decide)).trans hvalues
  have hs2 : assignStorageRef? config {contract := contract,locals := L1,immutables := imms} evm .localVar
      {base := "values",steps := [.aindex (.var "i")]} (.int (Int.ofNat r.value.toNat)) =
      .ok ({contract := contract,locals := L2,immutables := imms},evm) := by
    simpa only [L2,List.map_set] using assignLocalArrayExpr hv1
      (show evalExpr? config {contract := contract,locals := L1,immutables := imms} evm (.var "i") = .ok (.int (Int.ofNat i)) by
        simp only [evalExpr?,hi1,EvalResult.ofOption]) (by simpa only [List.length_map] using hiv)
  have her : evalExpr? config {contract := contract,locals := L1,immutables := imms} evm (.field (.var "request") "value") =
      .ok (.int (Int.ofNat r.value.toNat)) := by
    simp only [evalExpr?,L1,store_get_ne _ _ (by decide : ("attestations" == "request") = false),hr,
      EvalResult.ofOption,EvalResult.bind,bind]
    rfl
  refine ExecBlock.consNormal (ExecStmt.assign (fork := fork) (hperm := by first | exact Or.inl rfl | assumption | exact Or.inr ‹_›) her hs2) ?_
  have hres2 : L2.get? "res" = some (attestationsResultValue uids used) :=
    (store_get_ne _ _ (by decide)).trans ((store_get_ne _ _ (by decide)).trans huids)
  have hpath : updateLocalPath? config {contract := contract,locals := L2,immutables := imms} evm
      (attestationsResultValue uids used) [.field "uids",.aindex (.var "i")] (wordBytes32Value uid) =
      .ok (attestationsResultValue (uids.set i uid) used) := by
    rw [updateLocalPath?]
    simp only [show lookupField? (attestationsResultValue uids used) "uids" = some (.array (uids.map wordBytes32Value)) from rfl,
      EvalResult.ofOption,EvalResult.bind,bind]
    rw [updateLocalArrayIndex (i := i) (by simp only [evalExpr?,hi2,EvalResult.ofOption]) (by simpa only [List.length_map] using hiu)]
    rw [← List.map_set]
    rfl
  have hu2 : L2.get? "uid" = some (wordBytes32Value uid) :=
    (store_get_ne _ _ (by decide)).trans ((store_get_ne _ _ (by decide)).trans hu)
  refine ExecBlock.consNormal (ExecStmt.assign (fork := fork) (hperm := by first | exact Or.inl rfl | assumption | exact Or.inr ‹_›) (value := wordBytes32Value uid) (by simp only [evalExpr?,hu2,EvalResult.ofOption]) ?_) ExecBlock.nil
  simp only [assignStorageRef?,hres2,hpath,EvalResult.bind,bind,pure]
  rfl

end Benchmarks.EAS.EAS
