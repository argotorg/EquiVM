import Benchmarks.EAS.EAS.RecordEventSource

variable {fork : Ethereum.Fork}
open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.EAS.EAS

def recordTailBody : Body := recordArraysBody ++ recordEventBody
def recordTailLocals (L : Store) (ats : List AttestationRecord) (values uids : List UInt256)
    (used : UInt256) (a : AttestationRecord) (value uid : UInt256) (i : Nat) : Store :=
  (recordArraysLocals L ats values uids used a value uid i).insert "i" (.int (Int.ofNat (i+1)))

theorem recordTailSource {L imms : Store} {evm : EVM.State} {ats : List AttestationRecord}
    {values uids : List UInt256} {used uid schema : UInt256} {a : AttestationRecord}
    {r : AttestationRequestRecord} {attester : AccountAddress} {i : Nat}
    (ha : L.get? "attestation" = some a.value) (hr : L.get? "request" = some r.struct)
    (hu : L.get? "uid" = some (wordBytes32Value uid)) (hi : L.get? "i" = some (.int (Int.ofNat i)))
    (hats : L.get? "attestations" = some (.array (ats.map AttestationRecord.value)))
    (hvalues : L.get? "values" = some (.array (values.map (fun w => Value.int (Int.ofNat w.toNat)))))
    (huids : L.get? "res" = some (attestationsResultValue uids used))
    (hattester : L.get? "attester" = some (.address attester))
    (hschema : L.get? "schema" = some (wordBytes32Value schema))
    (hia : i < ats.length) (hiv : i < values.length) (hiu : i < uids.length) (hb : i+1 < UInt256.size)
    (hperm : evm.executionEnv.perm = true) :
    ExecBlock fork config {contract := contract,locals := L,immutables := imms} evm recordTailBody
      (.ok {contract := contract,locals := recordTailLocals L ats values uids used a r.value uid i,immutables := imms} evm) := by
  apply execBlock_append (recordArraysSource ha hr hu hi hats hvalues huids hia hiv hiu)
  apply recordEventSource (hperm := by assumption) (r := r) (attester := attester) (uid := uid) (schema := schema) (i := i)
  · simpa only [recordArraysLocals,store_get_ne _ _ (by decide : ("res" == "request") = false),
      store_get_ne _ _ (by decide : ("values" == "request") = false),
      store_get_ne _ _ (by decide : ("attestations" == "request") = false)] using hr
  · simpa only [recordArraysLocals,store_get_ne _ _ (by decide : ("res" == "attester") = false),
      store_get_ne _ _ (by decide : ("values" == "attester") = false),
      store_get_ne _ _ (by decide : ("attestations" == "attester") = false)] using hattester
  · simpa only [recordArraysLocals,store_get_ne _ _ (by decide : ("res" == "uid") = false),
      store_get_ne _ _ (by decide : ("values" == "uid") = false),
      store_get_ne _ _ (by decide : ("attestations" == "uid") = false)] using hu
  · simpa only [recordArraysLocals,store_get_ne _ _ (by decide : ("res" == "schema") = false),
      store_get_ne _ _ (by decide : ("values" == "schema") = false),
      store_get_ne _ _ (by decide : ("attestations" == "schema") = false)] using hschema
  · simpa only [recordArraysLocals,store_get_ne _ _ (by decide : ("res" == "i") = false),
      store_get_ne _ _ (by decide : ("values" == "i") = false),
      store_get_ne _ _ (by decide : ("attestations" == "i") = false)] using hi
  · exact hb

end Benchmarks.EAS.EAS
