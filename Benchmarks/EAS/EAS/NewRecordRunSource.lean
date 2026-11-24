import Benchmarks.EAS.EAS.NewRecordSource
import Benchmarks.EAS.EAS.ReadTimeBlock

variable {fork : Ethereum.Fork}
open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.EAS.EAS

def newRecordBody : Body := readTimeBlock "__c2$allocation" "__c2" ++ allocateBlock (.intLit 320) ++ newAttestationBody
def newRecordLocals (L : Store) (r : AttestationRequestRecord) (schema time : UInt256)
    (attester : AccountAddress) (heap : Nat) : Store :=
  newAttestationLocals (allocateBlockLocals (readTimeLocals L "__c2$allocation" "__c2" time heap)
    (allocateNext heap 320)) (newAttestation r schema time attester)

theorem newRecordSource {L imms : Store} {evm : EVM.State} {r : AttestationRequestRecord}
    {schema : UInt256} {attester : AccountAddress} {heap : Nat}
    (hr : L.get? "request" = some r.struct) (hs : L.get? "schema" = some (wordBytes32Value schema))
    (ha : L.get? "attester" = some (.address attester)) (hh : L.get? "$EAS.freeMemory" = some (.int (Int.ofNat heap))) :
    if allocateNext heap 320 ≤ 2^64-1 ∧ heap ≤ allocateNext heap 320 then
      ExecBlock fork config {contract := contract,locals := L,immutables := imms} evm newRecordBody
        (.ok {contract := contract,locals := newRecordLocals L r schema (easTimeWord evm.executionEnv) attester heap,immutables := imms} evm)
    else ExecBlock fork config {contract := contract,locals := L,immutables := imms} evm newRecordBody .reverted := by
  have ht := readTimeBlock_source (fork := fork) (cfg := config) (imms := imms) (evm := evm)
    "__c2$allocation" "__c2" hh (by decide) (by decide) (by decide)
  have hh1 : (readTimeLocals L "__c2$allocation" "__c2" (easTimeWord evm.executionEnv) heap).get? "$EAS.freeMemory" =
      some (.int (Int.ofNat heap)) := heapResultLocals_heap _ _ _ _ _ _
  have hn : ∀ frame, evalExpr? config frame evm (.intLit 320) = .ok (.int (Int.ofNat 320)) :=
    fun _ => by simp only [evalExpr?,pure]; rfl
  by_cases hg : allocateNext heap 320 ≤ 2^64-1 ∧ heap ≤ allocateNext heap 320
  · rw [if_pos hg,newRecordBody,List.append_assoc]
    apply execBlock_append ht
    apply execBlock_append (allocateBlock_ok (hn _) hh1 hg)
    apply newAttestationSource (r := r) (schema := schema) (time := easTimeWord evm.executionEnv) (attester := attester)
    · simpa (disch := decide) only [readTimeLocals,allocateBlockLocals_get,heapResultLocals_get] using hr
    · simpa (disch := decide) only [readTimeLocals,allocateBlockLocals_get,heapResultLocals_get] using hs
    · rw [allocateBlockLocals_get (by decide) (by decide) (by decide)]
      exact heapResultLocals_result _ _ _ _ _ _ (by decide)
    · simpa (disch := decide) only [readTimeLocals,allocateBlockLocals_get,heapResultLocals_get] using ha
  · rw [if_neg hg,newRecordBody,List.append_assoc]
    apply execBlock_append ht
    exact execBlock_append_term (allocateBlock_revert (hn _) hh1 hg) (by intros;exact nofun)

end Benchmarks.EAS.EAS
