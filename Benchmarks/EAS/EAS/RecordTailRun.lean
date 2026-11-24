import Benchmarks.EAS.EAS.RecordTailSource
import Benchmarks.EAS.EAS.RecordTailControl
import Benchmarks.EAS.EAS.RecordTailViews

variable {fork : Ethereum.Fork}
open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables Benchmarks.EAS.EAS.Immutables
namespace Benchmarks.EAS.EAS

structure RecordTailSourceView (L : Store) (ats : List AttestationRecord) (values uids : List UInt256)
    (used uid schema : UInt256) (a : AttestationRecord) (r : AttestationRequestRecord) (attester : AccountAddress) (i : Nat) : Prop where
  attestation : L.get? "attestation" = some a.value
  request : L.get? "request" = some r.struct
  uid : L.get? "uid" = some (wordBytes32Value uid)
  index : L.get? "i" = some (.int (Int.ofNat i))
  attestations : L.get? "attestations" = some (.array (ats.map AttestationRecord.value))
  values : L.get? "values" = some (.array (values.map (fun w => Value.int (Int.ofNat w.toNat))))
  result : L.get? "res" = some (attestationsResultValue uids used)
  attester : L.get? "attester" = some (.address attester)
  schema : L.get? "schema" = some (wordBytes32Value schema)

structure RecordTailMemoryView (mem : ByteArray) (site : UIDSite) (t3 t4 uidPtr : UInt256)
    (ptrs values uids : List UInt256) (value : UInt256) (heap : Nat) (valueMemory : ByteArray := mem) : Prop where
  records : WordArrayMemoryView mem (recordArrayPtr site t3 t4) ptrs heap
  valueArray : WordArrayMemoryView valueMemory (recordValuesPtr site t4) values heap
  uidArray : WordArrayMemoryView mem uidPtr uids heap
  lengthValues : values.length = ptrs.length
  lengthUIDs : uids.length = ptrs.length
  uidRecords : uidPtr.toNat+32+32*uids.length ≤ (recordArrayPtr site t3 t4).toNat
  recordValues : (recordArrayPtr site t3 t4).toNat+32+32*ptrs.length ≤ (recordValuesPtr site t4).toNat
  requestLow : 96 ≤ (refUIDPtr site t3).toNat
  requestEnd : (refUIDPtr site t3).toNat+192 ≤ uidPtr.toNat
  requestCovered : (refUIDPtr site t3).toNat+192 ≤ mem.size
  requestValue : memLoad (refUIDPtr site t3+UInt256.ofNat 160) mem = value
  uidPointer : recordUIDsPtr site mem = uidPtr
  resultLow : 96 ≤ (recordResultPtr site mem).toNat
  resultEnd : (recordResultPtr site mem).toNat+64 ≤ uidPtr.toNat
  resultCovered : (recordResultPtr site mem).toNat+64 ≤ mem.size
  heapRead : memLoad (UInt256.ofNat 64) mem = UInt256.ofNat heap

theorem recordTailRun {L : Store} {evm : EVM.State} {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C i heap : Nat}
    {dummy word src uidPtr t1 t3 t4 used schema : UInt256} {a : AttestationRecord} {r : AttestationRequestRecord}
    {attester : AccountAddress} {ats : List AttestationRecord} {ptrs values uids : List UInt256} {R : List UInt256}
    (v : EASImmutables) (site : UIDSite) (hstack : R.length+31 ≤ 1024) (hp : ee.perm = true)
    (hf : RecordTailSourceView L ats values uids used word schema a r attester i)
    (hm : RecordTailMemoryView mem site t3 t4 uidPtr ptrs values uids r.value heap)
    (hlen : ats.length = ptrs.length) (hi : i < ptrs.length) (hb : heap < UInt256.size)
    (rd : RD fork (deployedRuntime v) ee g s0 (refUIDReadyPC site)
      (refUIDReadyStack site dummy word src t1 (UInt256.ofNat i) t3 t4 R) mem aw rdata σ k C)
    (hperm : evm.executionEnv.perm = true) :
    ExecBlock fork config {contract := contract,locals := L,immutables := immStore v} evm recordTailBody
      (.ok {contract := contract,locals := recordTailLocals L ats values uids used a r.value word i,immutables := immStore v} evm) ∧
    WordArrayMemoryView (recordTailMemory mem site src t3 t4 r.value uidPtr word i) uidPtr (uids.set i word) heap ∧
    WordArrayMemoryView (recordTailMemory mem site src t3 t4 r.value uidPtr word i)
      (recordArrayPtr site t3 t4) (ptrs.set i src) heap ∧
    WordArrayMemoryView (recordTailMemory mem site src t3 t4 r.value uidPtr word i)
      (recordValuesPtr site t4) (values.set i r.value) heap ∧
    memLoad (UInt256.ofNat 64) (recordTailMemory mem site src t3 t4 r.value uidPtr word i) = UInt256.ofNat heap ∧
    ∃ aw' k' C', RD fork (deployedRuntime v) ee g s0 (recordNextPC site)
      (recordNextStack site t1 (UInt256.ofNat (i+1)) t3 t4 R)
      (recordTailMemory mem site src t3 t4 r.value uidPtr word i) aw' rdata σ k' C' := by
  have hiv : i < values.length := by rw [hm.lengthValues]; exact hi
  have hiu : i < uids.length := by rw [hm.lengthUIDs]; exact hi
  have hs := recordTailSource (fork := fork) (hperm := hperm) (imms := immStore v) (evm := evm) hf.attestation hf.request hf.uid hf.index hf.attestations hf.values hf.result
    hf.attester hf.schema (by omega) hiv hiu (by have := hm.records.span; omega)
  obtain ⟨hu,ha,hv,hh⟩ := recordTailMemory_views site hm.records hm.valueArray hm.uidArray hm.uidRecords hm.recordValues
    hi hiv hiu hb hm.heapRead
  exact ⟨hs,hu,ha,hv,hh,easRecordTail_of_views v site hstack hp hm.records hm.valueArray hm.uidArray
    hm.lengthValues hm.lengthUIDs hm.uidRecords hm.recordValues hi hb hm.requestLow hm.requestEnd
    hm.requestCovered hm.requestValue hm.uidPointer hm.resultLow hm.resultEnd hm.resultCovered rd⟩

end Benchmarks.EAS.EAS
