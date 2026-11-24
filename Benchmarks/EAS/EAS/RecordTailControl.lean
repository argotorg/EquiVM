import Benchmarks.EAS.EAS.RecordTailEVM
import Benchmarks.EAS.EAS.ResultPointer
import Benchmarks.EAS.EAS.ArrayDisjoint

variable {fork : Ethereum.Fork}
open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables Benchmarks.EAS.EAS.Immutables
namespace Benchmarks.EAS.EAS

theorem easRecordTail_of_views {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C i heap : Nat}
    {dummy word src value uidPtr t1 t3 t4 : UInt256} {ptrs values uids : List UInt256} {R : List UInt256}
    (v : EASImmutables) (site : UIDSite) (hstack : R.length+31 ≤ 1024) (hp : ee.perm = true)
    (ha : WordArrayMemoryView mem (recordArrayPtr site t3 t4) ptrs heap)
    (hv : WordArrayMemoryView mem (recordValuesPtr site t4) values heap)
    (hu : WordArrayMemoryView mem uidPtr uids heap)
    (hlenv : values.length = ptrs.length) (hlenu : uids.length = ptrs.length)
    (hua : uidPtr.toNat+32+32*uids.length ≤ (recordArrayPtr site t3 t4).toNat)
    (hav : (recordArrayPtr site t3 t4).toNat+32+32*ptrs.length ≤ (recordValuesPtr site t4).toNat)
    (hi : i < ptrs.length) (hb : heap < UInt256.size)
    (hrlo : 96 ≤ (refUIDPtr site t3).toNat)
    (hrhi : (refUIDPtr site t3).toNat+192 ≤ uidPtr.toNat)
    (hrin : (refUIDPtr site t3).toNat+192 ≤ mem.size)
    (hvalue : memLoad (refUIDPtr site t3+UInt256.ofNat 160) mem = value)
    (hptr : recordUIDsPtr site mem = uidPtr)
    (hmlo : 96 ≤ (recordResultPtr site mem).toNat)
    (hmhi : (recordResultPtr site mem).toNat+64 ≤ uidPtr.toNat)
    (hmin : (recordResultPtr site mem).toNat+64 ≤ mem.size)
    (rd : RD fork (deployedRuntime v) ee g s0 (refUIDReadyPC site)
      (refUIDReadyStack site dummy word src t1 (UInt256.ofNat i) t3 t4 R) mem aw rdata σ k C) :
    ∃ aw' k' C', RD fork (deployedRuntime v) ee g s0 (recordNextPC site)
      (recordNextStack site t1 (UInt256.ofNat (i+1)) t3 t4 R)
      (recordTailMemory mem site src t3 t4 value uidPtr word i) aw' rdata σ k' C' := by
  have has := ha.span
  have huc := hu.covered
  have hus := hu.span
  have hv1 := hv.write_disjoint ((recordArrayPtr site t3 t4).toNat+32+32*i) src hb (Or.inr (by omega))
  have hu1 := hu.write_disjoint ((recordArrayPtr site t3 t4).toNat+32+32*i) src hb (Or.inl (by omega))
  have hu2 := hu1.write_disjoint ((recordValuesPtr site t4).toNat+32+32*i) value hb (Or.inl (by omega))
  have hpre : MemoryPrefix mem (recordSecondMemory mem site src t3 t4 value i) uidPtr.toNat :=
    (memoryPrefix_sparse_writeWord mem _ uidPtr.toNat src (Or.inl (by omega))).trans
      (memoryPrefix_sparse_writeWord _ _ uidPtr.toNat value (Or.inl (by omega)))
  have hrword : (refUIDPtr site t3+UInt256.ofNat 160).toNat = (refUIDPtr site t3).toNat+160 :=
    uadd_word_ofNat_toNat _ _ (by omega)
  apply easRecordTail v site hstack hp hi (by omega) ha.covered ha.length
    (by have := hv.span; omega)
    (by simpa only [hlenv] using hv1.length)
  · exact (memLoad_write_below _ _ _ _ (by rw [hrword]; omega) (by rw [hrword]; omega)).trans hvalue
  · exact (recordUIDsPtr_preserve site hpre (by omega) (by omega) hmlo hmhi hmin (by omega)).trans hptr
  · simpa only [hlenu] using hu2.length
  · exact rd

end Benchmarks.EAS.EAS
