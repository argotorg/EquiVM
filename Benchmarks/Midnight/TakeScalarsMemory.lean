import Benchmarks.Midnight.TakeScalars
import Benchmarks.Midnight.OfferHeapMemory
import Benchmarks.Midnight.MemorySnapshot

/-! Preservation of the decoded heap while saving take's three address arguments. -/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Midnight

theorem takeScalarsMemory_size (mem bytes : ByteArray) :
    (takeScalarsMemory mem bytes).size = max mem.size 576 := by
  simp only [takeScalarsMemory, writeWord_sparse_size]
  omega

theorem takeScalarsMemory_free {mem bytes : ByteArray} (hm : 96 ≤ mem.size) :
    memLoad (UInt256.ofNat 64) (takeScalarsMemory mem bytes) = memLoad (UInt256.ofNat 64) mem := by
  unfold takeScalarsMemory
  rw [memLoad_writeWord_preserved _ 192 (UInt256.ofNat 64) _
      (by simp only [writeWord_sparse_size]; change 96 ≤ _; omega) (Or.inl (by decide)),
    memLoad_writeWord_preserved _ 288 (UInt256.ofNat 64) _
      (by rw [writeWord_sparse_size]; change 96 ≤ _; omega) (Or.inl (by decide)),
    memLoad_writeWord_preserved _ 544 (UInt256.ofNat 64) _ hm (Or.inl (by decide))]

theorem takeScalarsMemory_offer {mem bytes : ByteArray}
    {marketPtr arrayPtr callbackPtr root : UInt256} {offer : OfferData}
    (h : OfferStored mem ⟨832⟩ marketPtr arrayPtr callbackPtr root offer) :
    OfferStored (takeScalarsMemory mem bytes) ⟨832⟩ marketPtr arrayPtr callbackPtr root offer :=
  ((h.writeWord_below (off := 544) _ (by decide)).writeWord_below
    (off := 288) _ (by decide)).writeWord_below (off := 192) _ (by decide)

theorem takeScalarsMemory_bytes {mem bytes data : ByteArray} {ptr : UInt256}
    (h : MemoryByteString mem ptr data) (hlo : 576 ≤ ptr.toNat)
    (hpad : paddedSize data.size < 2^64) :
    MemoryByteString (takeScalarsMemory mem bytes) ptr data :=
  ((h.writeWord_below (off := 544) _ hlo hpad).writeWord_below
    (off := 288) _ (by omega) hpad).writeWord_below (off := 192) _ (by omega) hpad

theorem takeScalarsMemory_low {before after bytes : ByteArray}
    (h : MemoryWords after 96 (memoryWordSnapshot before 96 23)) (hb : 832 ≤ before.size) :
    MemoryWords (takeScalarsMemory after bytes) 96
      (memoryWordSnapshot (takeScalarsMemory before bytes) 96 23) := by
  have h1 := h.snapshot_writeWord hb 14 (by decide) (calldataWord bytes 100)
  have h2 := h1.snapshot_writeWord (by
    rw [writeWord_sparse_size]; change 832 ≤ _; omega) 6 (by decide) (calldataWord bytes 132)
  exact h2.snapshot_writeWord (by
    simp only [writeWord_sparse_size]; change 832 ≤ _; omega) 3 (by decide)
    (calldataWord bytes 164)

end Benchmarks.Midnight
