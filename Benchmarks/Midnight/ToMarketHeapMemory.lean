import Benchmarks.Midnight.ToMarketArrayAllocation
import Benchmarks.Midnight.ToMarketFirstFields
import Benchmarks.Midnight.CollateralHeapMemory

/-! Memory invariants linking market allocation to the collateral-decoding loop. -/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Midnight

theorem marketFirstMemory_bytes {mem bytes : ByteArray} {base start : Nat} {ptr : UInt256}
    (hb : MemoryBytes mem base bytes) (hbelow : base + bytes.size ≤ ptr.toNat) :
    MemoryBytes (marketFirstMemory mem ptr bytes start) base bytes :=
  hb.writeWords _ hbelow

theorem marketFirstMemory_free {mem bytes : ByteArray} {start : Nat} {ptr free : UInt256}
    (hfree : memLoad (UInt256.ofNat 64) mem = free)
    (hin : 96 ≤ mem.size) (hptr : 96 ≤ ptr.toNat) :
    memLoad (UInt256.ofNat 64) (marketFirstMemory mem ptr bytes start) = free := by
  rw [marketFirstMemory, memLoad_writeWordArray_preserved mem ptr.toNat (UInt256.ofNat 64) _ hin (Or.inl hptr), hfree]

theorem marketArrayMemory_bytes {mem bytes : ByteArray} {base : Nat} {ptr n : UInt256}
    (hb : MemoryBytes mem base bytes) (hbase : 96 ≤ base)
    (hbelow : base + bytes.size ≤ ptr.toNat) :
    MemoryBytes (marketArrayMemory mem ptr n) base bytes :=
  (hb.writeWord _ (Or.inr hbase)).writeWord _ (Or.inl hbelow)

theorem marketArrayMemory_free {mem : ByteArray} {ptr n : UInt256} (hptr : 96 ≤ ptr.toNat) :
    memLoad (UInt256.ofNat 64) (marketArrayMemory mem ptr n) =
      ptr + UInt256.ofNat (pointerArrayAllocation n.toNat) := by
  rw [marketArrayMemory, memLoad_writeWord_preserved _ _ _ _ (by
    change 96 ≤ _
    rw [writeWord_sparse_size]; omega) (Or.inl hptr)]
  exact memLoad_writeWord _ (UInt256.ofNat 64) _

theorem marketArrayMemory_header {mem : ByteArray} {ptr n : UInt256}
    (hp : ptr.toNat + 32 < UInt256.size) :
    MemoryWords (marketArrayMemory mem ptr n) ptr.toNat [n] :=
  MemoryWords.of_writeWordArray _ ptr.toNat [n] hp (by simp)

theorem marketArrayMemory_preserve {mem : ByteArray} {base : Nat} {ptr n : UInt256}
    {words : List UInt256} (h : MemoryWords mem base words)
    (hbase : 96 ≤ base) (hbelow : base + 32 * words.length ≤ ptr.toNat) :
    MemoryWords (marketArrayMemory mem ptr n) base words :=
  (h.writeWord _ (Or.inr hbase)).writeWord _ (Or.inl hbelow)

theorem MemoryWords.collateralLoop {mem : ByteArray} {base : Nat} {ptr writePtr : UInt256}
    {words : List UInt256} (h : MemoryWords mem base words) (cs : List CollateralData)
    (hbase : 96 ≤ base) (hbelow : base + 32 * words.length ≤ writePtr.toNat)
    (hfit : ptr.toNat + 128 * cs.length < 2^64)
    (harray : writePtr.toNat + 32 * cs.length ≤ ptr.toNat) :
    MemoryWords (collateralLoopMemory mem ptr writePtr cs) base words := by
  apply h.preserve (collateralLoopMemory_size cs)
  intro read hlo hhi
  exact collateralLoopMemory_preserved cs hfit harray (by omega) (by omega)
    (hhi.trans h.size) (Or.inl (by omega)) (Or.inl (by omega))

end Benchmarks.Midnight
