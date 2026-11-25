import Benchmarks.Midnight.MemorySnapshot
import Benchmarks.Midnight.PairDecode

/-! Liquidation's reserved words for the callback and its two mutable amounts. -/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Midnight

def liquidateEntryMemory (mem bytes : ByteArray) : ByteArray :=
  writeWord (writeWord (writeWord mem 736 (calldataWord bytes 228))
    608 (calldataWord bytes 100)) 640 (calldataWord bytes 68)

theorem liquidateEntryMemory_size {mem bytes : ByteArray} (hm : 832 ≤ mem.size) :
    (liquidateEntryMemory mem bytes).size = mem.size := by
  simp only [liquidateEntryMemory, writeWord_sparse_size]
  omega

theorem liquidateEntryMemory_load {mem bytes : ByteArray} (hm : 832 ≤ mem.size)
    (read : UInt256) (hi : read.toNat + 32 ≤ mem.size)
    (hd : read.toNat + 32 ≤ 608 ∨ 768 ≤ read.toNat) :
    memLoad read (liquidateEntryMemory mem bytes) = memLoad read mem := by
  unfold liquidateEntryMemory
  rw [memLoad_writeWord_preserved _ _ _ _ (by
      rw [writeWord_sparse_size, writeWord_sparse_size]
      omega) (by rcases hd with hd | hd <;> omega),
    memLoad_writeWord_preserved _ _ _ _ (by rw [writeWord_sparse_size]; omega)
      (by rcases hd with hd | hd <;> omega),
    memLoad_writeWord_preserved _ _ _ _ hi (by rcases hd with hd | hd <;> omega)]

theorem liquidateEntryMemory_seized (mem bytes : ByteArray) :
    memLoad (UInt256.ofNat 640) (liquidateEntryMemory mem bytes) = calldataWord bytes 68 :=
  memLoad_writeWord _ _ _

theorem liquidateEntryMemory_repaid (mem bytes : ByteArray) :
    memLoad (UInt256.ofNat 608) (liquidateEntryMemory mem bytes) = calldataWord bytes 100 := by
  unfold liquidateEntryMemory
  rw [memLoad_writeWord_preserved _ _ _ _ (by
      change 640 ≤ _
      rw [writeWord_sparse_size]
      omega) (Or.inl (by decide))]
  exact memLoad_writeWord _ (UInt256.ofNat 608) _

theorem liquidateEntryMemory_callback (mem bytes : ByteArray) :
    memLoad (UInt256.ofNat 736) (liquidateEntryMemory mem bytes) = calldataWord bytes 228 := by
  unfold liquidateEntryMemory
  rw [memLoad_writeWord_preserved _ _ _ _ (by
      change 768 ≤ _
      rw [writeWord_sparse_size, writeWord_sparse_size]
      omega) (Or.inr (by decide)),
    memLoad_writeWord_preserved _ _ _ _ (by
      change 768 ≤ _
      rw [writeWord_sparse_size]
      omega) (Or.inr (by decide))]
  exact memLoad_writeWord _ (UInt256.ofNat 736) _

end Benchmarks.Midnight
