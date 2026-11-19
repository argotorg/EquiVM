import Benchmarks.Midnight.ToMarketLoopStep

/-! Memory built by repeated collateral decoding, including its retained input buffer. -/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Midnight

-- LIBRARY CANDIDATE: combine natural offsets without assuming nonwrapping additions.
theorem wordAddNat_add (word : UInt256) (a b : Nat) :
    (word + UInt256.ofNat a) + UInt256.ofNat b = word + UInt256.ofNat (a + b) := by
  apply u256_inj
  simp only [uadd_toNat, ofNat_toNat_mod, Nat.mod_add_mod, Nat.add_mod_mod, Nat.add_assoc]

theorem wordAddNat_zero (word : UInt256) : word + UInt256.ofNat 0 = word := uadd_zero_r word

def collateralLoopMemory (mem : ByteArray) (ptr writePtr : UInt256) : List CollateralData → ByteArray
  | [] => mem
  | c :: cs => collateralLoopMemory (collateralStepMemory mem ptr writePtr c)
      (ptr + UInt256.ofNat 128) (writePtr + UInt256.ofNat 32) cs

theorem collateralStepMemory_bytes {mem bytes : ByteArray} {base : Nat} {ptr writePtr : UInt256}
    (c : CollateralData) (hbytes : MemoryBytes mem base bytes) (hbase : 96 ≤ base)
    (hptr : base + bytes.size ≤ ptr.toNat) (hwrite : base + bytes.size ≤ writePtr.toNat) :
    MemoryBytes (collateralStepMemory mem ptr writePtr c) base bytes := by
  exact ((hbytes.writeWord _ (Or.inr hbase)).writeWords c.words hptr).writeWord _ (Or.inl hwrite)

theorem collateralStepMemory_free {mem : ByteArray} {ptr writePtr : UInt256}
    (c : CollateralData) (hptr : 96 ≤ ptr.toNat) (hwrite : 96 ≤ writePtr.toNat) :
    memLoad (UInt256.ofNat 64) (collateralStepMemory mem ptr writePtr c) =
      ptr + UInt256.ofNat 128 := by
  have hs : 96 ≤ (writeWord mem 64 (ptr + UInt256.ofNat 128)).size := by
    rw [writeWord_sparse_size]; omega
  have hs' := writeWordArray_size_ge (writeWord mem 64 (ptr + UInt256.ofNat 128)) ptr.toNat c.words
  rw [collateralStepMemory, collateralCopyMemory,
    memLoad_writeWord_preserved _ _ _ _ (by change 96 ≤ _; omega) (Or.inl hwrite),
    memLoad_writeWordArray_below _ _ (UInt256.ofNat 64) _ hs hptr]
  exact memLoad_writeWord _ (UInt256.ofNat 64) _

theorem collateralStepMemory_size {mem : ByteArray} {ptr writePtr : UInt256} (c : CollateralData) :
    mem.size ≤ (collateralStepMemory mem ptr writePtr c).size := by
  have hs := writeWordArray_size_ge (writeWord mem 64 (ptr + UInt256.ofNat 128)) ptr.toNat c.words
  simp only [collateralStepMemory, collateralCopyMemory, writeWord_sparse_size] at *
  omega

end Benchmarks.Midnight
