import Benchmarks.Midnight.MemoryWords
import Benchmarks.Midnight.CollateralData

/-! A newly allocated collateral record preserves the previously allocated memory. -/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Midnight

def collateralRecordMemory (mem : ByteArray) (ptr : UInt256) (c : CollateralData) : ByteArray :=
  writeWordArray (writeWord mem 64 (ptr + UInt256.ofNat 128)) ptr.toNat c.words

theorem collateralRecordMemory_size (mem : ByteArray) {ptr : UInt256} (c : CollateralData)
    (hp : 96 ≤ ptr.toNat) :
    (collateralRecordMemory mem ptr c).size = max mem.size (ptr.toNat + 128) := by
  rw [collateralRecordMemory, writeWordArray_size_nonempty _ _ _ (by simp [CollateralData.words]),
    writeWord_sparse_size]
  change max (max mem.size 96) (ptr.toNat + 32 * 4) = _
  omega

theorem collateralRecordMemory_prefix (mem : ByteArray) (ptr : UInt256) (c : CollateralData) :
    MemoryPrefix mem (collateralRecordMemory mem ptr c) ptr.toNat :=
  (memoryPrefix_writeWord _ _ _ _ (Or.inr (by decide))).trans
    (memoryPrefix_writeWordArray _ _ _ _ le_rfl)

theorem collateralRecordMemory_free (mem : ByteArray) {ptr : UInt256} (c : CollateralData)
    (hp : 96 ≤ ptr.toNat) :
    memLoad (UInt256.ofNat 64) (collateralRecordMemory mem ptr c) = ptr + UInt256.ofNat 128 := by
  rw [collateralRecordMemory, memLoad_writeWordArray_below _ _ (UInt256.ofNat 64) _
    (by rw [writeWord_sparse_size]; change 96 ≤ _; omega) hp]
  exact memLoad_writeWord _ _ _

theorem collateralRecordMemory_words (mem : ByteArray) {ptr : UInt256} (c : CollateralData)
    (hp : ptr.toNat + 128 < UInt256.size) :
    MemoryWords (collateralRecordMemory mem ptr c) ptr.toNat c.words :=
  MemoryWords.of_writeWordArray _ _ _ (by exact hp) (by simp [CollateralData.words])

end Benchmarks.Midnight
