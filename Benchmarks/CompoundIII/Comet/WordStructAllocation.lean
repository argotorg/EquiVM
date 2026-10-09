import Benchmarks.CompoundIII.Comet.WordStructStore

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.CompoundIII.Comet

-- GENERALIZES userBasicAllocatedMemory to arbitrary fixed-size memory structures.
def allocatedWordStruct (mem : ByteArray) (ptr : UInt256) (n : Nat)
    (words : Nat → UInt256) : ByteArray :=
  wordStructStore (writeWord mem 64 (ptr + UInt256.ofNat (32 * n))) ptr n words

theorem allocatedWordStruct_size {mem ptr n words} (hn : 0 < n) (hlo : 96 ≤ ptr.toNat)
    (hb : ptr.toNat + 32 * n < UInt256.size) :
    (allocatedWordStruct mem ptr n words).size = max mem.size (ptr.toNat + 32 * n) := by
  unfold allocatedWordStruct
  rw [wordStructStore_size hn hb, writeWord_sparse_size]
  omega

theorem allocatedWordStruct_free {mem ptr n words} (hn : 0 < n) (hlo : 96 ≤ ptr.toNat)
    (hb : ptr.toNat + 32 * n < UInt256.size) :
    memLoad (UInt256.ofNat 64) (allocatedWordStruct mem ptr n words) =
      ptr + UInt256.ofNat (32 * n) := by
  apply loadedWord_of_read
  · rw [allocatedWordStruct_size hn hlo hb]
    change 64 + 32 ≤ _; omega
  · change (wordStructStore (writeWord mem 64 (ptr + UInt256.ofNat (32 * n))) ptr n words
      ).readWithPadding 64 32 = _
    unfold wordStructStore
    rw [sparseCascade_read_below _ _ 64 (by rw [writeWord_sparse_size]; omega) (by
      intro w hw
      obtain ⟨j, hj, rfl⟩ := List.mem_map.mp hw
      have hj' := List.mem_range.mp hj
      dsimp only
      rw [uadd_word_ofNat_toNat _ _ (by omega)]
      omega)]
    exact writeWord_sparse_read_back _ _ _

theorem allocatedWordStruct_prefix {mem ptr n words}
    (hb : ptr.toNat + 32 * n < UInt256.size) :
    MemoryPrefix mem (allocatedWordStruct mem ptr n words) ptr.toNat :=
  (memoryPrefix_sparse_writeWord mem 64 _ _ (Or.inr (by decide))).trans
    (wordStructStore_prefix hb (le_refl _))

end Benchmarks.CompoundIII.Comet
