import Benchmarks.CompoundIII.Comet.WordStructMemory

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.CompoundIII.Comet

-- LIBRARY CANDIDATE: write a contiguous Solidity memory structure from its field words.
def wordStructStore (mem : ByteArray) (ptr : UInt256) (n : Nat)
    (words : Nat → UInt256) : ByteArray :=
  writeCascade mem ((List.range n).map fun j ↦
    ((ptr + UInt256.ofNat (32 * j)).toNat, words j))

theorem wordStructStore_zero (mem : ByteArray) (ptr : UInt256) (words : Nat → UInt256) :
    wordStructStore mem ptr 0 words = mem := rfl

theorem wordStructStore_succ (mem : ByteArray) (ptr : UInt256) (n : Nat)
    (words : Nat → UInt256) :
    wordStructStore mem ptr (n + 1) words = writeWord (wordStructStore mem ptr n words)
      (ptr + UInt256.ofNat (32 * n)).toNat (words n) := by
  simp only [wordStructStore, List.range_succ, List.map_append, List.map_cons,
    List.map_nil, writeCascade_append, writeCascade_cons, writeCascade_nil]

theorem wordStructStore_size {mem ptr n words} (hpos : 0 < n)
    (hb : ptr.toNat + 32 * n < UInt256.size) :
    (wordStructStore mem ptr n words).size = max mem.size (ptr.toNat + 32 * n) := by
  induction n with
  | zero => omega
  | succ n ih =>
      rw [wordStructStore_succ, writeWord_sparse_size,
        uadd_word_ofNat_toNat _ _ (by omega)]
      cases n with
      | zero => simp [wordStructStore_zero]
      | succ n => rw [ih (by omega) (by omega)]; omega

theorem wordStructStore_word {mem ptr n words j} (hj : j < n)
    (hb : ptr.toNat + 32 * n < UInt256.size) :
    memLoad (ptr + UInt256.ofNat (32 * j)) (wordStructStore mem ptr n words) = words j := by
  have ha : (ptr + UInt256.ofNat (32 * j)).toNat = ptr.toNat + 32 * j :=
    uadd_word_ofNat_toNat _ _ (by omega)
  have hr : (wordStructStore mem ptr n words).readWithPadding (ptr.toNat + 32 * j) 32 =
      (words j).toByteArray := by
    induction n with
    | zero => omega
    | succ n ih =>
        rw [wordStructStore_succ, uadd_word_ofNat_toNat _ _ (by omega)]
        by_cases he : j = n
        · subst j
          exact writeWord_sparse_read_back _ _ _
        · have hjn : j < n := by omega
          rw [writeWord_sparse_read_preserved _ _ _ _ (Or.inl ⟨by omega, by
            rw [wordStructStore_size (by omega) (by omega)]; omega⟩)]
          exact ih hjn (by omega)
  apply loadedWord_of_read
  · rw [ha, wordStructStore_size (by omega) hb]; omega
  · rw [ha]; exact hr

theorem wordStructStore_memory {mem ptr n words} (hpos : 0 < n)
    (hb : ptr.toNat + 32 * n < UInt256.size) :
    WordStructMemory (wordStructStore mem ptr n words) ptr n words := by
  refine ⟨hb, ?_, fun _ hj ↦ wordStructStore_word hj hb⟩
  rw [wordStructStore_size hpos hb]
  exact Nat.le_max_right _ _

theorem wordStructStore_prefix {mem ptr n words limit}
    (hb : ptr.toNat + 32 * n < UInt256.size) (hl : limit ≤ ptr.toNat) :
    MemoryPrefix mem (wordStructStore mem ptr n words) limit := by
  apply memoryPrefix_sparse_cascade
  intro w hw
  obtain ⟨j, hj, rfl⟩ := List.mem_map.mp hw
  have hj' := List.mem_range.mp hj
  left
  dsimp only
  rw [uadd_word_ofNat_toNat _ _ (by omega)]
  omega

end Benchmarks.CompoundIII.Comet
