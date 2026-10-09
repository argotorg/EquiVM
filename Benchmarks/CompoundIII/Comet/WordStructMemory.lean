import Benchmarks.CompoundIII.Comet.Common
import Reasoning.HeapMemory

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.CompoundIII.Comet

-- LIBRARY CANDIDATE: a fixed-size Solidity memory structure with one word per field.
structure WordStructMemory (mem : ByteArray) (ptr : UInt256) (n : Nat)
    (words : Nat → UInt256) : Prop where
  bound : ptr.toNat + 32 * n < UInt256.size
  size : ptr.toNat + 32 * n ≤ mem.size
  word : ∀ i, i < n → memLoad (ptr + UInt256.ofNat (32 * i)) mem = words i

theorem WordStructMemory.congr {mem ptr n words words'}
    (h : WordStructMemory mem ptr n words) (heq : ∀ i < n, words i = words' i) :
    WordStructMemory mem ptr n words' :=
  ⟨h.bound, h.size, fun i hi ↦ (h.word i hi).trans (heq i hi)⟩

theorem WordStructMemory.write {mem ptr n words}
    (h : WordStructMemory mem ptr n words) (i : Nat) (hi : i < n) (value : UInt256) :
    WordStructMemory
      (writeWord mem (ptr + UInt256.ofNat (32 * i)).toNat value) ptr n
      (fun j ↦ if j = i then value else words j) := by
  have hb := h.bound
  have hs := h.size
  have ha (j : Nat) (hj : j < n) :
      (ptr + UInt256.ofNat (32 * j)).toNat = ptr.toNat + 32 * j :=
    uadd_word_ofNat_toNat _ _ (by omega)
  refine ⟨hb, ?_, ?_⟩
  · rw [writeWord_sparse_size]
    exact le_trans hs (Nat.le_max_left _ _)
  · intro j hj
    by_cases he : j = i
    · subst j
      rw [if_pos rfl]
      apply loadedWord_of_read
      · rw [writeWord_sparse_size]; exact Nat.le_max_right _ _
      · exact writeWord_sparse_read_back _ _ _
    · rw [if_neg he]
      have hread :
          (writeWord mem (ptr + UInt256.ofNat (32 * i)).toNat value).readWithPadding
            (ptr + UInt256.ofNat (32 * j)).toNat 32 =
          mem.readWithPadding (ptr + UInt256.ofNat (32 * j)).toNat 32 := by
        apply writeWord_sparse_read_preserved
        rw [ha i hi, ha j hj]
        by_cases hji : j < i
        · exact Or.inl ⟨by omega, by omega⟩
        · exact Or.inr ⟨by omega, by omega⟩
      have hn : (ptr + UInt256.ofNat (32 * j)).toNat + 32 ≤ mem.size := by
        rw [ha j hj]; omega
      have hwsize := writeWord_sparse_size mem
        (ptr + UInt256.ofNat (32 * i)).toNat value
      rw [← h.word j hj]
      unfold memLoad
      rw [if_neg (by omega), if_neg (by omega), hread]

theorem WordStructMemory.preserve {mem mem' ptr n words}
    (h : WordStructMemory mem ptr n words) (hlo : 96 ≤ ptr.toNat)
    (hp : MemoryPrefix mem mem' (ptr.toNat + 32 * n)) :
    WordStructMemory mem' ptr n words := by
  refine ⟨h.bound, le_trans h.size hp.size, ?_⟩
  intro i hi
  have hb := h.bound
  have hs := h.size
  have ha : (ptr + UInt256.ofNat (32 * i)).toNat = ptr.toNat + 32 * i :=
    uadd_word_ofNat_toNat _ _ (by omega)
  have he : memLoad (ptr + UInt256.ofNat (32 * i)) mem' =
      memLoad (ptr + UInt256.ofNat (32 * i)) mem := by
    have hs' := hp.size
    unfold memLoad
    rw [if_neg (by omega), if_neg (by omega), hp.read _ (by omega) (by omega) (by omega)]
  exact he.trans (h.word i hi)

-- LIBRARY CANDIDATE: a word write outside a memory structure preserves all its fields.
theorem WordStructMemory.writeDisjoint {mem ptr n words}
    (h : WordStructMemory mem ptr n words) (off : Nat) (value : UInt256)
    (hd : off + 32 ≤ ptr.toNat ∨ ptr.toNat + 32 * n ≤ off) :
    WordStructMemory (writeWord mem off value) ptr n words := by
  have hb := h.bound
  have hs := h.size
  refine ⟨hb, ?_, ?_⟩
  · rw [writeWord_sparse_size]
    exact le_trans hs (Nat.le_max_left _ _)
  · intro i hi
    have ha : (ptr + UInt256.ofNat (32 * i)).toNat = ptr.toNat + 32 * i :=
      uadd_word_ofNat_toNat _ _ (by omega)
    have hr : (writeWord mem off value).readWithPadding
        (ptr + UInt256.ofNat (32 * i)).toNat 32 =
        mem.readWithPadding (ptr + UInt256.ofNat (32 * i)).toNat 32 := by
      apply writeWord_sparse_read_preserved
      rw [ha]
      rcases hd with hd | hd
      · exact Or.inr ⟨by omega, by omega⟩
      · exact Or.inl ⟨by omega, by omega⟩
    rw [← h.word i hi]
    unfold memLoad
    rw [if_neg (by rw [writeWord_sparse_size]; omega), if_neg (by omega), hr]

theorem WordStructMemory.scratch {mem ptr n words}
    (h : WordStructMemory mem ptr n words) (hlo : 96 ≤ ptr.toNat) (key slot : UInt256) :
    WordStructMemory (twoWordHashMem key slot mem) ptr n words := by
  apply h.preserve hlo
  exact (memoryPrefix_sparse_writeWord mem 0 _ key (Or.inr (by decide))).trans
    (memoryPrefix_sparse_writeWord _ 32 _ slot (Or.inr (by decide)))

end Benchmarks.CompoundIII.Comet
