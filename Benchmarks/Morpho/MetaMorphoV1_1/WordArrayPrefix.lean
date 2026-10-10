import Benchmarks.Morpho.MetaMorphoV1_1.WordArrayInitMemory

/-! Memory invariants for arrays whose elements are initialized incrementally. -/

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Morpho.MetaMorphoV1_1

-- LIBRARY CANDIDATE: a word-array header and an initialized prefix of its elements.
structure WordArrayPrefix (mem : ByteArray) (ptr : Nat) (values : List UInt256)
    (count : Nat) : Prop where
  fit : ptr + 32 + 32 * values.length < UInt256.size
  count_le : count ≤ values.length
  size : ptr + 32 + 32 * count ≤ mem.size
  length : memLoad (UInt256.ofNat ptr) mem = UInt256.ofNat values.length
  data : ∀ j (hj : j < count), memLoad (UInt256.ofNat (ptr + 32 + 32 * j)) mem =
    values[j]'(lt_of_lt_of_le hj count_le)

theorem WordArrayPrefix.preserved {before after : ByteArray} {ptr count limit : Nat}
    {values : List UInt256} (h : WordArrayPrefix before ptr values count)
    (hp : MemoryPrefix before after limit) (hlo : 96 ≤ ptr)
    (hlimit : ptr + 32 + 32 * count ≤ limit) :
    WordArrayPrefix after ptr values count := by
  refine ⟨h.fit, h.count_le, le_trans h.size hp.size, ?_, ?_⟩
  · rw [hp.load_preserved hlo (by omega) (by have := h.size; omega)
      (by have := h.fit; omega)]
    exact h.length
  · intro j hj
    rw [hp.load_preserved (by omega) (by omega) (by have := h.size; omega)
      (by have := h.fit; have := h.count_le; omega)]
    exact h.data j hj

theorem WordArrayPrefix.write_disjoint {mem : ByteArray} {ptr count off : Nat}
    {values : List UInt256} (h : WordArrayPrefix mem ptr values count) (word : UInt256)
    (hdis : ptr + 32 + 32 * count ≤ off ∨ off + 32 ≤ ptr) :
    WordArrayPrefix (writeWord mem off word) ptr values count := by
  refine ⟨h.fit, h.count_le, ?_, ?_, ?_⟩
  · rw [writeWord_sparse_size]
    exact le_trans h.size (Nat.le_max_left _ _)
  · rw [Reasoning.Theory.writeWord, memLoad_write_disjoint _ _ _ _
      (by rw [ulit_toNat' _ (by have := h.fit; omega)]; have := h.size; omega)
      (by rw [ulit_toNat' _ (by have := h.fit; omega)]; omega)]
    exact h.length
  · intro j hj
    have hf : ptr + 32 + 32 * j < UInt256.size := by
      have := h.fit
      have := h.count_le
      omega
    rw [Reasoning.Theory.writeWord, memLoad_write_disjoint _ _ _ _
      (by rw [ulit_toNat' _ hf]; have := h.size; omega)
      (by rw [ulit_toNat' _ hf]; omega)]
    exact h.data j hj

theorem WordArrayPrefix.set {mem : ByteArray} {ptr count i : Nat}
    {values : List UInt256} (h : WordArrayPrefix mem ptr values count)
    (hi : i < count) (word : UInt256) :
    WordArrayPrefix (writeWord mem (ptr + 32 + 32 * i) word) ptr
      (values.set i word) count := by
  refine ⟨by simpa only [List.length_set] using h.fit,
    by simpa only [List.length_set] using h.count_le, ?_, ?_, ?_⟩
  · rw [writeWord_sparse_size]
    exact le_trans h.size (Nat.le_max_left _ _)
  · rw [Reasoning.Theory.writeWord, memLoad_write_disjoint _ _ _ _
      (by rw [ulit_toNat' _ (by have := h.fit; omega)]; have := h.size; omega)
      (.inl (by rw [ulit_toNat' _ (by have := h.fit; omega)]; omega)), h.length,
      List.length_set]
  · intro j hj
    have hf : ptr + 32 + 32 * j < UInt256.size := by
      have := h.fit
      have := h.count_le
      omega
    by_cases heq : i = j
    · subst j
      rw [List.getElem_set_self]
      exact memLoad_write_same _ _ _ _ (ulit_toNat' _ hf)
    · rw [List.getElem_set_ne heq, Reasoning.Theory.writeWord,
        memLoad_write_disjoint _ _ _ _
          (by rw [ulit_toNat' _ hf]; have := h.size; omega)
          (by rw [ulit_toNat' _ hf]; omega)]
      exact h.data j hj

theorem WordArrayPrefix.extend {mem : ByteArray} {ptr count : Nat}
    {values : List UInt256} (h : WordArrayPrefix mem ptr values count)
    (hi : count < values.length) (word : UInt256) :
    WordArrayPrefix (writeWord mem (ptr + 32 + 32 * count) word) ptr
      (values.set count word) (count + 1) := by
  refine ⟨by simpa only [List.length_set] using h.fit,
    by simp only [List.length_set]; omega, ?_, ?_, ?_⟩
  · rw [writeWord_sparse_size]
    omega
  · rw [Reasoning.Theory.writeWord, memLoad_write_disjoint _ _ _ _
      (by rw [ulit_toNat' _ (by have := h.fit; omega)]; have := h.size; omega)
      (.inl (by rw [ulit_toNat' _ (by have := h.fit; omega)]; omega)), h.length,
      List.length_set]
  · intro j hj
    have hf : ptr + 32 + 32 * j < UInt256.size := by have := h.fit; omega
    by_cases heq : count = j
    · subst j
      rw [List.getElem_set_self]
      exact memLoad_write_same _ _ _ _ (ulit_toNat' _ hf)
    · rw [List.getElem_set_ne heq, Reasoning.Theory.writeWord,
        memLoad_write_disjoint _ _ _ _
          (by rw [ulit_toNat' _ hf]; have := h.size; omega)
          (.inl (by rw [ulit_toNat' _ hf]; omega))]
      exact h.data j (by omega)

end Benchmarks.Morpho.MetaMorphoV1_1
