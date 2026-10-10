import Benchmarks.UniswapV4PoolManager.WordStructMemory
import Benchmarks.UniswapV4PoolManager.PoolKeyMemory

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.UniswapV4PoolManager

-- GENERALIZES wordSequenceMemory_size: a nonempty sequence needs no initial offset bound.
theorem wordSequenceMemory_size_nonempty (mem : ByteArray) (off : Nat) (words : List UInt256)
    (hn : words ≠ []) : (wordSequenceMemory mem off words).size = max mem.size (off+32*words.length) := by
  cases words with
  | nil => exact False.elim (hn rfl)
  | cons word words =>
    rw [wordSequenceMemory, wordSequenceMemory_size words (by rw [writeWord_sparse_size]; omega), writeWord_sparse_size]
    simp only [List.length_cons]
    omega

-- LIBRARY CANDIDATE: sequential writes establish a complete word-struct view.
theorem wordStructView_sequence (mem : ByteArray) (ptr : UInt256) (words : List UInt256)
    (hn : words ≠ []) (hf : ptr.toNat+32*words.length < UInt256.size) :
    WordStructView (wordSequenceMemory mem ptr.toNat words) ptr words := by
  have hsize := wordSequenceMemory_size_nonempty mem ptr.toNat words hn
  refine ⟨by rw [hsize]; exact Nat.le_max_right _ _, hf, ?_⟩
  intro i hi
  have hp := uadd_word_ofNat_toNat ptr (32*i) (by omega)
  apply loadedWord_of_read
  · rw [hp, hsize]; omega
  · rw [hp]
    exact wordSequenceMemory_read_word _ _ _ (by simp only [List.getElem?_eq_getElem hi])

-- LIBRARY CANDIDATE: a word sequence preserves a disjoint struct, including sparse writes.
theorem WordStructView.write_sequence {mem : ByteArray} {ptr : UInt256} {words : List UInt256}
    (h : WordStructView mem ptr words) (off : Nat) (values : List UInt256)
    (hd : ptr.toNat+32*words.length ≤ off ∨ off+32*values.length ≤ ptr.toNat) :
    WordStructView (wordSequenceMemory mem off values) ptr words := by
  induction values generalizing mem off with
  | nil => exact h
  | cons word values ih =>
    simp only [wordSequenceMemory]
    apply ih (h.write_disjoint off word (by simp only [List.length_cons] at hd; omega))
    simp only [List.length_cons] at hd
    omega

-- GENERALIZES poolModifyStateMemory_load_before: arbitrary word sequences and offsets.
theorem wordSequenceMemory_load_before (mem : ByteArray) (off : Nat) (values : List UInt256) (ptr : UInt256)
    (hin : ptr.toNat+32 ≤ mem.size) (hb : ptr.toNat+32 ≤ off) :
    memLoad ptr (wordSequenceMemory mem off values) = memLoad ptr mem := by
  induction values generalizing mem off with
  | nil => rfl
  | cons word values ih =>
    rw [wordSequenceMemory, ih _ _ (by rw [writeWord_sparse_size]; omega) (by omega)]
    exact writeWord_sparse_load_disjoint _ _ _ _ hin (.inl hb)

end Benchmarks.UniswapV4PoolManager
