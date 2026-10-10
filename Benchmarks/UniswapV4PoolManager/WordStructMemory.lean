import Benchmarks.UniswapV4PoolManager.WordStoreMemory
import Benchmarks.UniswapV4PoolManager.MappingScratchMemory

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.UniswapV4PoolManager

-- LIBRARY CANDIDATE: a finite sequence of word fields at a memory pointer.
structure WordStructView (mem : ByteArray) (ptr : UInt256) (words : List UInt256) : Prop where
  inBounds : ptr.toNat+32*words.length ≤ mem.size
  noWrap : ptr.toNat+32*words.length < UInt256.size
  load : ∀ i (hi : i < words.length), memLoad (ptr+UInt256.ofNat (32*i)) mem = words[i]

theorem WordStructView.load_zero {mem : ByteArray} {ptr : UInt256} {words : List UInt256}
    (h : WordStructView mem ptr words) (hi : 0 < words.length) : memLoad ptr mem = words[0] := by
  have hh := h.load 0 hi
  change memLoad (ptr+⟨0⟩) mem = words[0] at hh
  simpa only [uadd_zero_r] using hh

theorem WordStructView.write_disjoint {mem : ByteArray} {ptr : UInt256} {words : List UInt256}
    (h : WordStructView mem ptr words) (off : Nat) (word : UInt256)
    (hd : ptr.toNat+32*words.length ≤ off ∨ off+32 ≤ ptr.toNat) :
    WordStructView (writeWord mem off word) ptr words := by
  refine ⟨?_, h.noWrap, ?_⟩
  · rw [writeWord_sparse_size]; exact h.inBounds.trans (Nat.le_max_left _ _)
  · intro i hi
    have hn := uadd_word_ofNat_toNat ptr (32*i) (by have := h.noWrap; omega)
    rw [writeWord_sparse_load_disjoint _ _ _ _ (by rw [hn]; have := h.inBounds; omega)
      (by rw [hn]; omega)]
    exact h.load i hi

theorem WordStructView.write_field {mem : ByteArray} {ptr : UInt256} {words : List UInt256}
    (h : WordStructView mem ptr words) (i : Nat) (hi : i < words.length) (word : UInt256) :
    WordStructView (writeWord mem (ptr+UInt256.ofNat (32*i)).toNat word) ptr (words.set i word) := by
  have hlen : (words.set i word).length = words.length := List.length_set
  refine ⟨?_, ?_, ?_⟩
  · rw [hlen, writeWord_sparse_size]; exact h.inBounds.trans (Nat.le_max_left _ _)
  · simpa only [hlen] using h.noWrap
  · intro j hj
    have hj' : j < words.length := by simpa only [hlen] using hj
    by_cases he : i = j
    · subst j
      rw [writeWord_sparse_load_back]
      simp
    · have hn := uadd_word_ofNat_toNat ptr (32*i) (by have := h.noWrap; omega)
      have hm := uadd_word_ofNat_toNat ptr (32*j) (by have := h.noWrap; omega)
      rw [writeWord_sparse_load_disjoint _ _ _ _ (by rw [hm]; have := h.inBounds; omega)
        (by rw [hn, hm]; omega), h.load j hj']
      simp [he]

theorem WordStructView.hash_scratch {mem : ByteArray} {ptr : UInt256} {words : List UInt256}
    (h : WordStructView mem ptr words) (key base : UInt256) (hptr : 64 ≤ ptr.toNat) :
    WordStructView (twoWordHashMem key base mem) ptr words := by
  change WordStructView (writeWord (writeWord mem 0 key) 32 base) ptr words
  exact (h.write_disjoint 0 key (.inr (by omega))).write_disjoint 32 base (.inr hptr)

end Benchmarks.UniswapV4PoolManager
