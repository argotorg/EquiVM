import Benchmarks.UniswapV4PoolManager.SparseBytesMemory

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.UniswapV4PoolManager

-- LIBRARY CANDIDATE: an in-bounds byte sequence at an arbitrary memory offset.
structure MemorySlice (mem : ByteArray) (base : Nat) (data : ByteArray) : Prop where
  bytes : mem.readWithPadding base data.size = data
  inBounds : base+data.size ≤ mem.size

theorem MemorySlice.read_window {mem data : ByteArray} {base : Nat}
    (h : MemorySlice mem base data) (off count : Nat) (hw : off+count ≤ data.size) :
    mem.readWithPadding (base+off) count = data.extract off (off+count) := by
  rw [← h.bytes, readWithPadding_eq_extract_any _ _ _ h.inBounds, extract_extract_BA,
    readWithPadding_eq_extract_any _ _ _ (by have := h.inBounds; omega)]
  congr 1
  omega

theorem MemorySlice.writeWord {mem data : ByteArray} {base : Nat}
    (h : MemorySlice mem base data) (off : Nat) (word : UInt256)
    (hdis : base+data.size ≤ off ∨ off+32 ≤ base) :
    MemorySlice (writeWord mem off word) base data := by
  refine ⟨?_, ?_⟩
  · rw [writeWord_sparse_read_preserved_unbounded _ _ _ _ _ h.inBounds hdis]
    exact h.bytes
  · rw [writeWord_sparse_size]; have := h.inBounds; omega

theorem MemorySlice.wordSequence {mem data : ByteArray} {base : Nat}
    (h : MemorySlice mem base data) (off : Nat) (words : List UInt256)
    (hbefore : base+data.size ≤ off) :
    MemorySlice (wordSequenceMemory mem off words) base data := by
  induction words generalizing mem off with
  | nil => exact h
  | cons word words ih =>
    exact ih (h.writeWord off word (.inl hbefore)) (off+32) (by omega)

theorem MemorySlice.copy_before {mem data src : ByteArray} {base : Nat}
    (h : MemorySlice mem base data) (off : Nat) (hdest : off ≤ mem.size)
    (hbefore : base+data.size ≤ off) :
    MemorySlice (src.write 0 mem off src.size) base data := by
  refine ⟨?_, ?_⟩
  · rw [copyWindow_read_preserved_any _ _ _ _ _ _ _ (by omega) hdest h.inBounds (.inl hbefore)]
    exact h.bytes
  · rw [byteArray_write_all_size _ _ _ hdest]; have := h.inBounds; omega

-- LIBRARY CANDIDATE: each word occupies its corresponding 32-byte window.
theorem wordBytes_extract_word {words : List UInt256} {i : Nat} {word : UInt256}
    (hi : words[i]? = some word) :
    (wordBytes words).extract (32*i) (32*i+32) = word.toByteArray := by
  induction words generalizing i with
  | nil => simp at hi
  | cons first rest ih =>
    cases i with
    | zero =>
      simp only [List.getElem?_cons_zero, Option.some.injEq] at hi
      subst word
      simp only [Nat.mul_zero, Nat.zero_add, wordBytes]
      rw [extract_append_left _ _ _ _ (by rw [toByteArray_size]), toByteArray_extract_all]
    | succ i =>
      rw [wordBytes, extract_append_right_window _ _ _ _ (by rw [toByteArray_size]; omega),
        toByteArray_size]
      simpa only [show 32*(i+1)-32 = 32*i by omega,
        show 32*(i+1)+32-32 = 32*i+32 by omega] using ih hi

theorem MemorySlice.word_load {mem : ByteArray} {base : Nat} {words : List UInt256}
    (h : MemorySlice mem base (wordBytes words)) {i : Nat} {word read : UInt256}
    (hi : words[i]? = some word) (hr : read.toNat = base+32*i) :
    memLoad read mem = word := by
  have hib : i < words.length := (List.getElem?_eq_some_iff.mp hi).1
  have hs := h.inBounds
  rw [wordBytes_size] at hs
  apply loadedWord_of_read
  · rw [hr]; omega
  · rw [hr, h.read_window _ _ (by rw [wordBytes_size]; omega), wordBytes_extract_word hi]

end Benchmarks.UniswapV4PoolManager
