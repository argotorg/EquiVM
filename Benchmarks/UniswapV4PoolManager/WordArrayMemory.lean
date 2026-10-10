import Reasoning.HeapMemory
import Reasoning.ABIViews

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.UniswapV4PoolManager

-- LIBRARY CANDIDATE: splitting an in-bounds read also permits empty pieces.
theorem readWithPadding_split (mem : ByteArray) (off n m : Nat)
    (hin : off + n + m ≤ mem.size) :
    mem.readWithPadding off (n + m) =
      mem.readWithPadding off n ++ mem.readWithPadding (off + n) m := by
  by_cases hn : n = 0
  · subst n
    simp only [Nat.zero_add, Nat.add_zero, byteArray_readWithPadding_zero, ByteArray.empty_append]
  by_cases hm : m = 0
  · subst m
    simp only [Nat.add_zero, byteArray_readWithPadding_zero, ByteArray.append_empty]
  exact byteArray_readWithPadding_split_unbounded mem off n m (by omega) (by omega) hin

-- GENERALIZES writeWord_sparse_read_preserved to arbitrary-length, possibly empty windows.
theorem writeWord_sparse_read_preserved_unbounded (mem : ByteArray) (off read len : Nat)
    (word : UInt256) (hin : read + len ≤ mem.size)
    (hdis : read + len ≤ off ∨ off + 32 ≤ read) :
    (writeWord mem off word).readWithPadding read len = mem.readWithPadding read len := by
  by_cases hz : len = 0
  · subst len; simp only [byteArray_readWithPadding_zero]
  have hpos : 0 < len := by omega
  rcases hdis with hbelow | habove
  · by_cases hoff : off ≤ mem.size
    · exact write32_read_below_len_unbounded _ _ _ _ _ (by rw [toByteArray_size]) hoff hbelow hin
        hpos
    · rw [writeWord_sparse_eq _ _ _ (by omega),
        readWithPadding_eq_extract_unbounded _ _ _ hpos (by
          simp only [ByteArray.size_append, ByteArray_zeroes_size, toByteArray_size]; omega),
        extract_append_left _ _ _ _ (by
          simp only [ByteArray.size_append, ByteArray_zeroes_size]; omega),
        extract_append_left _ _ _ _ hin,
        ← readWithPadding_eq_extract_unbounded mem read len hpos hin]
  · have hprefix : (mem.extract 0 off ++ word.toByteArray.extract 0 32).size = off + 32 := by
      simp only [ByteArray.size_append, ByteArray.size_extract, toByteArray_size]; omega
    change (word.toByteArray.write 0 mem off 32).readWithPadding read len = _
    rw [write32_eq _ _ _ (by rw [toByteArray_size]) (by omega),
      readWithPadding_eq_extract_unbounded _ _ _ hpos (by
        rw [ByteArray.size_append, hprefix, ByteArray.size_extract]; omega),
      readWithPadding_eq_extract_unbounded _ _ _ hpos hin,
      extract_append_right_window _ _ _ _ (by rw [hprefix]; omega), hprefix,
      extract_extract_BA]
    congr 1 <;> omega

-- LIBRARY CANDIDATE: sequential ABI word stores, with unbounded byte-array reads.
def wordSequenceMemory (mem : ByteArray) (off : Nat) : List UInt256 → ByteArray
  | [] => mem
  | word :: words => wordSequenceMemory (writeWord mem off word) (off + 32) words

theorem wordSequenceMemory_prefix (mem : ByteArray) (off : Nat) (words : List UInt256) :
    MemoryPrefix mem (wordSequenceMemory mem off words) off := by
  induction words generalizing mem off with
  | nil => exact .refl _ _
  | cons word words ih =>
      exact (memoryPrefix_sparse_writeWord mem off off word (.inl (le_refl _))).trans
        ((ih _ _).mono (by omega))

theorem wordSequenceMemory_size {mem : ByteArray} {off : Nat} (words : List UInt256)
    (hoff : off ≤ mem.size) :
    (wordSequenceMemory mem off words).size = max mem.size (off + 32 * words.length) := by
  induction words generalizing mem off with
  | nil => simp only [wordSequenceMemory, List.length_nil, Nat.mul_zero, Nat.add_zero]; omega
  | cons word words ih =>
      rw [wordSequenceMemory, ih (by rw [writeWord_sparse_size]; omega), writeWord_sparse_size]
      simp only [List.length_cons]; omega

theorem wordSequenceMemory_read_below (mem : ByteArray) (off : Nat) (words : List UInt256)
    (read : Nat) (hin : read + 32 ≤ mem.size) (hbelow : read + 32 ≤ off) :
    (wordSequenceMemory mem off words).readWithPadding read 32 = mem.readWithPadding read 32 := by
  induction words generalizing mem off with
  | nil => rfl
  | cons word words ih =>
      rw [wordSequenceMemory, ih _ _ (by rw [writeWord_sparse_size]; omega) (by omega)]
      exact writeWord_sparse_read_preserved mem off read word (.inl ⟨hbelow, hin⟩)

theorem wordSequenceMemory_read (mem : ByteArray) (off : Nat) (words : List UInt256)
    :
    (wordSequenceMemory mem off words).readWithPadding off (32 * words.length) = wordBytes words :=
        by
  induction words generalizing mem off with
  | nil => simp only [wordSequenceMemory, List.length_nil, Nat.mul_zero,
      byteArray_readWithPadding_zero, wordBytes]
  | cons word words ih =>
      have hext : off + 32 ≤ (writeWord mem off word).size := by rw [writeWord_sparse_size]; omega
      have hspan : off + 32 + 32 * words.length ≤
          (wordSequenceMemory (writeWord mem off word) (off + 32) words).size := by
        rw [wordSequenceMemory_size words hext]
        exact Nat.le_max_right _ _
      rw [wordSequenceMemory, List.length_cons,
        show 32 * (words.length + 1) = 32 + 32 * words.length by omega,
        readWithPadding_split _ _ _ _ hspan,
        wordSequenceMemory_read_below _ _ _ _ hext (le_refl _), writeWord_sparse_read_back,
        ih _ _]
      rfl

theorem wordSequenceMemory_read_below_unbounded (mem : ByteArray) (off : Nat)
    (words : List UInt256) (read len : Nat) (hin : read + len ≤ mem.size)
    (hbelow : read + len ≤ off) :
    (wordSequenceMemory mem off words).readWithPadding read len = mem.readWithPadding read len := by
  induction words generalizing mem off with
  | nil => rfl
  | cons word words ih =>
      rw [wordSequenceMemory, ih _ _ (by rw [writeWord_sparse_size]; omega) (by omega)]
      exact writeWord_sparse_read_preserved_unbounded mem off read len word hin (.inl hbelow)

end Benchmarks.UniswapV4PoolManager
