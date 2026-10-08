import Benchmarks.EAS.Attester.Memory

open Ethereum Ethereum.EVM

namespace Reasoning.Theory

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

-- LIBRARY CANDIDATE: preserve an arbitrary allocated window across disjoint sparse stores.
theorem writeCascade_read_preserved_unbounded (mem : ByteArray) (writes : List (Nat × UInt256))
    (read len : Nat) (hin : read + len ≤ mem.size)
    (hdis : ∀ w ∈ writes, read + len ≤ w.1 ∨ w.1 + 32 ≤ read) :
    (writeCascade mem writes).readWithPadding read len = mem.readWithPadding read len := by
  induction writes generalizing mem with
  | nil => rfl
  | cons w ws ih =>
      rw [writeCascade_cons,
        ih _ (by rw [writeWord_sparse_size]; omega)
          (by intro v hv; exact hdis v (List.mem_cons_of_mem _ hv))]
      exact writeWord_sparse_read_preserved_unbounded mem w.1 read len w.2 hin
        (hdis w List.mem_cons_self)

-- LIBRARY CANDIDATE: recover a stored word when subsequent writes are disjoint.
theorem writeCascade_read_word_at (mem : ByteArray) (writes : List (Nat × UInt256))
    (i off : Nat) (word : UInt256)
    (hget : writes[i]? = some (off, word))
    (hdis : ∀ w ∈ writes.drop (i + 1), off + 32 ≤ w.1 ∨ w.1 + 32 ≤ off) :
    (writeCascade mem writes).readWithPadding off 32 = word.toByteArray := by
  induction writes generalizing mem i with
  | nil => simp at hget
  | cons w ws ih =>
      cases i with
      | zero =>
          have hw : w = (off, word) := Option.some.inj hget
          subst w
          rw [writeCascade_cons, writeCascade_read_preserved_unbounded _ _ _ _
            (by rw [writeWord_sparse_size]; omega) (by simpa using hdis),
            writeWord_sparse_read_back]
      | succ i =>
          rw [writeCascade_cons]
          exact ih _ i hget (by simpa using hdis)

end Reasoning.Theory
