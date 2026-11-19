import Benchmarks.Midnight.Common

/-! Consecutive EVM word writes and fixed-array ABI return encoding. -/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Midnight

def writeWordArray (mem : ByteArray) (off : Nat) : List UInt256 → ByteArray
  | [] => mem
  | word :: rest => writeWordArray (writeWord mem off word) (off + 32) rest

def wordArrayBytes : List UInt256 → ByteArray
  | [] => .empty
  | word :: rest => word.toByteArray ++ wordArrayBytes rest

theorem wordArrayBytes_append (xs ys : List UInt256) :
    wordArrayBytes (xs ++ ys) = wordArrayBytes xs ++ wordArrayBytes ys := by
  induction xs with
  | nil => simp [wordArrayBytes]
  | cons x xs ih => simp only [List.cons_append, wordArrayBytes, ih, ByteArray.append_assoc]

theorem wordArrayBytes_size (words : List UInt256) :
    (wordArrayBytes words).size = 32 * words.length := by
  induction words with
  | nil => rfl
  | cons word rest ih =>
    simp only [wordArrayBytes, ByteArray.size_append, toByteArray_size, ih, List.length_cons]
    omega

-- LIBRARY CANDIDATE: sparse memory does not materialize a zero-only tail.
theorem writePastSourceAtEnd (src mem : ByteArray) (length : Nat) :
    src.write src.size mem mem.size length = mem := by
  simp [ByteArray.write]
  intro
  apply ByteArray.ext
  simp [ByteArray.data_copySlice]

-- LIBRARY CANDIDATE: consecutive writes compose at the end of their first region.
theorem writeWordArray_append (mem : ByteArray) (off : Nat) (xs ys : List UInt256) :
    writeWordArray mem off (xs ++ ys) =
      writeWordArray (writeWordArray mem off xs) (off + 32 * xs.length) ys := by
  induction xs generalizing mem off with
  | nil => simp [writeWordArray]
  | cons x xs ih =>
    simp only [List.cons_append, writeWordArray, ih, List.length_cons]
    congr 1
    omega

-- LIBRARY CANDIDATE: MLOAD after MSTORE at the same address.
theorem memLoad_writeWord (mem : ByteArray) (off : UInt256) (word : UInt256) :
    memLoad off (writeWord mem off.toNat word) = word := by
  apply mloadWordValue_of_readWithPadding
  · rw [writeWord_sparse_size]; omega
  · exact writeWord_sparse_read_back _ _ _

theorem memLoad_writeWord_preserved (mem : ByteArray) (off : Nat) (read word : UInt256)
    (hin : read.toNat + 32 ≤ mem.size)
    (hdisj : read.toNat + 32 ≤ off ∨ off + 32 ≤ read.toNat) :
    memLoad read (writeWord mem off word) = memLoad read mem := by
  unfold memLoad
  rw [writeWord_sparse_size, if_neg (by omega), if_neg (by omega)]
  rw [writeWord_sparse_read_preserved _ _ _ _ (hdisj.elim
    (fun h ↦ Or.inl ⟨h, hin⟩) (fun h ↦ Or.inr ⟨h, hin⟩))]

-- LIBRARY CANDIDATE: memory size after writing consecutive ABI words.
theorem writeWordArray_size (mem : ByteArray) (off : Nat) (words : List UInt256)
    (hin : off ≤ mem.size) :
    (writeWordArray mem off words).size = max mem.size (off + 32 * words.length) := by
  induction words generalizing mem off with
  | nil => simpa [writeWordArray] using (Nat.max_eq_left hin).symm
  | cons word rest ih =>
    simp only [writeWordArray, List.length_cons]
    rw [ih _ _ (by rw [writeWord_sparse_size]; exact Nat.le_max_right _ _), writeWord_sparse_size]
    omega

-- LIBRARY CANDIDATE: a lower memory word is preserved by consecutive writes.
theorem writeWordArray_size_ge (mem : ByteArray) (off : Nat) (words : List UInt256) :
    mem.size ≤ (writeWordArray mem off words).size := by
  induction words generalizing mem off with
  | nil => exact Nat.le_refl _
  | cons word words ih =>
    exact Nat.le_trans (by rw [writeWord_sparse_size]; exact Nat.le_max_left _ _)
      (ih (writeWord mem off word) (off + 32))

theorem writeWordArray_read_below (mem : ByteArray) (off read : Nat) (words : List UInt256)
    (hin : read + 32 ≤ mem.size) (hbelow : read + 32 ≤ off) :
    (writeWordArray mem off words).readWithPadding read 32 = mem.readWithPadding read 32 := by
  induction words generalizing mem off with
  | nil => rfl
  | cons word rest ih =>
    rw [writeWordArray, ih _ _ (by rw [writeWord_sparse_size]; omega) (by omega)]
    exact writeWord_sparse_read_preserved _ _ _ _ (Or.inl ⟨hbelow, hin⟩)

theorem memLoad_writeWordArray_below (mem : ByteArray) (off : Nat) (read : UInt256)
    (words : List UInt256) (hin : read.toNat + 32 ≤ mem.size) (hbelow : read.toNat + 32 ≤ off) :
    memLoad read (writeWordArray mem off words) = memLoad read mem := by
  have hsz := writeWordArray_size_ge mem off words
  unfold memLoad
  rw [if_neg (by omega), if_neg (by omega), writeWordArray_read_below _ _ _ _ hin hbelow]

-- LIBRARY CANDIDATE: each consecutive word can be loaded back by its array index.
theorem writeWordArray_read_index (mem : ByteArray) (off : Nat) (words : List UInt256)
    (i : Fin words.length) :
    (writeWordArray mem off words).readWithPadding (off + 32 * i.val) 32 =
      words[i].toByteArray := by
  induction words generalizing mem off with
  | nil => exact Fin.elim0 i
  | cons word rest ih =>
    rcases i with ⟨i, hi⟩
    cases i with
    | zero =>
      simp only [Nat.mul_zero, Nat.add_zero, List.getElem_cons_zero, writeWordArray]
      rw [writeWordArray_read_below _ _ _ _ (by rw [writeWord_sparse_size]; omega) (by omega)]
      exact writeWord_sparse_read_back _ _ _
    | succ i =>
      simpa only [writeWordArray, List.getElem_cons_succ, Nat.mul_add, Nat.mul_one,
        Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using
        ih (writeWord mem off word) (off + 32) ⟨i, by simpa using hi⟩

-- LIBRARY CANDIDATE: reconstruct an ABI word region from its individual reads.
theorem wordArray_read_of_reads (mem : ByteArray) (off : Nat) (words : List UInt256)
    (hin : off + 32 * words.length ≤ mem.size)
    (hread : ∀ i : Fin words.length,
      mem.readWithPadding (off + 32 * i.val) 32 = words[i].toByteArray) :
    mem.readWithPadding off (32 * words.length) = wordArrayBytes words := by
  induction words generalizing off with
  | nil => exact byteArray_readWithPadding_zero _ _
  | cons word rest ih =>
    by_cases hn : rest = []
    · subst rest
      simpa [wordArrayBytes] using hread ⟨0, by simp⟩
    · have hpos : 0 < rest.length := by cases rest <;> simp_all
      have hin' : off + 32 + 32 * rest.length ≤ mem.size := by
        simp only [List.length_cons] at hin
        omega
      rw [List.length_cons, Nat.mul_add, Nat.mul_one, Nat.add_comm (32 * rest.length),
        byteArray_readWithPadding_split_unbounded _ _ _ _ (by decide) (by omega) hin']
      rw [show mem.readWithPadding off 32 = word.toByteArray from by
        simpa using hread ⟨0, by simp⟩]
      rw [ih (off + 32) hin' (fun i ↦ by
        simpa [Nat.mul_add, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using
          hread ⟨i.val + 1, by simpa using i.isLt⟩)]
      rfl

theorem writeWordArray_read (mem : ByteArray) (off : Nat) (words : List UInt256)
    (hin : off ≤ mem.size) :
    (writeWordArray mem off words).readWithPadding off (32 * words.length) = wordArrayBytes words :=
  wordArray_read_of_reads _ _ _ (by rw [writeWordArray_size _ _ _ hin]; omega)
    (writeWordArray_read_index mem off words)

def wordArrayValues (words : List UInt256) : List Value :=
  words.map (fun word ↦ .int (Int.ofNat word.toNat))

-- LIBRARY CANDIDATE: encode a bounded unsigned word of arbitrary ABI width.
theorem encodeUIntWord (width : BitWidth) (word : UInt256)
    (hlt : word.toNat < EVM.twoPow width.val) :
    encodeABIValue? (.elem (.int (.uint width))) (.int (Int.ofNat word.toNat)) =
      some (EVM.Word.toBytesBE word) := by
  rcases width with ⟨width, hw⟩
  simp only [encodeABIValue?, encodeABIWord?]
  have hc : 0 ≤ Int.ofNat word.toNat ∧ Int.ofNat word.toNat < Int.ofNat (EVM.twoPow width) :=
    ⟨Int.natCast_nonneg _, Int.ofNat_lt.mpr hlt⟩
  rw [if_pos hc, if_neg (Nat.ne_of_gt hw.1)]
  simp [show EVM.word word.toNat = word from u256_ofNat_toNat word]

theorem encodeUIntWordArrayElems (width : BitWidth) (words : List UInt256)
    (hlt : ∀ word ∈ words, word.toNat < EVM.twoPow width.val) :
    encodeABIStaticArrayElems? (.elem (.int (.uint width))) (wordArrayValues words) =
      some ((wordArrayBytes words).toList) := by
  induction words with
  | nil => simp [wordArrayValues, wordArrayBytes, encodeABIStaticArrayElems?, byteArray_toList_eq]
  | cons word rest ih =>
    simp only [wordArrayValues] at ih
    simp only [wordArrayValues, List.map_cons, encodeABIStaticArrayElems?,
      encodeUIntWord width word (hlt word List.mem_cons_self), bind, Option.bind]
    rw [ih (fun w hw ↦ hlt w (List.mem_cons_of_mem _ hw))]
    simp only [wordArrayBytes, byteArray_toList_append]
    rw [word_toBytesBE_eq_toByteArray_toList]

-- LIBRARY CANDIDATE: fixed-array ABI return of bounded unsigned words.
theorem uintWordArrayReturnEncoding (width : BitWidth) (words : List UInt256)
    (hlt : ∀ word ∈ words, word.toNat < EVM.twoPow width.val) :
    encodeReturnValue? (.array (.elem (.int (.uint width))) words.length)
      (.array (wordArrayValues words)) = some (wordArrayBytes words) := by
  have hlen : (wordArrayValues words).length = words.length := List.length_map _
  have henc := encodeUIntWordArrayElems width words hlt
  simp only [encodeReturnValue?, encodeReturnValues?, encodeABIValues?, abiTupleHeadSize?,
    staticABIEncodedSize?, isDynamicABIType, bind, Option.bind, encodeABIValuesFrom?,
    encodeABIValue?, hlen, if_true, encodeABIArrayElems?, Bool.false_eq_true, if_false, henc,
    List.nil_append, List.append_nil]
  congr 1
  apply ByteArray.ext
  simp [byteArray_toList_eq]

end Benchmarks.Midnight
