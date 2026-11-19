import Benchmarks.Midnight.MemoryPrefix

/-! Typed word sequences in memory and their preservation by disjoint writes. -/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Midnight

-- LIBRARY CANDIDATE: a word outside an entire output region survives all its writes.
theorem memLoad_writeWordArray_preserved (mem : ByteArray) (base : Nat) (read : UInt256)
    (words : List UInt256) (hin : read.toNat + 32 ≤ mem.size)
    (hd : read.toNat + 32 ≤ base ∨ base + 32 * words.length ≤ read.toNat) :
    memLoad read (writeWordArray mem base words) = memLoad read mem := by
  induction words generalizing mem base with
  | nil => rfl
  | cons w ws ih =>
    have hd' : read.toNat + 32 ≤ base + 32 ∨ base + 32 + 32 * ws.length ≤ read.toNat := by
      simp only [List.length_cons] at hd
      omega
    rw [writeWordArray, ih _ _ (by rw [writeWord_sparse_size]; omega) hd']
    exact memLoad_writeWord_preserved _ _ _ _ hin (by
      simp only [List.length_cons] at hd
      omega)

-- LIBRARY CANDIDATE: a nonempty word sequence materializes its entire output region.
theorem writeWordArray_size_nonempty (mem : ByteArray) (base : Nat) (words : List UInt256)
    (hn : words ≠ []) :
    (writeWordArray mem base words).size = max mem.size (base + 32 * words.length) := by
  cases words with
  | nil => contradiction
  | cons w ws =>
    rw [writeWordArray, writeWordArray_size _ _ _ (by rw [writeWord_sparse_size]; omega),
      writeWord_sparse_size]
    simp only [List.length_cons]
    omega

structure MemoryWords (mem : ByteArray) (base : Nat) (words : List UInt256) : Prop where
  bound : base + 32 * words.length < UInt256.size
  size : base + 32 * words.length ≤ mem.size
  load : ∀ i : Fin words.length, memLoad (UInt256.ofNat (base + 32 * i.val)) mem = words[i]

theorem MemoryWords.of_writeWordArray (mem : ByteArray) (base : Nat) (words : List UInt256)
    (hb : base + 32 * words.length < UInt256.size) (hn : words ≠ []) :
    MemoryWords (writeWordArray mem base words) base words := by
  have hs : base + 32 * words.length ≤ (writeWordArray mem base words).size := by
    rw [writeWordArray_size_nonempty _ _ _ hn]
    omega
  refine ⟨hb, hs, fun i ↦ ?_⟩
  have hi := i.isLt
  have ha : (UInt256.ofNat (base + 32 * i.val)).toNat = base + 32 * i.val :=
    UInt256.toNat_ofNat_of_lt (by omega)
  apply mloadWordValue_of_readWithPadding (by rw [ha]; omega)
  rw [ha]
  exact writeWordArray_read_index mem base words i

theorem MemoryWords.load_word {mem : ByteArray} {base : Nat} {words : List UInt256}
    (h : MemoryWords mem base words) (i : Fin words.length) {word : UInt256}
    (he : word.toNat = base + 32 * i.val) : memLoad word mem = words[i] := by
  have hw := u256_ofNat_toNat word
  rw [he] at hw
  rw [← hw]
  exact h.load i

theorem MemoryWords.of_writeWord (mem : ByteArray) (base : Nat) (word : UInt256)
    (hb : base + 32 < UInt256.size) :
    MemoryWords (Reasoning.Theory.writeWord mem base word) base [word] := by
  simpa only [writeWordArray, List.length_cons, List.length_nil, Nat.reduceAdd, Nat.mul_one] using
    MemoryWords.of_writeWordArray mem base [word] (by simpa using hb) (by simp)

theorem MemoryWords.load_offset {mem : ByteArray} {base : Nat} {words : List UInt256}
    (h : MemoryWords mem base words) (i : Fin words.length) {ptr : UInt256}
    (he : ptr.toNat = base) :
    memLoad (ptr + UInt256.ofNat (32 * i.val)) mem = words[i] := by
  have hi := i.isLt
  have hb := h.bound
  apply h.load_word i
  rw [uadd_word_ofNat_toNat _ _ (by omega), he]

theorem MemoryWords.preserve {before after : ByteArray} {base : Nat} {words : List UInt256}
    (h : MemoryWords before base words) (hs : before.size ≤ after.size)
    (hr : ∀ word : UInt256, base ≤ word.toNat → word.toNat + 32 ≤ base + 32 * words.length →
      memLoad word after = memLoad word before) : MemoryWords after base words := by
  refine ⟨h.bound, h.size.trans hs, fun i ↦ ?_⟩
  have hi := i.isLt
  have hb := h.bound
  have ha : (UInt256.ofNat (base + 32 * i.val)).toNat = base + 32 * i.val :=
    UInt256.toNat_ofNat_of_lt (by omega)
  rw [hr _ (by rw [ha]; omega) (by rw [ha]; omega), h.load i]

theorem MemoryWords.writeWord {mem : ByteArray} {base off : Nat} {words : List UInt256}
    (h : MemoryWords mem base words) (word : UInt256)
    (hd : base + 32 * words.length ≤ off ∨ off + 32 ≤ base) :
    MemoryWords (Reasoning.Theory.writeWord mem off word) base words := by
  apply h.preserve (by rw [writeWord_sparse_size]; omega)
  intro read hlo hhi
  exact memLoad_writeWord_preserved _ _ _ _ (hhi.trans h.size) (by rcases hd with hd | hd <;> omega)

theorem MemoryWords.writeWords {mem : ByteArray} {base off : Nat} {words : List UInt256}
    (h : MemoryWords mem base words) (written : List UInt256)
    (hd : base + 32 * words.length ≤ off ∨ off + 32 * written.length ≤ base) :
    MemoryWords (writeWordArray mem off written) base words := by
  apply h.preserve (writeWordArray_size_ge _ _ _)
  intro read hlo hhi
  exact memLoad_writeWordArray_preserved _ _ _ _ (hhi.trans h.size)
    (by rcases hd with hd | hd <;> omega)

theorem MemoryWords.append {mem : ByteArray} {base : Nat} {first last : List UInt256}
    (hf : MemoryWords mem base first)
    (ht : MemoryWords mem (base + 32 * first.length) last) :
    MemoryWords mem base (first ++ last) := by
  refine ⟨by simpa [List.length_append, Nat.mul_add, Nat.add_assoc] using ht.bound,
    by simpa [List.length_append, Nat.mul_add, Nat.add_assoc] using ht.size, fun i ↦ ?_⟩
  have hi := i.isLt
  simp only [List.length_append] at hi
  change _ = (first ++ last)[i.val]
  by_cases hleft : i.val < first.length
  · rw [List.getElem_append_left hleft]
    exact hf.load ⟨i.val, hleft⟩
  · rw [List.getElem_append_right (by omega)]
    have hr := ht.load ⟨i.val - first.length, by omega⟩
    have he : base + 32 * first.length + 32 * (i.val - first.length) = base + 32 * i.val := by omega
    simpa only [he] using hr

theorem MemoryWords.read {mem : ByteArray} {base : Nat} {words : List UInt256}
    (h : MemoryWords mem base words) :
    mem.readWithPadding base (32 * words.length) = wordArrayBytes words := by
  apply wordArray_read_of_reads _ _ _ h.size
  intro i
  have hi := i.isLt
  have hb := h.bound
  have hs := h.size
  have ha : (UInt256.ofNat (base + 32 * i.val)).toNat = base + 32 * i.val :=
    UInt256.toNat_ofNat_of_lt (by omega)
  have hr := h.load i
  unfold memLoad at hr
  rw [ha, if_neg (by omega)] at hr
  rw [read32_roundtrip _ _ (by omega), uInt256OfByteArray_eq, hr]

theorem MemoryWords.append_writeWordArray {mem : ByteArray} {base : Nat} {first : List UInt256}
    (h : MemoryWords mem base first) (last : List UInt256)
    (hb : base + 32 * (first ++ last).length < UInt256.size) :
    MemoryWords (writeWordArray mem (base + 32 * first.length) last) base (first ++ last) := by
  by_cases hn : last = []
  · subst last
    simpa only [List.append_nil, writeWordArray] using h
  have ht := MemoryWords.of_writeWordArray mem (base + 32 * first.length) last
    (by simpa only [List.length_append, Nat.mul_add, Nat.add_assoc] using hb) hn
  have hf : MemoryWords (writeWordArray mem (base + 32 * first.length) last) base first := by
    apply h.preserve (writeWordArray_size_ge _ _ _)
    intro read hlo hhi
    exact memLoad_writeWordArray_preserved _ _ _ _ (hhi.trans h.size) (Or.inl hhi)
  refine ⟨hb, ?_, fun i ↦ ?_⟩
  · have hs := ht.size
    simpa only [List.length_append, Nat.mul_add, Nat.add_assoc] using hs
  · have hi := i.isLt
    simp only [List.length_append] at hi
    change _ = (first ++ last)[i.val]
    by_cases hleft : i.val < first.length
    · rw [List.getElem_append_left hleft]
      exact hf.load ⟨i.val, hleft⟩
    · rw [List.getElem_append_right (by omega)]
      have hr := ht.load ⟨i.val - first.length, by omega⟩
      have he : base + 32 * first.length + 32 * (i.val - first.length) = base + 32 * i.val := by omega
      simpa only [he] using hr

end Benchmarks.Midnight
