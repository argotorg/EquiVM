import Benchmarks.Midnight.MemoryPrefix

/-! Byte buffers whose complete word reads survive later heap allocations. -/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Midnight

-- LIBRARY CANDIDATE: an ABI input buffer in memory and preservation under later writes.
structure MemoryBytes (mem : ByteArray) (base : Nat) (bytes : ByteArray) : Prop where
  bound : base + bytes.size < UInt256.size
  size : base + bytes.size ≤ mem.size
  read : ∀ off, off + 32 ≤ bytes.size →
    mem.readWithPadding (base + off) 32 = bytes.extract off (off + 32)

theorem MemoryBytes.append (front bytes : ByteArray)
    (hb : front.size + bytes.size < UInt256.size) :
    MemoryBytes (front ++ bytes) front.size bytes := by
  refine ⟨hb, by rw [ByteArray.size_append], fun off ho ↦ ?_⟩
  rw [readWithPadding_eq_extract _ _ (by rw [ByteArray.size_append]; omega),
    extract_append_right_window _ _ _ _ (by omega)]
  congr 1 <;> omega

theorem MemoryBytes.load {mem bytes : ByteArray} {base : Nat}
    (h : MemoryBytes mem base bytes) {off : Nat} (ho : off + 32 ≤ bytes.size) :
    memLoad (UInt256.ofNat (base + off)) mem = calldataWord bytes off := by
  have hb := h.bound
  have hs := h.size
  have hv : (UInt256.ofNat (base + off)).toNat = base + off :=
    UInt256.toNat_ofNat_of_lt (by omega)
  apply mloadWordValue_of_readWithPadding (by rw [hv]; omega)
  rw [hv, h.read off ho, calldataWord_bytes_at ho]

theorem MemoryBytes.load_word {mem bytes : ByteArray} {base off : Nat} {word : UInt256}
    (h : MemoryBytes mem base bytes) (ho : off + 32 ≤ bytes.size)
    (hw : word.toNat = base + off) : memLoad word mem = calldataWord bytes off := by
  have he := u256_ofNat_toNat word
  rw [hw] at he
  rw [← he]
  exact h.load ho

theorem MemoryBytes.writeWord {mem bytes : ByteArray} {base off : Nat}
    (h : MemoryBytes mem base bytes) (word : UInt256)
    (hdisj : base + bytes.size ≤ off ∨ off + 32 ≤ base) :
    MemoryBytes (Reasoning.Theory.writeWord mem off word) base bytes := by
  refine ⟨h.bound, ?_, fun read hr ↦ ?_⟩
  · have hs := h.size
    rw [writeWord_sparse_size]
    omega
  · rw [writeWord_sparse_read_preserved]
    · exact h.read read hr
    · have hs := h.size
      rcases hdisj with hdisj | hdisj
      · exact Or.inl ⟨by omega, by omega⟩
      · exact Or.inr ⟨by omega, by omega⟩

theorem MemoryBytes.writeWords {mem bytes : ByteArray} {base off : Nat}
    (h : MemoryBytes mem base bytes) (words : List UInt256)
    (hdisj : base + bytes.size ≤ off) :
    MemoryBytes (writeWordArray mem off words) base bytes := by
  induction words generalizing mem off with
  | nil => exact h
  | cons word rest ih =>
    exact ih (h.writeWord word (Or.inl hdisj)) (by omega)

theorem MemoryBytes.preserve {before after bytes : ByteArray} {base limit : Nat}
    (h : MemoryBytes before base bytes) (hp : MemoryPrefix before after limit)
    (hlo : 96 ≤ base) (hhi : base + bytes.size ≤ limit) :
    MemoryBytes after base bytes := by
  refine ⟨h.bound, h.size.trans hp.size, fun off ho ↦ ?_⟩
  rw [hp.read (base + off) (by omega) (by omega) (by have := h.size; omega), h.read off ho]

-- LIBRARY CANDIDATE: appending bytes preserves any complete word in the old front.
theorem memLoad_append_left (front bytes : ByteArray) (off : UInt256)
    (h : off.toNat + 32 ≤ front.size) :
    memLoad off (front ++ bytes) = memLoad off front := by
  simp only [memLoad]
  rw [if_neg (by rw [ByteArray.size_append]; omega), if_neg (by omega),
    readWithPadding_eq_extract _ _ (by rw [ByteArray.size_append]; omega),
    extract_append_left _ _ _ _ h, readWithPadding_eq_extract _ _ h]

end Benchmarks.Midnight
