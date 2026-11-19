import Benchmarks.Midnight.WordArray

/-! Preservation of allocated memory outside Solidity's scratch words and free pointer. -/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Midnight

structure MemoryPrefix (before after : ByteArray) (limit : Nat) : Prop where
  size : before.size ≤ after.size
  read : ∀ off, 96 ≤ off → off + 32 ≤ limit → off + 32 ≤ before.size →
    after.readWithPadding off 32 = before.readWithPadding off 32

theorem MemoryPrefix.refl (mem : ByteArray) (limit : Nat) : MemoryPrefix mem mem limit :=
  ⟨le_rfl, fun _ _ _ _ ↦ rfl⟩

theorem MemoryPrefix.trans {before middle after : ByteArray} {limit : Nat}
    (h₁ : MemoryPrefix before middle limit) (h₂ : MemoryPrefix middle after limit) :
    MemoryPrefix before after limit := by
  refine ⟨h₁.size.trans h₂.size, fun off hlo hlim hin ↦ ?_⟩
  rw [h₂.read off hlo hlim (hin.trans h₁.size), h₁.read off hlo hlim hin]

theorem MemoryPrefix.mono {before after : ByteArray} {limit smaller : Nat}
    (h : MemoryPrefix before after limit) (hle : smaller ≤ limit) :
    MemoryPrefix before after smaller :=
  ⟨h.size, fun off hlo hlim hin ↦ h.read off hlo (hlim.trans hle) hin⟩

theorem MemoryPrefix.load {before after : ByteArray} {limit : Nat}
    (h : MemoryPrefix before after limit) (off : UInt256)
    (hlo : 96 ≤ off.toNat) (hlim : off.toNat + 32 ≤ limit)
    (hin : off.toNat + 32 ≤ before.size) : memLoad off after = memLoad off before := by
  unfold memLoad
  rw [if_neg (by have hs := h.size; omega), if_neg (by omega), h.read off.toNat hlo hlim hin]

theorem memoryPrefix_writeWord (mem : ByteArray) (off limit : Nat) (word : UInt256)
    (hdisj : limit ≤ off ∨ off + 32 ≤ 96) :
    MemoryPrefix mem (writeWord mem off word) limit := by
  refine ⟨by rw [writeWord_sparse_size]; omega, fun read hlo hlim hin ↦ ?_⟩
  apply writeWord_sparse_read_preserved
  rcases hdisj with hdisj | hdisj
  · exact Or.inl ⟨by omega, hin⟩
  · exact Or.inr ⟨by omega, hin⟩

theorem memoryPrefix_writeWordArray (mem : ByteArray) (off limit : Nat) (words : List UInt256)
    (hbelow : limit ≤ off) : MemoryPrefix mem (writeWordArray mem off words) limit := by
  induction words generalizing mem off with
  | nil => exact .refl _ _
  | cons word rest ih =>
    exact (memoryPrefix_writeWord mem off limit word (Or.inl hbelow)).trans
      (ih _ _ (by omega))

-- LIBRARY CANDIDATE: variable-length windows preserved by sparse word writes.
theorem writeWord_sparse_read_preserved_len (mem : ByteArray) (off read len : Nat)
    (word : UInt256) (hin : read + len ≤ mem.size)
    (hdisj : read + len ≤ off ∨ off + 32 ≤ read) (hpos : 0 < len) (hlen : len < 2 ^ 64) :
    (writeWord mem off word).readWithPadding read len = mem.readWithPadding read len := by
  by_cases hoff : off ≤ mem.size
  · exact writeWord_read_preserved_len mem off read len word
      (by have hu := USize.size_pos; omega)
      (hdisj.elim (fun h ↦ Or.inl ⟨h, hin⟩) (fun h ↦ Or.inr ⟨h, hin⟩)) hpos hlen
  · rw [writeWord_sparse_eq mem off word (by omega)]
    rw [readWithPadding_eq_extract' _ read len hpos hlen (by
      rw [ByteArray.size_append, ByteArray.size_append, ByteArray_zeroes_size, toByteArray_size]
      omega)]
    rw [extract_append_left _ _ _ _ (by
      rw [ByteArray.size_append, ByteArray_zeroes_size]; omega),
      extract_append_left _ _ _ _ hin]
    exact (readWithPadding_eq_extract' _ read len hpos hlen hin).symm

theorem writeWordArray_read_below_len (mem : ByteArray) (off read len : Nat)
    (words : List UInt256) (hin : read + len ≤ mem.size) (hbelow : read + len ≤ off)
    (hpos : 0 < len) (hlen : len < 2 ^ 64) :
    (writeWordArray mem off words).readWithPadding read len = mem.readWithPadding read len := by
  induction words generalizing mem off with
  | nil => rfl
  | cons word rest ih =>
    rw [writeWordArray, ih _ _ (by rw [writeWord_sparse_size]; omega) (by omega)]
    exact writeWord_sparse_read_preserved_len _ _ _ _ _ hin (Or.inl hbelow) hpos hlen

end Benchmarks.Midnight
