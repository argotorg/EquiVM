import Benchmarks.Auction.ReturnReserve

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Auction

-- LIBRARY CANDIDATE: zeroes uses a Nat length, so a word write needs no USize gap bound.
theorem writeWord_sparse_eq (mem : ByteArray) (off : Nat) (word : UInt256)
    (hoff : mem.size ≤ off) :
    writeWord mem off word = mem ++ ffi.ByteArray.zeroes (off - mem.size) ++ word.toByteArray := by
  have hsz : word.toByteArray.data.size = 32 := word.toByteArrayWithSizeProof.2
  have hpz : (ffi.ByteArray.zeroes (off - mem.size)).data.size = off - mem.size :=
    ByteArray_zeroes_size _
  apply ByteArray.ext
  unfold Reasoning.Theory.writeWord ByteArray.write
  rw [if_neg (by decide : ¬ ((32 : Nat) = 0)),
    if_neg (show ¬ (0 ≥ word.toByteArray.size) from by rw [toByteArray_size]; omega)]
  simp only [ByteArray.data_copySlice, ByteArray.data_append]
  have hdsz : (mem.data ++ (ffi.ByteArray.zeroes (off - mem.size)).data).size = off := by
    rw [Array.size_append, hpz]
    change mem.size + (off - mem.size) = off
    omega
  rw [toByteArray_size, show min 32 (32 - 0) = 32 from rfl,
    show min mem.size (off + 32) - (off + 32) = 0 by omega,
    show (ffi.ByteArray.zeroes 0).data = (#[] : Array UInt8) from by
      rw [zeroes_zero (n := 0) rfl]
      rfl, Array.append_empty]
  rw [Array.extract_eq_self_of_le (by rw [hdsz]),
    Array.extract_eq_self_of_le (show word.toByteArray.data.size ≤ 0 + (32 + 0) by rw [hsz]),
    Array.extract_eq_empty_of_le (by rw [hdsz]; omega), Array.append_empty]

theorem writeWord_sparse_size (mem : ByteArray) (off : Nat) (word : UInt256) :
    (writeWord mem off word).size = max mem.size (off + 32) := by
  by_cases hle : off ≤ mem.size
  · exact writeWord_size mem off word (by have hu := lt_usize 0 (by decide); omega)
  · rw [writeWord_sparse_eq mem off word (by omega), ByteArray.size_append,
      ByteArray.size_append, ByteArray_zeroes_size, toByteArray_size]
    omega

theorem writeWord_sparse_read_preserved (mem : ByteArray) (off read : Nat) (word : UInt256)
    (hdisj : (read + 32 ≤ off ∧ read + 32 ≤ mem.size) ∨
      (off + 32 ≤ read ∧ read + 32 ≤ mem.size)) :
    (writeWord mem off word).readWithPadding read 32 = mem.readWithPadding read 32 := by
  by_cases hle : off ≤ mem.size
  · exact writeWord_read_preserved mem off read word
      (by have hu := lt_usize 0 (by decide); omega) hdisj
  · have hread : read + 32 ≤ mem.size := hdisj.elim And.right And.right
    rw [writeWord_sparse_eq mem off word (by omega)]
    rw [readWithPadding_eq_extract _ read (by
      rw [ByteArray.size_append, ByteArray.size_append, ByteArray_zeroes_size, toByteArray_size]
      omega)]
    rw [extract_append_left _ _ _ _ (by
      rw [ByteArray.size_append, ByteArray_zeroes_size]
      omega), extract_append_left _ _ _ _ hread]
    exact (readWithPadding_eq_extract _ read hread).symm

theorem writeWord_sparse_read_window (mem : ByteArray) (off start len : Nat) (word : UInt256)
    (hwithin : start + len ≤ 32) (hpos : 0 < len) (hlen : len < 2 ^ 64) :
    (writeWord mem off word).readWithPadding (off + start) len =
      word.toByteArray.extract start (start + len) := by
  by_cases hle : off ≤ mem.size
  · exact writeWord_read_window mem off start len word hwithin hpos hlen
      (by have hu := lt_usize 0 (by decide); omega)
  · rw [writeWord_sparse_eq mem off word (by omega)]
    have hprefix : (mem ++ ffi.ByteArray.zeroes (off - mem.size)).size = off := by
      rw [ByteArray.size_append, ByteArray_zeroes_size]
      omega
    rw [readWithPadding_eq_extract' _ (off + start) len hpos hlen (by
      rw [ByteArray.size_append, hprefix, toByteArray_size]
      omega)]
    rw [extract_append_right_window _ _ _ _ (by rw [hprefix]; omega), hprefix]
    congr 1 <;> omega

theorem writeWord_sparse_read_back (mem : ByteArray) (off : Nat) (word : UInt256) :
    (writeWord mem off word).readWithPadding off 32 = word.toByteArray := by
  have h := writeWord_sparse_read_window mem off 0 32 word (by decide) (by decide) (by decide)
  simpa only [Nat.add_zero, Nat.zero_add,
    show word.toByteArray.extract 0 32 = word.toByteArray from by
      rw [← toByteArray_size word]
      exact byteArray_extract_self _] using h

theorem memoryPrefix_sparse_writeWord (mem : ByteArray) (off limit : Nat) (word : UInt256)
    (hdisj : limit ≤ off ∨ off + 32 ≤ 96) :
    MemoryPrefix mem (writeWord mem off word) limit := by
  refine ⟨by rw [writeWord_sparse_size]; exact Nat.le_max_left _ _, fun read hlo hhi hin ↦ ?_⟩
  apply writeWord_sparse_read_preserved
  rcases hdisj with hb | ha
  · exact Or.inl ⟨le_trans hhi hb, hin⟩
  · exact Or.inr ⟨le_trans ha hlo, hin⟩

theorem MemoryCursor.writeAbove {mem aw ptr} (h : MemoryCursor mem aw ptr)
    (off word : UInt256) (hlo : ptr.toNat ≤ off.toNat) (hb : off.toNat + 32 ≤ 2 ^ 200) :
    HeapMemory (writeWord mem off.toNat word) (expandedWords aw off ⟨32⟩) ptr := by
  have hs := writeWord_sparse_size mem off.toNat word
  refine ⟨by have hm := h.size; omega, ?_, h.lower, by omega,
    activeWords_expand32 h.active hb⟩
  rw [writeWord_sparse_read_preserved mem off.toNat 64 word
    (Or.inl ⟨by have hp := h.lower; omega, h.size⟩), h.free]

end Auction
