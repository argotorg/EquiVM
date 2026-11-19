import Benchmarks.Midnight.CalldataBytesEncodeMemory

/-! Length-prefixed byte strings and preservation across later heap writes. -/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Midnight

-- LIBRARY CANDIDATE: extend word-wise preservation to a complete padded byte buffer.
theorem MemoryPrefix.read_words {before after : ByteArray} {limit off n : Nat}
    (h : MemoryPrefix before after limit) (hlo : 96 ≤ off)
    (hlim : off + 32 * n ≤ limit) (hin : off + 32 * n ≤ before.size) :
    after.readWithPadding off (32 * n) = before.readWithPadding off (32 * n) := by
  induction n generalizing off with
  | zero => simp only [Nat.mul_zero, byteArray_readWithPadding_zero]
  | succ n ih =>
    cases n with
    | zero =>
      simpa only [Nat.reduceAdd, Nat.mul_one] using h.read off hlo hlim hin
    | succ n =>
      have he : 32 * (n + 1 + 1) = 32 + 32 * (n + 1) := by omega
      rw [he, byteArray_readWithPadding_split_unbounded _ _ _ _ (by decide) (by omega)
        (by have := h.size; omega),
        byteArray_readWithPadding_split_unbounded _ _ _ _ (by decide) (by omega) (by omega),
        h.read off hlo (by omega) (by omega), ih (by omega) (by omega) (by omega)]

-- LIBRARY CANDIDATE: Solidity's materialized bytes representation, including zero padding.
structure MemoryByteString (mem : ByteArray) (ptr : UInt256) (bytes : ByteArray) : Prop where
  lower : 96 ≤ ptr.toNat
  length : bytes.size < 2^64
  bound : ptr.toNat + 32 + paddedSize bytes.size < UInt256.size
  size : ptr.toNat + 32 + paddedSize bytes.size ≤ mem.size
  header : memLoad ptr mem = UInt256.ofNat bytes.size
  payload : mem.readWithPadding (ptr.toNat + 32) (paddedSize bytes.size) =
    bytes ++ ByteArray.zeroes (paddedSize bytes.size - bytes.size)

theorem MemoryByteString.preserve {before after bytes : ByteArray} {ptr : UInt256} {limit : Nat}
    (h : MemoryByteString before ptr bytes) (hp : MemoryPrefix before after limit)
    (hhi : ptr.toNat + 32 + paddedSize bytes.size ≤ limit) :
    MemoryByteString after ptr bytes := by
  refine ⟨h.lower, h.length, h.bound, h.size.trans hp.size, ?_, ?_⟩
  · rw [hp.load ptr h.lower (by omega) (by have := h.size; omega), h.header]
  · rw [show paddedSize bytes.size = 32 * ((bytes.size + 31) / 32) from by
      unfold paddedSize; omega]
    rw [hp.read_words (by have := h.lower; omega) (by
      unfold paddedSize at hhi; omega) (by
      have hmem := h.size
      unfold paddedSize at hmem
      omega)]
    simpa only [paddedSize, Nat.mul_comm] using h.payload

theorem calldataBytesEncodeMemory_stored (mem bytes : ByteArray) {ptr : UInt256} {start len : Nat}
    (hlo : 96 ≤ ptr.toNat) (hlen : len < 2^64)
    (hbound : ptr.toNat + 32 + paddedSize len < UInt256.size)
    (hs : start + len ≤ bytes.size) :
    MemoryByteString (calldataBytesEncodeMemory mem bytes ptr.toNat start len) ptr
      (bytes.extract start (start + len)) := by
  have he : (bytes.extract start (start + len)).size = len := by
    rw [ByteArray.size_extract]; omega
  refine ⟨hlo, by rw [he]; exact hlen, by rw [he]; exact hbound, ?_, ?_, ?_⟩
  · rw [he, calldataBytesEncodeMemory_size _ _ _ _ _ hs]
    have := paddedSize_le_add31 len
    omega
  · have hh := calldataBytesEncodeMemory_header mem bytes ptr.toNat start len hs (by omega)
    rw [he]
    simpa only [List.getElem_cons_zero, Nat.mul_zero, Nat.add_zero, u256_ofNat_toNat] using
      hh.load ⟨0, by simp⟩
  · rw [he]
    exact copyZeroMemory_read_padded bytes (writeWord mem ptr.toNat (UInt256.ofNat len))
      start (ptr.toNat + 32) len hs hlen

theorem MemoryByteString.writeWord_below {mem bytes : ByteArray} {ptr : UInt256} {off : Nat}
    (h : MemoryByteString mem ptr bytes) (word : UInt256) (hoff : off + 32 ≤ ptr.toNat)
    (hpad : paddedSize bytes.size < 2^64) :
    MemoryByteString (writeWord mem off word) ptr bytes := by
  refine ⟨h.lower, h.length, h.bound, ?_, ?_, ?_⟩
  · rw [writeWord_sparse_size]
    exact h.size.trans (Nat.le_max_left _ _)
  · rw [memLoad_writeWord_preserved _ _ _ _ (by have hs := h.size; omega)
      (Or.inr hoff), h.header]
  · by_cases hz : paddedSize bytes.size = 0
    · simpa only [hz, byteArray_readWithPadding_zero] using h.payload
    · rw [writeWord_sparse_read_preserved_len _ _ _ _ _ h.size (Or.inr (by omega))
        (by omega) hpad, h.payload]

theorem MemoryByteString.writeWords_below {mem bytes : ByteArray} {ptr : UInt256} {off : Nat}
    (h : MemoryByteString mem ptr bytes) (words : List UInt256)
    (hoff : off + 32 * words.length ≤ ptr.toNat) (hpad : paddedSize bytes.size < 2^64) :
    MemoryByteString (writeWordArray mem off words) ptr bytes := by
  induction words generalizing mem off with
  | nil => exact h
  | cons word rest ih =>
    simp only [List.length_cons] at hoff
    exact ih (h.writeWord_below word (by omega) hpad) (by omega)

end Benchmarks.Midnight
