import Benchmarks.Midnight.CalldataBytesEncoder

/-! Size, preserved words, and padded payload of an encoded calldata bytes value. -/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Midnight

theorem calldataBytesEncodeMemory_size (mem bytes : ByteArray) (output ptr len : Nat)
    (hs : ptr + len ≤ bytes.size) :
    (calldataBytesEncodeMemory mem bytes output ptr len).size =
      max mem.size (output + len + 64) := by
  by_cases hz : len = 0
  · subst len
    simp only [calldataBytesEncodeMemory, copyZeroMemory, ByteArray.write, if_true,
      Nat.add_zero, writeWord_sparse_size]
    omega
  · rw [calldataBytesEncodeMemory, copyZeroMemory_size _ _ _ _ _ hz hs,
      writeWord_sparse_size]
    omega

theorem calldataBytesEncodeMemory_prefix (mem bytes : ByteArray) (output ptr len limit : Nat)
    (hs : ptr + len ≤ bytes.size) (hl : limit ≤ output) :
    MemoryPrefix mem (calldataBytesEncodeMemory mem bytes output ptr len) limit := by
  have hp := memoryPrefix_writeWord mem output limit (UInt256.ofNat len) (Or.inl hl)
  by_cases hz : len = 0
  · subst len
    simp only [calldataBytesEncodeMemory, copyZeroMemory, ByteArray.write, if_true,
      Nat.add_zero]
    exact hp.trans (memoryPrefix_writeWord _ _ _ _ (Or.inl (by omega)))
  · exact hp.trans (copyZeroMemory_prefix _ _ _ _ _ _ hz hs (by omega))

theorem calldataBytesEncodeMemory_load_before (mem bytes : ByteArray) (output ptr len : Nat)
    (read : UInt256) (hs : ptr + len ≤ bytes.size)
    (hin : read.toNat + 32 ≤ mem.size) (hl : read.toNat + 32 ≤ output) :
    memLoad read (calldataBytesEncodeMemory mem bytes output ptr len) = memLoad read mem := by
  by_cases hz : len = 0
  · subst len
    simp only [calldataBytesEncodeMemory, copyZeroMemory, ByteArray.write, if_true,
      Nat.add_zero]
    rw [memLoad_writeWord_preserved _ _ _ _ (by rw [writeWord_sparse_size]; omega)
        (Or.inl (by omega)), memLoad_writeWord_preserved _ _ _ _ hin (Or.inl hl)]
  · rw [calldataBytesEncodeMemory, copyZeroMemory_load_before _ _ _ _ _ _ hz hs
        (by rw [writeWord_sparse_size]; omega) (by omega),
      memLoad_writeWord_preserved _ _ _ _ hin (Or.inl hl)]

theorem MemoryWords.calldataBytesEncode {mem bytes : ByteArray} {output ptr len base : Nat}
    {words : List UInt256} (h : MemoryWords mem base words) (hs : ptr + len ≤ bytes.size)
    (hl : base + 32 * words.length ≤ output) :
    MemoryWords (calldataBytesEncodeMemory mem bytes output ptr len) base words := by
  have hp := calldataBytesEncodeMemory_prefix mem bytes output ptr len output hs le_rfl
  apply h.preserve hp.size
  intro read hlo hhi
  exact calldataBytesEncodeMemory_load_before _ _ _ _ _ _ hs (hhi.trans h.size) (by omega)

theorem calldataBytesEncodeMemory_read_before (mem bytes : ByteArray)
    (output ptr len read count : Nat) (hs : ptr + len ≤ bytes.size)
    (hc : 0 < count) (hc64 : count < 2^64)
    (hin : read + count ≤ mem.size) (hl : read + count ≤ output) :
    (calldataBytesEncodeMemory mem bytes output ptr len).readWithPadding read count =
      mem.readWithPadding read count := by
  by_cases hz : len = 0
  · subst len
    simp only [calldataBytesEncodeMemory, copyZeroMemory, ByteArray.write, if_true,
      Nat.add_zero]
    rw [writeWord_sparse_read_preserved_len _ _ _ _ _ (by rw [writeWord_sparse_size]; omega)
        (Or.inl (by omega)) hc hc64,
      writeWord_sparse_read_preserved_len _ _ _ _ _ hin (Or.inl hl) hc hc64]
  · rw [calldataBytesEncodeMemory, copyZeroMemory_read_before _ _ _ _ _ _ _ hz hs hc hc64
        (by rw [writeWord_sparse_size]; omega) (by omega),
      writeWord_sparse_read_preserved_len _ _ _ _ _ hin (Or.inl hl) hc hc64]

theorem calldataBytesEncodeMemory_header (mem bytes : ByteArray) (output ptr len : Nat)
    (hs : ptr + len ≤ bytes.size) (hb : output + 32 < UInt256.size) :
    MemoryWords (calldataBytesEncodeMemory mem bytes output ptr len) output [UInt256.ofNat len] := by
  have hh : MemoryWords (writeWord mem output (UInt256.ofNat len)) output [UInt256.ofNat len] := by
    simpa only [writeWordArray, List.length_cons, List.length_nil, Nat.reduceAdd, Nat.mul_one] using
      MemoryWords.of_writeWordArray mem output [UInt256.ofNat len] (by simpa using hb) (by simp)
  by_cases hz : len = 0
  · subst len
    simpa only [calldataBytesEncodeMemory, copyZeroMemory, ByteArray.write, if_true,
      Nat.add_zero] using hh.writeWord ⟨0⟩ (Or.inl (by simp))
  · have hp := copyZeroMemory_prefix bytes (writeWord mem output (UInt256.ofNat len)) ptr
      (output + 32) len (output + 32) hz hs le_rfl
    apply hh.preserve hp.size
    intro read hlo hhi
    exact copyZeroMemory_load_before _ _ _ _ _ _ hz hs (hhi.trans hh.size)
      (by simpa only [List.length_cons, List.length_nil] using hhi)

theorem copyZeroMemory_read_padded (src mem : ByteArray) (ptr dest len : Nat)
    (hs : ptr + len ≤ src.size) (hlen : len < 2^64) :
    (copyZeroMemory src mem ptr dest len).readWithPadding dest (paddedSize len) =
      src.extract ptr (ptr + len) ++ ByteArray.zeroes (paddedSize len - len) := by
  have hl := nat_le_paddedSize len
  have hu := paddedSize_le_add31 len
  by_cases hz : len = 0
  · subst len
    simp only [paddedSize, Nat.reduceAdd, Nat.reduceDiv, Nat.mul_zero, Nat.sub_self,
      Nat.add_zero, byteArray_readWithPadding_zero, ByteArray.extract_same,
      zeroes_zero rfl, ByteArray.append_empty]
  have hp : 0 < len := by omega
  have hr := copyZeroMemory_read src mem ptr dest len hp hs hlen
  rw [readWithPadding_eq_extract' _ _ _ hp hlen hs] at hr
  by_cases halign : paddedSize len = len
  · rw [halign, Nat.sub_self, zeroes_zero rfl, ByteArray.append_empty, hr]
  have he : paddedSize len = len + (paddedSize len - len) := by omega
  conv_lhs => rw [he]
  rw [byteArray_readWithPadding_split_unbounded _ _ _ _ hp (by omega)
    (by rw [copyZeroMemory_size _ _ _ _ _ hz hs]; omega), hr]
  have hzword : (⟨0⟩ : UInt256).toByteArray = ByteArray.zeroes 32 := by decide +kernel
  have htail := writeWord_sparse_read_window (src.write ptr mem dest len) (dest + len)
    0 (paddedSize len - len) (⟨0⟩ : UInt256) (by omega) (by omega) (by omega)
  simp only [Nat.add_zero, Nat.zero_add, hzword] at htail
  rw [zeroes32_extract_zeroes (paddedSize len - len) (by omega)] at htail
  exact congrArg (fun tail ↦ src.extract ptr (ptr + len) ++ tail) htail

end Benchmarks.Midnight
