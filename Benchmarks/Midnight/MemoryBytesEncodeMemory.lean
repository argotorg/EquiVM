import Benchmarks.Midnight.MemoryBytesEncoder

/-! Memory preservation and exact output bytes for the memory bytes encoder. -/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Midnight

-- LIBRARY CANDIDATE: recover the unpadded payload of a materialized bytes value.
theorem MemoryByteString.extract {mem bytes : ByteArray} {ptr : UInt256}
    (h : MemoryByteString mem ptr bytes) :
    mem.extract (ptr.toNat + 32) (ptr.toNat + 32 + bytes.size) = bytes := by
  by_cases hz : bytes.size = 0
  · rw [hz, Nat.add_zero, ByteArray.extract_same, (ByteArray.size_eq_zero_iff.mp hz)]
  have hp := h.payload
  have hlen := nat_le_paddedSize bytes.size
  rw [readWithPadding_eq_extract_unbounded _ _ _ (by omega) h.size] at hp
  have he := congrArg (fun data : ByteArray ↦ data.extract 0 bytes.size) hp
  dsimp only at he
  rw [extract_extract_BA, Nat.add_zero, min_eq_left (by omega),
    extract_append_left _ _ _ _ le_rfl, byteArray_extract_self] at he
  exact he

theorem memoryBytesEncodeMemory_eq (mem : ByteArray) (ptr output len : Nat) :
    memoryBytesEncodeMemory mem ptr output len =
      calldataBytesEncodeMemory mem (writeWord mem output (UInt256.ofNat len))
        output (ptr + 32) len := rfl

theorem memoryBytesEncodeMemory_size (mem : ByteArray) (ptr output len : Nat)
    (hs : ptr + 32 + len ≤ mem.size) :
    (memoryBytesEncodeMemory mem ptr output len).size = max mem.size (output + len + 64) := by
  rw [memoryBytesEncodeMemory_eq]
  exact calldataBytesEncodeMemory_size _ _ _ _ _ (by rw [writeWord_sparse_size]; omega)

theorem memoryBytesEncodeMemory_prefix (mem : ByteArray) (ptr output len limit : Nat)
    (hs : ptr + 32 + len ≤ mem.size) (hl : limit ≤ output) :
    MemoryPrefix mem (memoryBytesEncodeMemory mem ptr output len) limit := by
  rw [memoryBytesEncodeMemory_eq]
  exact calldataBytesEncodeMemory_prefix _ _ _ _ _ _ (by rw [writeWord_sparse_size]; omega) hl

theorem memoryBytesEncodeMemory_load_before (mem : ByteArray) (ptr output len : Nat)
    (read : UInt256) (hs : ptr + 32 + len ≤ mem.size)
    (hin : read.toNat + 32 ≤ mem.size) (hl : read.toNat + 32 ≤ output) :
    memLoad read (memoryBytesEncodeMemory mem ptr output len) = memLoad read mem := by
  rw [memoryBytesEncodeMemory_eq]
  exact calldataBytesEncodeMemory_load_before _ _ _ _ _ _
    (by rw [writeWord_sparse_size]; omega) hin hl

theorem MemoryWords.memoryBytesEncode {mem : ByteArray} {ptr output len base : Nat}
    {words : List UInt256} (h : MemoryWords mem base words)
    (hs : ptr + 32 + len ≤ mem.size) (hl : base + 32 * words.length ≤ output) :
    MemoryWords (memoryBytesEncodeMemory mem ptr output len) base words := by
  rw [memoryBytesEncodeMemory_eq]
  exact h.calldataBytesEncode (by rw [writeWord_sparse_size]; omega) hl

theorem memoryBytesEncodeMemory_stored {mem bytes : ByteArray} {ptr output : UInt256}
    (h : MemoryByteString mem ptr bytes) (hlo : 96 ≤ output.toNat)
    (hbelow : ptr.toNat + 32 + paddedSize bytes.size ≤ output.toNat)
    (hbound : output.toNat + 32 + paddedSize bytes.size < UInt256.size) :
    MemoryByteString (memoryBytesEncodeMemory mem ptr.toNat output.toNat bytes.size) output bytes := by
  have hs := h.size
  have hl := nat_le_paddedSize bytes.size
  have hp := h.preserve (memoryPrefix_writeWord mem output.toNat
    (ptr.toNat + 32 + paddedSize bytes.size) (UInt256.ofNat bytes.size) (Or.inl hbelow)) le_rfl
  have hr := calldataBytesEncodeMemory_stored mem
    (writeWord mem output.toNat (UInt256.ofNat bytes.size))
    (ptr := output) (start := ptr.toNat + 32) (len := bytes.size) hlo h.length hbound
    (by rw [writeWord_sparse_size]; omega)
  rw [hp.extract] at hr
  exact hr

end Benchmarks.Midnight
