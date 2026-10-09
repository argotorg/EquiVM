import Benchmarks.Safe.MemoryBytesDecoded

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Safe

-- LIBRARY CANDIDATE: a length-prefixed bytes value with room for the final word load.
structure BytesMemory (mem : ByteArray) (ptr : Nat) (bytes : ByteArray) : Prop where
  length : memLoad (UInt256.ofNat ptr) mem = UInt256.ofNat bytes.size
  payload : mem.readWithPadding (ptr + 32) bytes.size = bytes
  available : ptr + 64 + bytes.size ≤ mem.size

theorem BytesMemory.word {mem bytes : ByteArray} {ptr off : Nat}
    (h : BytesMemory mem ptr bytes) (hin : off + 32 ≤ bytes.size)
    (hb : ptr + 32 + off < UInt256.size) :
    memLoad (UInt256.ofNat (ptr + 32 + off)) mem = calldataWord bytes off := by
  apply memLoad_of_wordRead
  rw [ulit_toNat' _ hb]
  have hr := paddedReadWindow mem (ptr + 32) off 32 bytes.size (by
    have := h.available; omega) hin
  rw [h.payload] at hr
  exact hr.symm.trans (calldataWord_bytes_at hin).symm

theorem BytesMemory.slice {mem bytes : ByteArray} {ptr start finish : Nat}
    (h : BytesMemory mem ptr bytes) (hs : start ≤ finish) (he : finish ≤ bytes.size) :
    mem.readWithPadding (ptr + 32 + start) (finish - start) =
      bytes.extract start finish := by
  have hr := paddedReadWindow mem (ptr + 32) start (finish - start) bytes.size (by
    have := h.available; omega) (by omega)
  rw [h.payload, Nat.add_sub_of_le hs] at hr
  exact hr.symm

theorem BytesMemory.sliceWords {mem bytes : ByteArray} {ptr start finish : Nat}
    (h : BytesMemory mem ptr bytes) (hs : start ≤ finish) (he : finish ≤ bytes.size) :
    (wordBytes (memoryWords mem (ptr + 32 + start) ((finish - start + 31) / 32))).extract
      0 (finish - start) = bytes.extract start finish := by
  rw [memoryWords_prefix _ _ _ _ (by have := h.available; omega) (by omega), h.slice hs he]

theorem BytesMemory.decoded (bytes : ByteArray) : BytesMemory (memoryBytesDecoded bytes) 128 bytes
  :=
  ⟨memoryBytesDecoded_length bytes, memoryBytesDecoded_payload bytes,
    by rw [memoryBytesDecoded_size]⟩

end Benchmarks.Safe
