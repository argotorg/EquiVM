import Benchmarks.Safe.MemoryBytesAllocation

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Safe

-- LIBRARY CANDIDATE: a memory load is always its padded 32-byte read, including zero memory.
theorem memLoadReadWord (mem : ByteArray) (off : UInt256) :
    memLoad off mem = uInt256OfByteArray (mem.readWithPadding off.toNat 32) :=
  memLoad_of_wordRead _ _ _
    (toByteArray_uInt256OfByteArray_of_size32 (paddedReadSize mem _ 32)).symm

-- LIBRARY CANDIDATE: copying an in-bounds source slice at the memory boundary appends it.
theorem copyWindowAtEnd (src mem : ByteArray) (off len : Nat) (hin : off + len ≤ src.size) :
    src.write off mem mem.size len = mem ++ src.extract off (off + len) := by
  by_cases hz : len = 0
  · rw [hz, byteArray_write_zero_length]
    have he : src.extract off (off + 0) = ByteArray.empty := by
      apply byteArray_eq_empty_of_size_eq_zero
      rw [ByteArray.size_extract]; omega
    rw [he, ByteArray.append_empty]
  · rw [copyWindow_eq _ _ _ _ _ hz hin (le_refl _), byteArray_extract_self]
    have he : mem.extract (mem.size + len) mem.size = ByteArray.empty := by
      apply byteArray_eq_empty_of_size_eq_zero
      rw [ByteArray.size_extract]; omega
    rw [he, ByteArray.append_empty]

def memoryBytesDecoded (payload : ByteArray) : ByteArray :=
  writeWord (memoryBytesInitialHeader payload.size ++ payload) (160 + payload.size) ⟨0⟩

theorem memoryBytesDecoded_size (payload : ByteArray) :
    (memoryBytesDecoded payload).size = 192 + payload.size := by
  rw [memoryBytesDecoded, writeWord_sparse_size, ByteArray.size_append,
    memoryBytesInitialHeader_size]
  omega

theorem memoryBytesDecoded_preserved (payload : ByteArray) (off count : Nat)
    (hin : off + count ≤ 160) :
    (memoryBytesDecoded payload).readWithPadding off count =
      (memoryBytesInitialHeader payload.size).readWithPadding off count := by
  rw [memoryBytesDecoded,
    writeWordReadBelow _ _ _ _ _ (by
      rw [ByteArray.size_append, memoryBytesInitialHeader_size]
      omega)
      (by omega), readAppendPrefixLen _ _ _ _ (by rw [memoryBytesInitialHeader_size]; exact hin)]

theorem memoryBytesDecoded_free (payload : ByteArray) :
    memLoad ⟨64⟩ (memoryBytesDecoded payload) =
      UInt256.ofNat (memoryBytesInitialEnd payload.size) := by
  rw [memLoadReadWord, memoryBytesDecoded_preserved _ _ _ (by decide), ← memLoadReadWord]
  exact memoryBytesInitialHeader_free payload.size

theorem memoryBytesDecoded_length (payload : ByteArray) :
    memLoad ⟨128⟩ (memoryBytesDecoded payload) = UInt256.ofNat payload.size := by
  rw [memLoadReadWord, memoryBytesDecoded_preserved _ _ _ (by decide), ← memLoadReadWord]
  exact memoryBytesInitialHeader_length payload.size

theorem memoryBytesDecoded_payload (payload : ByteArray) :
    (memoryBytesDecoded payload).readWithPadding 160 payload.size = payload := by
  rw [memoryBytesDecoded,
    writeWordReadBelow _ _ _ _ _ (by rw [ByteArray.size_append, memoryBytesInitialHeader_size])
      (le_refl _), ← memoryBytesInitialHeader_size payload.size, readAppendTail]

theorem memoryBytesDecoded_words (payload : ByteArray) :
    (wordBytes (memoryWords (memoryBytesDecoded payload) 160
      ((payload.size + 31) / 32))).extract 0 payload.size = payload := by
  rw [memoryWords_prefix _ _ _ _ (by rw [memoryBytesDecoded_size]; omega) (by omega),
    memoryBytesDecoded_payload]

theorem memoryBytesDecoded_copy {cd : ByteArray} {off len : Nat}
    (hin : off + len ≤ cd.size) :
    writeWord (cd.write off (memoryBytesInitialHeader len) 160 len) (160 + len) ⟨0⟩ =
      memoryBytesDecoded (cd.extract off (off + len)) := by
  have hs : (cd.extract off (off + len)).size = len := by rw [ByteArray.size_extract]; omega
  rw [← memoryBytesInitialHeader_size len, copyWindowAtEnd _ _ _ _ hin]
  simp only [memoryBytesDecoded, hs, memoryBytesInitialHeader_size]

end Benchmarks.Safe
