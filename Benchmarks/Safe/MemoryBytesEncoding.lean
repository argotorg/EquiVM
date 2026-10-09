import Benchmarks.Safe.MemoryBytesEncoder
import Benchmarks.Safe.AddressArrayEncoding

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory

namespace Benchmarks.Safe

-- LIBRARY CANDIDATE: a prefix of an appended buffer is read at its original boundary.
theorem readAppendTailPrefix (before after : ByteArray) (len : Nat) (hl : len ≤ after.size) :
    (before ++ after).readWithPadding before.size len = after.extract 0 len := by
  rw [← paddedReadPrefix _ _ len after.size (by simp) hl, readAppendTail]

theorem memoryBytesEncodedMemory_size (mem : ByteArray) (dst len : Nat) (words : List UInt256)
    (hm : mem.size ≤ dst) (hn : words.length = (len + 31) / 32) :
    (memoryBytesEncodedMemory mem dst len words).size = dst + 64 + len := by
  simp only [memoryBytesEncodedMemory, writeWord_sparse_size, ByteArray.size_append,
    wordBytes_size, hn]
  omega

theorem memoryBytesEncodedMemory_preserved (mem : ByteArray) (dst len off count : Nat)
    (words : List UInt256) (hin : off + count ≤ mem.size) (ha : off + count ≤ dst) :
    (memoryBytesEncodedMemory mem dst len words).readWithPadding off count =
      mem.readWithPadding off count := by
  unfold memoryBytesEncodedMemory
  rw [writeWordReadBelow _ _ _ _ _ (by
    simp only [ByteArray.size_append, writeWord_sparse_size]; omega) (by omega),
    readAppendPrefixLen _ _ _ _ (by rw [writeWord_sparse_size]; omega),
    writeWordReadBelow _ _ _ _ _ hin ha]

theorem memoryBytesEncodedMemory_header (mem : ByteArray) (dst len : Nat)
    (words : List UInt256) :
    (memoryBytesEncodedMemory mem dst len words).readWithPadding dst 32 =
      (UInt256.ofNat len).toByteArray := by
  unfold memoryBytesEncodedMemory
  rw [writeWord_sparse_read_preserved _ _ _ _ (.inl ⟨by omega, by
    simp only [ByteArray.size_append, writeWord_sparse_size]; omega⟩),
    readAppendPrefix _ _ _ (by rw [writeWord_sparse_size]; omega),
    writeWord_sparse_read_back]

theorem memoryBytesEncodedMemory_payload (mem : ByteArray) (dst len : Nat)
    (words : List UInt256) (hm : mem.size ≤ dst) (hn : words.length = (len + 31) / 32) :
    (memoryBytesEncodedMemory mem dst len words).readWithPadding (dst + 32)
      (32 * words.length) =
      (wordBytes words).extract 0 len ++ ByteArray.zeroes (32 * words.length - len) := by
  have hs : (writeWord mem dst (UInt256.ofNat len)).size = dst + 32 := by
    rw [writeWord_sparse_size]; omega
  unfold memoryBytesEncodedMemory
  rw [zeroTailRead _ _ _ _ (by
    rw [ByteArray.size_append, hs, wordBytes_size, hn]; omega) (by rw [hn]; omega)
      (by rw [hn]; omega)]
  rw [← hs, readAppendTailPrefix _ _ _ (by rw [wordBytes_size, hn]; omega)]

theorem memoryBytesEncodedMemory_read (mem : ByteArray) (dst len : Nat)
    (words : List UInt256) (hm : mem.size ≤ dst) (hn : words.length = (len + 31) / 32) :
    (memoryBytesEncodedMemory mem dst len words).readWithPadding dst
      (32 + 32 * words.length) =
      (UInt256.ofNat len).toByteArray ++ (wordBytes words).extract 0 len ++
        ByteArray.zeroes (32 * words.length - len) := by
  by_cases hz : words.length = 0
  · have hl : len = 0 := by rw [hz] at hn; omega
    have he : (wordBytes words).extract 0 0 = ByteArray.empty := by
      apply ByteArray.ext
      simp [ByteArray.data_extract]
    simp only [hz, hl, Nat.mul_zero, Nat.add_zero, Nat.sub_self,
      memoryBytesEncodedMemory_header, he, zeroes_zero rfl,
      ByteArray.append_empty]
  · rw [byteArray_readWithPadding_split_unbounded _ _ _ _ (by decide) (by omega)
      (by rw [memoryBytesEncodedMemory_size _ _ _ _ hm hn, hn]; omega),
      memoryBytesEncodedMemory_header, memoryBytesEncodedMemory_payload _ _ _ _ hm hn,
      ByteArray.append_assoc]

end Benchmarks.Safe
