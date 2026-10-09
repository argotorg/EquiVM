import Benchmarks.Safe.MemoryBytesEncoding

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory

namespace Benchmarks.Safe

theorem memoryBytesEncodedInto_size (mem : ByteArray) (dst len : Nat) (words : List UInt256)
    (hn : words.length = (len + 31) / 32) :
    (memoryBytesEncodedInto mem dst len words).size = max mem.size (dst + 64 + len) := by
  rw [memoryBytesEncodedInto, writeWord_sparse_size,
    writeWords_size _ _ _ (by rw [writeWord_sparse_size]; omega), writeWord_sparse_size]
  rw [hn]
  omega

theorem memoryBytesEncodedInto_preserved (mem : ByteArray) (dst len off count : Nat)
    (words : List UInt256) (hin : off + count ≤ mem.size) (ha : off + count ≤ dst) :
    (memoryBytesEncodedInto mem dst len words).readWithPadding off count =
      mem.readWithPadding off count := by
  unfold memoryBytesEncodedInto
  rw [writeWordReadBelow _ _ _ _ _ (by
    rw [writeWords_size _ _ _ (by rw [writeWord_sparse_size]; omega),
      writeWord_sparse_size]; omega) (by omega),
    writeWords_readBelow _ _ _ _ _ (by rw [writeWord_sparse_size]; omega) (by omega),
    writeWordReadBelow _ _ _ _ _ hin ha]

theorem memoryBytesEncodedInto_header (mem : ByteArray) (dst len : Nat)
    (words : List UInt256) :
    (memoryBytesEncodedInto mem dst len words).readWithPadding dst 32 =
      (UInt256.ofNat len).toByteArray := by
  unfold memoryBytesEncodedInto
  rw [writeWordReadBelow _ _ _ _ _ (by
      rw [writeWords_size _ _ _ (by rw [writeWord_sparse_size]; omega),
        writeWord_sparse_size]; omega) (by omega),
    writeWords_readBelow _ _ _ _ _ (by rw [writeWord_sparse_size]; omega) (by omega),
    writeWord_sparse_read_back]

theorem memoryBytesEncodedInto_payload (mem : ByteArray) (dst len : Nat)
    (words : List UInt256) (hn : words.length = (len + 31) / 32) :
    (memoryBytesEncodedInto mem dst len words).readWithPadding (dst + 32)
      (32 * words.length) =
      (wordBytes words).extract 0 len ++ ByteArray.zeroes (32 * words.length - len) := by
  have hin : dst + 32 + 32 * words.length ≤
      (writeWords (writeWord mem dst (UInt256.ofNat len)) (dst + 32) words).size := by
    rw [writeWords_size _ _ _ (by rw [writeWord_sparse_size]; omega)]
    omega
  unfold memoryBytesEncodedInto
  rw [zeroTailRead _ _ _ _ (by rw [hn] at hin; omega) (by rw [hn]; omega)
      (by rw [hn]; omega),
    ← paddedReadPrefix _ _ _ (32 * words.length) hin (by rw [hn]; omega),
    WordArrayMemory.read _ _ _ (writeWords_view _ _ _) hin]

theorem memoryBytesEncodedInto_read (mem : ByteArray) (dst len : Nat)
    (words : List UInt256) (hn : words.length = (len + 31) / 32) :
    (memoryBytesEncodedInto mem dst len words).readWithPadding dst
      (32 + 32 * words.length) =
      (UInt256.ofNat len).toByteArray ++ (wordBytes words).extract 0 len ++
        ByteArray.zeroes (32 * words.length - len) := by
  by_cases hz : words.length = 0
  · have hl : len = 0 := by rw [hz] at hn; omega
    have he : (wordBytes words).extract 0 0 = ByteArray.empty := by
      apply ByteArray.ext
      simp
    simp only [hz, hl, Nat.mul_zero, Nat.add_zero, Nat.sub_self,
      memoryBytesEncodedInto_header, he, zeroes_zero rfl, ByteArray.append_empty]
  · rw [byteArray_readWithPadding_split_unbounded _ _ _ _ (by decide) (by omega)
      (by rw [memoryBytesEncodedInto_size _ _ _ _ hn, hn]; omega),
      memoryBytesEncodedInto_header, memoryBytesEncodedInto_payload _ _ _ _ hn,
      ByteArray.append_assoc]

end Benchmarks.Safe
