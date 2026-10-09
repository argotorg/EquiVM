import Benchmarks.Safe.MemoryBytesEncoding
import Benchmarks.Safe.Decoders

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory

namespace Benchmarks.Safe

def preModuleHeadMemory (mem : ByteArray) (base : Nat) (target value : UInt256) : ByteArray :=
  writeWord (writeWord (writeWord mem base (UInt256.land target solcAddrMask))
    (base + 32) value) (base + 64) (UInt256.ofNat 160)

def preModuleArgsMemory (mem : ByteArray) (base len : Nat)
    (target value operation sender : UInt256) (words : List UInt256) : ByteArray :=
  writeWord (writeWord
    (memoryBytesEncodedMemory (preModuleHeadMemory mem base target value)
      (base + 160) len words) (base + 96) operation)
    (base + 128) (UInt256.land solcAddrMask sender)

theorem preModuleHeadMemory_size (mem : ByteArray) (base : Nat) (target value : UInt256) :
    (preModuleHeadMemory mem base target value).size = max mem.size (base + 96) := by
  simp only [preModuleHeadMemory, writeWord_sparse_size]
  omega

theorem preModuleHeadMemory_preserved (mem : ByteArray) (base off count : Nat)
    (target value : UInt256) (hin : off + count ≤ mem.size) (ha : off + count ≤ base) :
    (preModuleHeadMemory mem base target value).readWithPadding off count =
      mem.readWithPadding off count := by
  rw [preModuleHeadMemory, writeWordReadBelow _ _ _ _ _ (by
    simp only [writeWord_sparse_size]; omega) (by omega),
    writeWordReadBelow _ _ _ _ _ (by rw [writeWord_sparse_size]; omega) (by omega),
    writeWordReadBelow _ _ _ _ _ hin ha]

theorem preModuleHeadMemory_words (mem : ByteArray) (base src : Nat)
    (target value : UInt256) (words : List UInt256) (hw : WordArrayMemory mem src words)
    (hin : src + 32 * words.length ≤ mem.size) (ha : src + 32 * words.length ≤ base) :
    WordArrayMemory (preModuleHeadMemory mem base target value) src words := by
  intro i hi
  rw [preModuleHeadMemory_preserved _ _ _ _ _ _ (by omega) (by omega)]
  exact hw i hi

theorem preModuleArgsMemory_size (mem : ByteArray) (base len : Nat)
    (target value operation sender : UInt256) (words : List UInt256)
    (hm : mem.size ≤ base + 160) (hn : words.length = (len + 31) / 32) :
    (preModuleArgsMemory mem base len target value operation sender words).size =
      base + 224 + len := by
  rw [preModuleArgsMemory, writeWord_sparse_size, writeWord_sparse_size,
    memoryBytesEncodedMemory_size _ _ _ _ (by rw [preModuleHeadMemory_size]; omega) hn]
  omega

theorem preModuleArgsMemory_preserved (mem : ByteArray) (base len off count : Nat)
    (target value operation sender : UInt256) (words : List UInt256)
    (hin : off + count ≤ mem.size) (ha : off + count ≤ base) :
    (preModuleArgsMemory mem base len target value operation sender words).readWithPadding
      off count = mem.readWithPadding off count := by
  have hm : mem.size ≤
      (memoryBytesEncodedMemory (preModuleHeadMemory mem base target value)
        (base + 160) len words).size := by
    simp only [memoryBytesEncodedMemory, preModuleHeadMemory, writeWord_sparse_size,
      ByteArray.size_append]
    omega
  rw [preModuleArgsMemory, writeWordReadBelow _ _ _ _ _ (by
    rw [writeWord_sparse_size]; omega) (by omega),
    writeWordReadBelow _ _ _ _ _ (by omega) (by omega),
    memoryBytesEncodedMemory_preserved _ _ _ _ _ _ (by
      rw [preModuleHeadMemory_size]; omega) (by omega),
    preModuleHeadMemory_preserved _ _ _ _ _ _ hin ha]

end Benchmarks.Safe
