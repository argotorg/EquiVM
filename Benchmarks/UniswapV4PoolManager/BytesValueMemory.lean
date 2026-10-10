import Benchmarks.UniswapV4PoolManager.SparseBytesMemory
import Benchmarks.UniswapV4PoolManager.BytesABI

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.UniswapV4PoolManager

-- LIBRARY CANDIDATE: an ABI bytes value copied to any destination in memory.
def bytesValueMemory (src mem : ByteArray) (srcOff dest : Nat) (len : UInt256) : ByteArray :=
  copyZeroMemory src (writeWord mem dest len) srcOff (dest+32) len.toNat

theorem bytesValueMemory_size (src mem : ByteArray) (srcOff dest : Nat) (len : UInt256)
    (hs : srcOff+len.toNat ≤ src.size) :
    (bytesValueMemory src mem srcOff dest len).size = max mem.size (dest+len.toNat+64) := by
  rw [bytesValueMemory, copyZeroMemory_size _ _ _ _ _ hs
    (by rw [writeWord_sparse_size]; omega), writeWord_sparse_size]
  omega

theorem bytesValueMemory_read (src mem : ByteArray) (srcOff dest : Nat) (len : UInt256)
    (hs : srcOff+len.toNat ≤ src.size) :
    (bytesValueMemory src mem srcOff dest len).readWithPadding dest (32+paddedSize len.toNat) =
      bytesValueEncoding (src.extract srcOff (srcOff+len.toNat)) := by
  have hz : (src.extract srcOff (srcOff+len.toNat)).size = len.toNat := by
    rw [ByteArray.size_extract]; omega
  rw [bytesValueMemory, copyZeroMemory_read_prefix _ _ _ _ _ _ _ hs
    (by rw [writeWord_sparse_size]; omega) rfl, writeWord_sparse_read_back,
    readWithPadding_eq_extract_any _ _ _ hs, bytesValueEncoding, hz, u256_ofNat_toNat]
  exact ByteArray.append_assoc.symm

theorem bytesValueMemory_read_before (src mem : ByteArray) (srcOff dest : Nat) (len : UInt256)
    (read count : Nat) (hs : srcOff+len.toNat ≤ src.size)
    (hin : read+count ≤ mem.size) (hb : read+count ≤ dest) :
    (bytesValueMemory src mem srcOff dest len).readWithPadding read count = mem.readWithPadding read count := by
  rw [bytesValueMemory, copyZeroMemory_read_before _ _ _ _ _ _ _ hs
    (by rw [writeWord_sparse_size]; omega) (by omega),
    writeWord_sparse_read_preserved_unbounded _ _ _ _ _ hin (.inl hb)]

end Benchmarks.UniswapV4PoolManager
