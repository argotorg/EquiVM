import Benchmarks.Safe.ByteCopy
import Benchmarks.Safe.MemoryBytesDecoded
import Benchmarks.Safe.Blocks.Runtime_038

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open safeRuntimeBlocks

namespace Benchmarks.Safe

-- LIBRARY CANDIDATE: store a returned byte buffer and reserve its rounded allocation.
def returnDataMemory (mem : ByteArray) (ptr : Nat) (out : ByteArray) : ByteArray :=
  out.write 0
    (writeWord (writeWord mem 64 (UInt256.ofNat (ptr + 32 + ABI.paddedSize out.size))) ptr
      (UInt256.ofNat out.size)) (ptr + 32) out.size

theorem returnDataMemory_size (mem out : ByteArray) (ptr : Nat) (hp : 96 ≤ ptr) :
    (returnDataMemory mem ptr out).size = max mem.size (ptr + 32 + out.size) := by
  rw [returnDataMemory, byteArray_write_all_size _ _ _ (by
    simp only [writeWord_sparse_size]; omega)]
  simp only [writeWord_sparse_size]
  omega

theorem returnDataMemory_free (mem out : ByteArray) (ptr : Nat) (hp : 96 ≤ ptr) :
    memLoad ⟨64⟩ (returnDataMemory mem ptr out) =
      UInt256.ofNat (ptr + 32 + ABI.paddedSize out.size) := by
  apply memLoad_of_wordRead
  change (returnDataMemory mem ptr out).readWithPadding 64 32 = _
  rw [returnDataMemory, copyWindowReadBelow _ _ _ _ _ _ _ (by omega)
      (by simp only [writeWord_sparse_size]; omega) (by omega),
    writeWordReadBelow _ _ _ _ _ (by rw [writeWord_sparse_size]; omega) hp,
    writeWord_sparse_read_back]

theorem returnDataMemory_length (mem out : ByteArray) (ptr : Nat) :
    (returnDataMemory mem ptr out).readWithPadding ptr 32 =
      (UInt256.ofNat out.size).toByteArray := by
  rw [returnDataMemory, copyWindowReadBelow _ _ _ _ _ _ _ (by omega)
    (by simp only [writeWord_sparse_size]; omega) (by omega), writeWord_sparse_read_back]

theorem returnDataMemory_word (mem out : ByteArray) (ptr : Nat) (hl : 32 ≤ out.size) :
    (returnDataMemory mem ptr out).readWithPadding (ptr + 32) 32 =
      (calldataWord out 0).toByteArray := by
  rw [returnDataMemory, copyWindow_read_word out _ 0 (ptr + 32) out.size 0
    (by omega) (by omega) (by simp only [writeWord_sparse_size]; omega) (by omega)]
  rw [readWithPadding_eq_extract out 0 hl]
  exact (calldataWord_bytes hl).symm

theorem returnDataMemory_preserved (mem out : ByteArray) (ptr off count : Nat)
    (hin : off + count ≤ mem.size) (hl : 96 ≤ off) (hh : off + count ≤ ptr) :
    (returnDataMemory mem ptr out).readWithPadding off count =
      mem.readWithPadding off count := by
  rw [returnDataMemory, copyWindowReadBelow _ _ _ _ _ _ _ (by omega)
    (by simp only [writeWord_sparse_size]; omega) (by omega),
    writeWordReadBelow _ _ _ _ _ (by rw [writeWord_sparse_size]; omega) hh,
    writeWordReadAbove _ _ _ _ _ hin hl]

theorem safeReturnDataMemory {mem out : ByteArray} {ptr : Nat}
    (hf : memLoad ⟨64⟩ mem = UInt256.ofNat ptr)
    (hb : ptr + out.size + 64 < UInt256.size) :
    safeRuntime_block_8809_memory (mem := mem) (rdata := out) = returnDataMemory mem ptr out := by
  have halloc : UInt256.land (UInt256.ofNat out.size + UInt256.ofNat 63)
      (UInt256.lnot (UInt256.ofNat 31)) = UInt256.ofNat (32 + ABI.paddedSize out.size) := by
    rw [u256_land_comm]
    apply u256_inj
    change (bytesAllocSize out.size).toNat = _
    rw [bytesAllocSize_toNat (by omega), ulit_toNat' _ (by
      dsimp [ABI.paddedSize]; omega)]
    dsimp [ABI.paddedSize]
    omega
  have hnext : UInt256.ofNat ptr + UInt256.ofNat (32 + ABI.paddedSize out.size) =
      UInt256.ofNat (ptr + 32 + ABI.paddedSize out.size) := by
    apply u256_inj
    rw [ulit_toNat' _ (by dsimp [ABI.paddedSize]; omega)]
    simpa only [Nat.add_assoc] using
      (uadd_ofNat_toNat (a := ptr) (b := 32 + ABI.paddedSize out.size) (by omega)
        (by dsimp [ABI.paddedSize]; omega) (by dsimp [ABI.paddedSize]; omega))
  have h32 : (UInt256.ofNat ptr + UInt256.ofNat 32).toNat = ptr + 32 :=
    uadd_ofNat_toNat (by omega) (by decide) (by omega)
  change memLoad (UInt256.ofNat 64) mem = UInt256.ofNat ptr at hf
  simp only [safeRuntime_block_8809_memory, hf, halloc, hnext, h32,
    ulit_toNat' ptr (by omega), ulit_toNat' out.size (by omega),
    returnDataMemory, Reasoning.Theory.writeWord]
  rfl

end Benchmarks.Safe
