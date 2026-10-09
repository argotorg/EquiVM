import Benchmarks.Safe.MemoryBytesDecoder
import Benchmarks.Safe.MemoryBytesEncoding

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Safe

def memoryBytesInitialEnd (len : Nat) : Nat := 160 + ABI.paddedSize len

theorem memoryBytesInitialEnd_bound {len : Nat} (hn : len ≤ 2 ^ 64 - 192) :
    memoryBytesInitialEnd len < 2 ^ 64 := by
  simp only [memoryBytesInitialEnd, ABI.paddedSize]
  omega

theorem memoryBytesInitialEnd_large {len : Nat} (hn : 2 ^ 64 - 192 < len) :
    2 ^ 64 ≤ memoryBytesInitialEnd len := by
  simp only [memoryBytesInitialEnd, ABI.paddedSize]
  omega

-- The compiler rounds the payload, adds its length word, then advances the initial free pointer.
theorem memoryBytesEnd_initial {len : Nat} (hn : len < 2 ^ 64) :
    memoryBytesEnd solcFreePtrMem (UInt256.ofNat len) =
      UInt256.ofNat (memoryBytesInitialEnd len) := by
  have hsize : UInt256.size = 2 ^ 256 := rfl
  have hp : ABI.paddedSize len ≤ len + 31 := by unfold ABI.paddedSize; omega
  have hr : UInt256.land (UInt256.lnot (UInt256.ofNat 31))
      (UInt256.ofNat len + UInt256.ofNat 31) = UInt256.ofNat (ABI.paddedSize len) := by
    apply u256_inj
    change (returnReserveSize len).toNat = _
    rw [returnReserveSize_toNat (by omega), ulit_toNat' _ (by omega)]
    simp only [ABI.paddedSize, Nat.mul_comm]
  have ha : UInt256.land (UInt256.ofNat 63 + UInt256.ofNat (ABI.paddedSize len))
      (UInt256.lnot (UInt256.ofNat 31)) = UInt256.ofNat (32 + ABI.paddedSize len) := by
    rw [u256_land_comm, u256_add_comm]
    apply u256_inj
    change (bytesAllocSize (ABI.paddedSize len)).toNat = _
    rw [bytesAllocSize_toNat (by omega), ulit_toNat' _ (by omega)]
    unfold ABI.paddedSize
    omega
  have hf : memLoad (UInt256.ofNat 64) solcFreePtrMem = UInt256.ofNat 128 :=
    solcFreePtrMem_mload64
  rw [memoryBytesEnd, hf, hr, ha]
  apply u256_inj
  rw [ulit_toNat' _ (by unfold memoryBytesInitialEnd; omega)]
  have hh := uadd_ofNat_toNat (a := 128) (b := 32 + ABI.paddedSize len)
    (by omega) (by omega) (by omega)
  simpa only [memoryBytesInitialEnd, ← Nat.add_assoc] using hh

def memoryBytesInitialHeader (len : Nat) : ByteArray :=
  writeWord (writeWord solcFreePtrMem 64 (UInt256.ofNat (memoryBytesInitialEnd len)))
    128 (UInt256.ofNat len)

theorem memoryBytesInitialHeader_size (len : Nat) :
    (memoryBytesInitialHeader len).size = 160 := by
  simp only [memoryBytesInitialHeader, writeWord_sparse_size, solcFreePtrMem_size]
  decide

theorem memoryBytesInitialHeader_free (len : Nat) :
    memLoad ⟨64⟩ (memoryBytesInitialHeader len) = UInt256.ofNat (memoryBytesInitialEnd len) := by
  apply memLoad_of_wordRead
  change (writeWord _ 128 _).readWithPadding 64 32 = _
  rw [writeWord_sparse_read_preserved _ _ _ _ (.inl ⟨by decide, by
    rw [writeWord_sparse_size]; omega⟩), writeWord_sparse_read_back]

theorem memoryBytesInitialHeader_length (len : Nat) :
    memLoad ⟨128⟩ (memoryBytesInitialHeader len) = UInt256.ofNat len :=
  memLoad_of_wordRead _ _ _ (writeWord_sparse_read_back _ _ _)

end Benchmarks.Safe
