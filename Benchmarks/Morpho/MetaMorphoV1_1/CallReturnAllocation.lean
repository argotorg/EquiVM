import Benchmarks.Morpho.MetaMorphoV1_1.CallReturnMemory

/-! Arithmetic for the compiled length-word-plus-payload allocation. -/

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Morpho.MetaMorphoV1_1.SourceMemory

theorem callReturnSizeWord (size : Nat) (hsize : size < 2 ^ 64) :
    UInt256.ofNat 32 + UInt256.land (UInt256.lnot (UInt256.ofNat 31))
      (UInt256.ofNat 31 + UInt256.ofNat size) = bytesAllocSize size := by
  have hs : size + 63 < UInt256.size := by change _ < 2 ^ 256; omega
  rw [u256_land_comm, u256_add_comm (UInt256.ofNat 31)]
  change UInt256.ofNat 32 + roundedSize (UInt256.ofNat size) = _
  apply u256_inj
  rw [uadd_toNat, roundedSize_toNat, UInt256.toNat_ofNat_of_lt (by omega : size < UInt256.size),
    bytesAllocSize_toNat hs, Nat.mod_eq_of_lt (by omega : size + 31 < UInt256.size)]
  change (32 + (size + 31) / 32 * 32) % UInt256.size = (size + 63) / 32 * 32
  rw [Nat.mod_eq_of_lt (by omega)]
  omega

theorem roundedSize_bytesAlloc (size : Nat) (hsize : size < 2 ^ 64) :
    roundedSize (bytesAllocSize size) = bytesAllocSize size := by
  have hs : size + 63 < UInt256.size := by change _ < 2 ^ 256; omega
  apply u256_inj
  rw [roundedSize_toNat, bytesAllocSize_toNat hs,
    Nat.mod_eq_of_lt (show (size + 63) / 32 * 32 + 31 < UInt256.size by
      change _ < 2 ^ 256; omega)]
  omega

theorem nextCursor_bytesAllocSize (ptr : UInt256) (size : Nat) (hsize : size < 2 ^ 64) :
    nextCursor ptr (bytesAllocSize size) = bytesAllocPtr ptr size := by
  rw [nextCursor, roundedSize_bytesAlloc size hsize]
  rfl

theorem allocationFits_bytesAlloc (ptr : UInt256) (size : Nat) (hsize : size < 2 ^ 64) :
    allocationFits ptr (bytesAllocSize size) ↔
      allocationFits ptr (UInt256.ofNat (32 + size)) := by
  simp only [allocationFits, nextCursor_bytesAllocSize ptr size hsize, nextCursor_bytesAlloc]

end Benchmarks.Morpho.MetaMorphoV1_1.SourceMemory
