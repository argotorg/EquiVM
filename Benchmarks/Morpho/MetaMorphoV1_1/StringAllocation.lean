import Benchmarks.Morpho.MetaMorphoV1_1.AllocationRoutines

/-! Allocation arithmetic for a storage string copied at the initial free-memory cursor. -/

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory
open Benchmarks.Morpho.MetaMorphoV1_1.SourceMemory

namespace Benchmarks.Morpho.MetaMorphoV1_1

def stringWordCount (len : UInt256) : Nat := (len.toNat + 31) / 32

def stringCopySize (len : UInt256) : UInt256 := UInt256.ofNat (32 + 32 * stringWordCount len)

def stringCopyEnd (len : UInt256) : UInt256 := UInt256.ofNat (160 + 32 * stringWordCount len)

theorem stringCopySize_toNat (len : UInt256) (hlen : len.toNat < 2 ^ 255) :
    (stringCopySize len).toNat = 32 + 32 * stringWordCount len := by
  apply UInt256.toNat_ofNat_of_lt
  change 32 + 32 * ((len.toNat + 31) / 32) < 2 ^ 256
  omega

theorem stringCopyEnd_toNat (len : UInt256) (hlen : len.toNat < 2 ^ 255) :
    (stringCopyEnd len).toNat = 160 + 32 * stringWordCount len := by
  apply UInt256.toNat_ofNat_of_lt
  change 160 + 32 * ((len.toNat + 31) / 32) < 2 ^ 256
  omega

theorem stringRoundedSourceSize (len : UInt256) (hlen : len.toNat < 2 ^ 255) :
    roundedSize (UInt256.ofNat (len.toNat + 32)) = stringCopySize len := by
  have hs : len.toNat + 32 < UInt256.size := by change _ < 2 ^ 256; omega
  apply u256_inj
  rw [roundedSize_toNat, UInt256.toNat_ofNat_of_lt hs, stringCopySize_toNat len hlen,
    Nat.mod_eq_of_lt (show len.toNat + 32 + 31 < UInt256.size by change _ < 2 ^ 256; omega)]
  unfold stringWordCount
  omega

theorem stringRoundedCopySize (len : UInt256) (hlen : len.toNat < 2 ^ 255) :
    roundedSize (stringCopySize len) = stringCopySize len := by
  apply u256_inj
  rw [roundedSize_toNat, stringCopySize_toNat len hlen]
  have hs : 32 + 32 * stringWordCount len + 31 < UInt256.size := by
    change 32 + 32 * ((len.toNat + 31) / 32) + 31 < 2 ^ 256
    omega
  rw [Nat.mod_eq_of_lt hs]
  omega

theorem stringCopyNextCursor (len : UInt256) (hlen : len.toNat < 2 ^ 255) :
    nextCursor ⟨128⟩ (stringCopySize len) = stringCopyEnd len := by
  rw [nextCursor, stringRoundedCopySize len hlen]
  apply u256_inj
  rw [uadd_toNat, stringCopySize_toNat len hlen, stringCopyEnd_toNat len hlen]
  change (128 + (32 + 32 * stringWordCount len)) % UInt256.size = _
  have hb : 128 + (32 + 32 * stringWordCount len) < UInt256.size := by
    change 128 + (32 + 32 * ((len.toNat + 31) / 32)) < 2 ^ 256
    omega
  rw [Nat.mod_eq_of_lt hb]
  omega

theorem stringSourceNextCursor (len : UInt256) (hlen : len.toNat < 2 ^ 255) :
    nextCursor ⟨128⟩ (UInt256.ofNat (len.toNat + 32)) = stringCopyEnd len := by
  rw [← stringCopyNextCursor len hlen]
  simp only [nextCursor, stringRoundedSourceSize len hlen, stringRoundedCopySize len hlen]

theorem stringAllocationFits (len : UInt256) (hlen : len.toNat < 2 ^ 255) :
    allocationFits ⟨128⟩ (stringCopySize len) ↔
      allocationFits ⟨128⟩ (UInt256.ofNat (len.toNat + 32)) := by
  simp only [allocationFits, stringCopyNextCursor len hlen, stringSourceNextCursor len hlen]

theorem stringCopySize_sub (len : UInt256) (hlen : len.toNat < 2 ^ 255) :
    UInt256.sub (stringCopyEnd len) ⟨128⟩ = stringCopySize len := by
  apply u256_inj
  rw [usub_toNat (by rw [stringCopyEnd_toNat len hlen]; change 128 ≤ _; omega),
    stringCopyEnd_toNat len hlen, stringCopySize_toNat len hlen]
  change 160 + 32 * stringWordCount len - 128 = 32 + 32 * stringWordCount len
  omega

end Benchmarks.Morpho.MetaMorphoV1_1
