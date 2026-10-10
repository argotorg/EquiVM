import Benchmarks.Morpho.MetaMorphoV1_1.StringAllocation
import Benchmarks.EAS.Attester.WordHelpers

/-! Allocation arithmetic for storage strings at a cursor following earlier allocations. -/

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory
open Benchmarks.Morpho.MetaMorphoV1_1.SourceMemory

namespace Benchmarks.Morpho.MetaMorphoV1_1

def stringCopyEndAt (free : Nat) (len : UInt256) : UInt256 :=
  UInt256.ofNat (free + 32 + 32 * stringWordCount len)

theorem stringCopyEndAt_toNat (free : Nat) (len : UInt256)
    (hfree : free < 2 ^ 64) (hlen : len.toNat < 2 ^ 255) :
    (stringCopyEndAt free len).toNat = free + 32 + 32 * stringWordCount len := by
  apply UInt256.toNat_ofNat_of_lt
  change free + 32 + 32 * ((len.toNat + 31) / 32) < 2 ^ 256
  omega

theorem stringCopyNextCursorAt (free : Nat) (len : UInt256) (hlen : len.toNat < 2 ^ 255) :
    nextCursor (UInt256.ofNat free) (stringCopySize len) = stringCopyEndAt free len := by
  rw [nextCursor, stringRoundedCopySize len hlen]
  change UInt256.ofNat free + UInt256.ofNat (32 + 32 * stringWordCount len) = _
  rw [ofNat_add_words]
  unfold stringCopyEndAt
  congr 1
  omega

theorem stringSourceNextCursorAt (free : Nat) (len : UInt256) (hlen : len.toNat < 2 ^ 255) :
    nextCursor (UInt256.ofNat free) (UInt256.ofNat (len.toNat + 32)) =
      stringCopyEndAt free len := by
  rw [← stringCopyNextCursorAt free len hlen]
  simp only [nextCursor, stringRoundedSourceSize len hlen, stringRoundedCopySize len hlen]

theorem stringAllocationFitsAt (free : Nat) (len : UInt256) (hlen : len.toNat < 2 ^ 255) :
    allocationFits (UInt256.ofNat free) (stringCopySize len) ↔
      allocationFits (UInt256.ofNat free) (UInt256.ofNat (len.toNat + 32)) := by
  simp only [allocationFits, stringCopyNextCursorAt free len hlen,
    stringSourceNextCursorAt free len hlen]

theorem stringCopySize_subAt (free : Nat) (len : UInt256)
    (hfree : free < 2 ^ 64) (hlen : len.toNat < 2 ^ 255) :
    UInt256.sub (stringCopyEndAt free len) (UInt256.ofNat free) = stringCopySize len := by
  have hf : (UInt256.ofNat free).toNat = free :=
    UInt256.toNat_ofNat_of_lt (lt_trans hfree (by decide))
  apply u256_inj
  rw [usub_toNat (by rw [stringCopyEndAt_toNat free len hfree hlen, hf]; omega),
    stringCopyEndAt_toNat free len hfree hlen, hf, stringCopySize_toNat len hlen]
  omega

end Benchmarks.Morpho.MetaMorphoV1_1
