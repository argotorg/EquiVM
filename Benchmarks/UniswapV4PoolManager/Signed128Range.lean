import Benchmarks.UniswapV4PoolManager.Signed128
import Benchmarks.UniswapV4PoolManager.SignedRangeSource
import Benchmarks.UniswapV4PoolManager.SignedComparison

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.UniswapV4PoolManager

-- LIBRARY CANDIDATE: signed casts widen monotonically with the target width.
theorem signedFits_widen {small large : BitWidth} {n : Int} (hw : small.val ≤ large.val)
    (hn : signedFits small n) : signedFits large n := by
  have hp : (2 : Int)^(small.val-1) ≤ (2 : Int)^(large.val-1) :=
    pow_le_pow_right₀ (by decide) (Nat.sub_le_sub_right hw 1)
  exact ⟨le_trans (neg_le_neg hp) hn.1, lt_of_lt_of_le hn.2 hp⟩

theorem signedFits128_int256 {n : Int} (hn : signedFits ⟨128, by decide⟩ n) : int256Fits n :=
  signedFits_widen (large := ⟨256, by decide⟩) (by decide) hn

-- LIBRARY CANDIDATE: the compiler's two comparisons check the complete int128 range.
theorem int128RangeGuard {n : Int} (hn : int256Fits n) :
    UInt256.lor (UInt256.sgt (EVM.wordOfInt n) (UInt256.ofNat (2^127-1)))
      (UInt256.slt (EVM.wordOfInt n) (UInt256.ofNat (2^256-2^127))) =
      UInt256.fromBool (decide (¬signedFits ⟨128, by decide⟩ n)) := by
  rw [sgt_signed, slt_signed, signed_wordOfInt hn]
  have hhi : EVM.signed (UInt256.ofNat (2^127-1)) = (2^127 : Int)-1 := by decide +kernel
  have hlo : EVM.signed (UInt256.ofNat (2^256-2^127)) = -(2^127 : Int) := by decide +kernel
  rw [hhi, hlo]
  have he : (¬signedFits ⟨128, by decide⟩ n) ↔ (2^127 : Int)-1 < n ∨ n < -(2^127 : Int) := by
    unfold signedFits
    norm_num only
    omega
  simp only [he]
  by_cases hh : (2^127 : Int)-1 < n <;> by_cases hl : n < -(2^127 : Int) <;>
    simp only [hh, hl, decide_true, decide_false, or_self, or_true, or_false, true_or, false_or] <;> decide +kernel

end Benchmarks.UniswapV4PoolManager
