import Benchmarks.UniswapV4PoolManager.Values

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.UniswapV4PoolManager

-- LIBRARY CANDIDATE: normalize EVM truth tests to their boolean word.
theorem wordNonzeroBool (word : UInt256) : UInt256.isZero (UInt256.isZero word) =
    (decide (word ≠ ⟨0⟩)).toUInt256 := by
  by_cases hz : word = ⟨0⟩
  · subst word; decide
  · simp only [decide_eq_true hz, isZero_eq_zero_of_ne hz]
    rfl

-- LIBRARY CANDIDATE: a word is positive exactly when it is nonzero.
theorem wordPositive_iff (w : UInt256) : 0 < w.toNat ↔ w ≠ ⟨0⟩ := by
  constructor
  · intro hp he
    subst w
    exact Nat.not_lt_zero _ hp
  · intro hn
    have hz : w.toNat ≠ 0 := fun he => hn (uint256_toNat_eq_zero he)
    omega

-- LIBRARY CANDIDATE: AND with one preserves canonical Boolean words.
theorem wordBoolAndOne (b : Bool) : UInt256.land (UInt256.fromBool b) ⟨1⟩ = UInt256.fromBool b := by
  cases b <;> rfl

end Benchmarks.UniswapV4PoolManager
