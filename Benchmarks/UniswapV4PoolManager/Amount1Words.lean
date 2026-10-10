import Benchmarks.UniswapV4PoolManager.AbsDiffWords
import Benchmarks.UniswapV4PoolManager.FullMath96Words
import Benchmarks.UniswapV4PoolManager.WordBoolean

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.UniswapV4PoolManager

abbrev amount1Fits (a b liquidity : UInt256) : Prop := fullMathFits liquidity (absDiffWord a b) fullMathQ96
instance (a b liquidity : UInt256) : Decidable (amount1Fits a b liquidity) :=
  inferInstanceAs (Decidable (fullMathFits _ _ _))
def amount1Word (a b liquidity : UInt256) (roundUp : Bool) : UInt256 :=
  fullMathWord liquidity (absDiffWord a b) fullMathQ96 +
    UInt256.fromBool (roundUp && decide (0 < (fullMathRemainder liquidity (absDiffWord a b) fullMathQ96).toNat))

theorem amount1Word_down (a b liquidity : UInt256) :
    amount1Word a b liquidity false = fullMathWord liquidity (absDiffWord a b) fullMathQ96 := by
  simp only [amount1Word, Bool.false_and]
  exact u256_add_zero _

theorem amount1Word_up (a b liquidity : UInt256) : amount1Word a b liquidity true =
    UInt256.land (UInt256.isZero (UInt256.isZero (UInt256.mulMod liquidity (absDiffWord a b) fullMathQ96))) ⟨1⟩ +
      fullMathWord liquidity (absDiffWord a b) fullMathQ96 := by
  rw [wordNonzeroBool]
  change _ = UInt256.land (UInt256.fromBool (decide (fullMathRemainder liquidity (absDiffWord a b) fullMathQ96 ≠ ⟨0⟩))) ⟨1⟩ + _
  rw [wordBoolAndOne]
  simp only [amount1Word, Bool.true_and, wordPositive_iff]
  exact u256_add_comm _ _

end Benchmarks.UniswapV4PoolManager
