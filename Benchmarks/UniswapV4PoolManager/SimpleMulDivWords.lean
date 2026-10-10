import Benchmarks.UniswapV4PoolManager.WordPow2

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.UniswapV4PoolManager

def simpleMulDiv (a b denominator : UInt256) : UInt256 := UInt256.div (UInt256.mul a b) denominator

theorem simpleMulDiv_zero (a b : UInt256) : simpleMulDiv a b ⟨0⟩ = ⟨0⟩ := by
  apply u256_inj
  rw [simpleMulDiv, udiv_toNat]
  exact Nat.div_zero _

theorem simpleMulDiv_pow2 (a denominator : UInt256) {n : Nat} (hn : n < 256) :
    simpleMulDiv a (UInt256.ofNat (2^n)) denominator =
      UInt256.div (UInt256.shiftLeft a (UInt256.ofNat n)) denominator := by
  rw [simpleMulDiv, wordMulPow2 a hn]

end Benchmarks.UniswapV4PoolManager
