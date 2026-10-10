import Benchmarks.UniswapV4PoolManager.BalanceDeltaSource

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.UniswapV4PoolManager

theorem balanceDeltaWord_zero_right (a : UInt256) :
    balanceDeltaWord a ⟨0⟩ = UInt256.shiftLeft a (UInt256.ofNat 128) := by
  rw [balanceDeltaWord, u256_land_zero_right, u256_lor_zero]

theorem balanceDeltaWord_zero_left (b : UInt256) :
    balanceDeltaWord ⟨0⟩ b = UInt256.land (UInt256.ofNat (2^128-1)) b := by
  rw [balanceDeltaWord, show UInt256.shiftLeft (⟨0⟩ : UInt256) (UInt256.ofNat 128) = ⟨0⟩ by decide,
    uint256_lor_zero_left]

end Benchmarks.UniswapV4PoolManager
