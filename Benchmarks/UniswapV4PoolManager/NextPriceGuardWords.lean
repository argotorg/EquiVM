import Benchmarks.UniswapV4PoolManager.NextPriceWords

open Ethereum Ethereum.EVM Reasoning.Theory
namespace Benchmarks.UniswapV4PoolManager

theorem nextPriceValid_test {price liquidity : UInt256} (h : nextPriceValid price liquidity) :
    UInt256.lor (UInt256.isZero price) (UInt256.isZero liquidity) = ⟨0⟩ := by
  rw [isZero_eq_zero_of_ne h.1, isZero_eq_zero_of_ne h.2]
  rfl

theorem nextPriceInvalid_test {price liquidity : UInt256} (h : ¬nextPriceValid price liquidity) :
    UInt256.lor (UInt256.isZero price) (UInt256.isZero liquidity) ≠ ⟨0⟩ := by
  intro he
  apply h
  constructor
  · intro hz
    have hh := u256_lor_eq_zero_left he
    rw [hz] at hh
    exact (by decide : UInt256.isZero ⟨0⟩ ≠ ⟨0⟩) hh
  · intro hz
    have hh := u256_lor_eq_zero_right he
    rw [hz] at hh
    exact (by decide : UInt256.isZero ⟨0⟩ ≠ ⟨0⟩) hh

end Benchmarks.UniswapV4PoolManager
