import Benchmarks.UniswapV4PoolManager.PositionGetCostBlock
import Benchmarks.UniswapV4PoolManager.MemoryGas

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.UniswapV4PoolManager

theorem positionGetActiveWords_ge (aw params free : UInt256) :
    aw.toNat ≤ (positionGetActiveWords aw params free).toNat := by
  unfold positionGetActiveWords
  apply Nat.le_trans ?_ (memoryWords_ge_active _ _ _)
  apply Nat.le_trans ?_ (memoryWords_ge_active _ _ _)
  apply Nat.le_trans ?_ (memoryWords_ge_active _ _ _)
  apply Nat.le_trans ?_ (memoryWords_ge_active _ _ _)
  apply Nat.le_trans ?_ (memoryWords_ge_active _ _ _)
  apply Nat.le_trans ?_ (memoryWords_ge_active _ _ _)
  apply Nat.le_trans ?_ (memoryWords_ge_active _ _ _)
  apply Nat.le_trans ?_ (memoryWords_ge_active _ _ _)
  apply Nat.le_trans ?_ (memoryWords_ge_active _ _ _)
  apply Nat.le_trans ?_ (memoryWords_ge_active _ _ _)
  apply Nat.le_trans ?_ (memoryWords_ge_active _ _ _)
  apply Nat.le_trans ?_ (memoryWords_ge_active _ _ _)
  apply Nat.le_trans ?_ (memoryWords_ge_active _ _ _)
  apply Nat.le_trans ?_ (memoryWords_ge_active _ _ _)
  apply Nat.le_trans ?_ (memoryWords_ge_active _ _ _)
  exact Nat.le_refl _

end Benchmarks.UniswapV4PoolManager
