import Benchmarks.UniswapV4PoolManager.PoolUpdateTickFinishSource

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.UniswapV4PoolManager

theorem tickFeesPost_env (evm : EVM.State) (id packed : UInt256) (tick : Int) :
    (tickFeesPost evm id packed tick).executionEnv = evm.executionEnv := by
  unfold tickFeesPost
  split
  · simp only [tickFeeWrites, tickFeeWrite0, storageStore_executionEnv]
  · rfl

theorem tickLiquidityStore_env (evm : EVM.State) (id : UInt256) (tick : Int) (gross : UInt256) (net : Int) :
    (tickLiquidityStore evm id tick gross net).executionEnv = evm.executionEnv := by
  rw [tickLiquidityStore, storageStore_executionEnv]

theorem tickFeesPost_σ₀ (evm : EVM.State) (id packed : UInt256) (tick : Int) :
    (tickFeesPost evm id packed tick).σ₀ = evm.σ₀ := by
  unfold tickFeesPost
  split
  · simp only [tickFeeWrites, tickFeeWrite0, storageStore_σ₀]
  · rfl

theorem tickLiquidityStore_σ₀ (evm : EVM.State) (id : UInt256) (tick : Int) (gross : UInt256) (net : Int) :
    (tickLiquidityStore evm id tick gross net).σ₀ = evm.σ₀ := by
  rw [tickLiquidityStore, storageStore_σ₀]

theorem tickLiquidityStore_accounts {evm : EVM.State} {I : ExecutionEnv} (hI : evm.executionEnv = I)
    (id : UInt256) (tick : Int) (gross : UInt256) (net : Int) :
    (tickLiquidityStore evm id tick gross net).accountMap = sstoreAccountMap I.codeOwner evm.accountMap
      (tickSlot id tick) (tickLiquidityPacked gross (EVM.wordOfInt net)) := by
  rw [tickLiquidityStore, storageStore_accountMap, hI]

end Benchmarks.UniswapV4PoolManager
