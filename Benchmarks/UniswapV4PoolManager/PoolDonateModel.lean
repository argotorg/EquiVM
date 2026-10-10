import Benchmarks.UniswapV4PoolManager.PoolSwapFinishStorage
import Benchmarks.UniswapV4PoolManager.SimpleMulDivWords
import Benchmarks.UniswapV4PoolManager.BalanceDeltaSource

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.UniswapV4PoolManager

abbrev poolDonateFunction : FunctionDecl := contract.functions[21]!

def poolDonateDelta (amount0 amount1 : UInt256) : UInt256 :=
  balanceDeltaWord (UInt256.sub ⟨0⟩ amount0) (UInt256.sub ⟨0⟩ amount1)

def poolDonateGrowth (amount liquidity : UInt256) : UInt256 :=
  simpleMulDiv amount (UInt256.ofNat (2^128)) liquidity

def poolDonateStep (evm : State) (id : UInt256) (second : Bool) (amount liquidity : UInt256) : State :=
  if amount = ⟨0⟩ then evm else
    Solm.EVM.storageStore evm evm.executionEnv.codeOwner (poolFeeGrowthSlot id second)
      (poolFeeGrowthWord evm id second + poolDonateGrowth amount liquidity)

def poolDonatePost (evm : State) (id amount0 amount1 : UInt256) : State :=
  poolDonateStep (poolDonateStep evm id false amount0 (poolLiquidityWord evm id))
    id true amount1 (poolLiquidityWord evm id)

theorem poolDonateStep_executionEnv (evm : State) (id : UInt256) (second : Bool) (amount liquidity : UInt256) :
    (poolDonateStep evm id second amount liquidity).executionEnv = evm.executionEnv := by
  unfold poolDonateStep
  split
  · rfl
  · exact storageStore_executionEnv ..

theorem poolDonateStep_σ₀ (evm : State) (id : UInt256) (second : Bool) (amount liquidity : UInt256) :
    (poolDonateStep evm id second amount liquidity).σ₀ = evm.σ₀ := by
  unfold poolDonateStep
  split
  · rfl
  · exact storageStore_σ₀ ..

theorem poolDonatePost_executionEnv (evm : State) (id amount0 amount1 : UInt256) :
    (poolDonatePost evm id amount0 amount1).executionEnv = evm.executionEnv := by
  rw [poolDonatePost, poolDonateStep_executionEnv, poolDonateStep_executionEnv]

theorem poolDonatePost_σ₀ (evm : State) (id amount0 amount1 : UInt256) :
    (poolDonatePost evm id amount0 amount1).σ₀ = evm.σ₀ := by
  rw [poolDonatePost, poolDonateStep_σ₀, poolDonateStep_σ₀]

theorem poolDonateGrowth_compiled (amount liquidity : UInt256) :
    poolDonateGrowth amount liquidity = UInt256.div (UInt256.shiftLeft amount (UInt256.ofNat 128)) liquidity :=
  simpleMulDiv_pow2 _ _ (by decide)

end Benchmarks.UniswapV4PoolManager
