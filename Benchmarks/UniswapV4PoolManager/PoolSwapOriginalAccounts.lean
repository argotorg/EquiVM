import Benchmarks.UniswapV4PoolManager.PoolSwapIterationSource
import Benchmarks.UniswapV4PoolManager.PoolSwapFinishStorage

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.UniswapV4PoolManager

theorem poolSwapCrossPost_σ₀ (evm : State) (id : UInt256) (s : PoolSwapStepWords) (z : Bool) :
    (poolSwapCrossPost evm id s z).σ₀ = evm.σ₀ := by
  simp only [poolSwapCrossPost, tickCrossPost, tickCrossWrite0, storageStore_σ₀]

theorem poolSwapTickResult_σ₀ {f ff : Frame} {evm post : State} {id : UInt256}
    {s : PoolSwapStepWords} {r : PoolSwapResultWords} {z : Bool}
    (h : poolSwapTickResult f evm id s r z = .ok ff post) : post.σ₀ = evm.σ₀ := by
  unfold poolSwapTickResult at h
  split at h
  · split at h
    · split at h
      · cases h
      · split at h
        · cases h
          exact poolSwapCrossPost_σ₀ ..
        · cases h
    · cases h; rfl
  · unfold poolSwapRepriceResult at h
    split at h
    · cases h; rfl
    · split at h
      · cases h
      · cases h; rfl

theorem poolSwapIterationResult_σ₀ {f ff : Frame} {evm post : State} {id : UInt256}
    {s : PoolSwapStepWords} {r : PoolSwapResultWords} {p : PoolSwapParamsWords}
    {remaining calculated fee protocol amount : UInt256}
    (h : poolSwapIterationResult f evm id s r p remaining calculated fee protocol amount = .ok ff post) :
    post.σ₀ = evm.σ₀ := by
  unfold poolSwapIterationResult at h
  dsimp only at h
  split at h
  · unfold poolSwapAccountingResult at h
    split at h
    · exact poolSwapTickResult_σ₀ h
    · cases h
  · cases h

theorem poolSwapFinishPost_σ₀ (evm : State) (id packed : UInt256) (s : PoolSwapStepWords)
    (r : PoolSwapResultWords) (z : Bool) : (poolSwapFinishPost evm id packed s r z).σ₀ = evm.σ₀ := by
  unfold poolSwapFinishPost poolSwapGrowthPost
  rw [storageStore_σ₀]
  unfold poolSwapLiquidityPost
  split <;> simp only [poolLiquidityStore, poolSwapSlot0Post, storageStore_σ₀]

end Benchmarks.UniswapV4PoolManager
