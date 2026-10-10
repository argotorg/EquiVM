import Benchmarks.UniswapV4PoolManager.PoolSwapFeeWords
import Benchmarks.UniswapV4PoolManager.SimpleMulDivTrace
import Benchmarks.UniswapV4PoolManager.RuntimeBlocks_056

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Benchmarks.UniswapV4PoolManager.Immutables
namespace Benchmarks.UniswapV4PoolManager
set_option maxRecDepth 5000

def poolSwapGrowthMemory (mem : ByteArray) (step : UInt256) (s : PoolSwapStepWords) (liquidity : UInt256) : ByteArray :=
  if liquidity = ⟨0⟩ then mem
  else (poolSwapGrowthStep s liquidity).feeGrowthGlobal.toByteArray.write 0 mem (step+UInt256.ofNat 224).toNat 32

def poolSwapGrowthAW (aw step state liquidity : UInt256) : UInt256 :=
  if liquidity = ⟨0⟩ then M aw (state+UInt256.ofNat 64) ⟨32⟩
  else M (M (M aw (state+UInt256.ofNat 64) ⟨32⟩) (step+UInt256.ofNat 192) ⟨32⟩) (step+UInt256.ofNat 224) ⟨32⟩

theorem poolSwapGrowthTrace {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem rdata : ByteArray} {s : PoolSwapStepWords}
    {aw step state liquidity tag x1 params remaining calculated fee protocol amount dir pool : UInt256}
    {σ : AccountMap} {k C : Nat} {R : List UInt256}
    (v : PoolManagerImmutables) (hstack : R.length+15 ≤ 1024) (hlc : liquidity.toNat < 2^128)
    (hl : memLoad (state+UInt256.ofNat 64) mem = liquidity)
    (hf : memLoad (step+UInt256.ofNat 192) mem = s.feeAmount)
    (hg : memLoad (step+UInt256.ofNat 224) mem = s.feeGrowthGlobal)
    (h : RD (deployedRuntime v) I g s0 ⟨19804⟩
      ([tag, x1, params, remaining, calculated, fee, protocol, amount, dir, step, pool, state] ++ R) mem aw rdata σ k C) :
    ∃ k' C', C ≤ C' ∧ RD (deployedRuntime v) I g s0 ⟨19833⟩
      ([⟨0⟩, tag, x1, params, remaining, calculated, fee, protocol, amount, dir, step, pool, state] ++ R)
      (poolSwapGrowthMemory mem step s liquidity) (poolSwapGrowthAW aw step state liquidity) rdata σ k' C' := by
  have hm : UInt256.land liquidity (UInt256.ofNat 340282366920938463463374607431768211455) = liquidity :=
    u256LandMaskCleanOfToNat _ _ rfl hlc
  by_cases hz : liquidity = ⟨0⟩
  · have rd := poolManagerBlocks.poolManager_block_19804_fallthrough hstack (by rw [hl, hm, hz]; rfl) h
    simp only [poolManagerBlocks.poolManager_block_19804_fallthrough_stack, hl, hm] at rd
    rw [hz] at rd
    simp only [poolSwapGrowthMemory, poolSwapGrowthAW, if_pos hz]
    exact ⟨_, _, by omega, rd⟩
  · have rd := poolManagerBlocks.poolManager_block_19804_taken hstack (by rwa [hl, hm])
      (by rw [poolManagerPatchedValidJumpsRuntime v]; jump_dest) h
    simp only [poolManagerBlocks.poolManager_block_19804_taken_stack, hl, hm] at rd
    obtain ⟨k', C', hC, rd'⟩ := simpleMulDivFeeGrowthTrace v (by change R.length+2+13 ≤ 1024; omega) hf hg rd
    exact ⟨k', C', by omega, by simpa only [poolSwapGrowthMemory, poolSwapGrowthAW, poolSwapGrowthStep, if_neg hz] using rd'⟩

end Benchmarks.UniswapV4PoolManager
