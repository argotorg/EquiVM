import Benchmarks.UniswapV4PoolManager.TickScanWords
import Benchmarks.UniswapV4PoolManager.MostSignificantBitTrace
import Benchmarks.UniswapV4PoolManager.RuntimeBlocks_054
import Benchmarks.UniswapV4PoolManager.RuntimeBlocks_061

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables
open Benchmarks.UniswapV4PoolManager.Immutables
namespace Benchmarks.UniswapV4PoolManager
set_option maxRecDepth 5000

theorem tickScanLeftNextTrace {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem rdata : ByteArray} {aw masked compressed spacing initialized : UInt256}
    {σ : AccountMap} {k C : Nat} {R : List UInt256}
    (v : PoolManagerImmutables) (hstack : R.length+12 ≤ 1024)
    (h : RD (deployedRuntime v) I g s0 (if masked = ⟨0⟩ then ⟨21091⟩ else ⟨19372⟩)
      ([masked, tickPositionBit compressed, compressed, spacing, initialized] ++ R) mem aw rdata σ k C) :
    ∃ k' C', C ≤ C' ∧ RD (deployedRuntime v) I g s0 ⟨19401⟩
      (initialized :: tickScanResultWord compressed spacing masked true :: R) mem aw rdata σ k' C' := by
  by_cases hz : masked = ⟨0⟩
  · rw [if_pos hz] at h
    have rd1 := poolManagerBlocks.poolManager_block_21091 (by simp; omega)
      (by rw [poolManagerPatchedValidJumpsRuntime v]; jump_dest) h
    simp only [poolManagerBlocks.poolManager_block_21091_stack] at rd1
    have rd2 := poolManagerBlocks.poolManager_block_19399 (by simp; omega) rd1
    simp only [poolManagerBlocks.poolManager_block_19399_stack] at rd2
    refine ⟨k+13+2, C+49+4, by omega, ?_⟩
    simpa only [tickScanResultWord, if_pos hz, tickScanDefaultDistance, if_true, tickScanNextWord] using rd2
  · rw [if_neg hz] at h
    have rd1 := poolManagerBlocks.poolManager_block_19372 (by simp; omega)
      (by rw [poolManagerPatchedValidJumpsRuntime v]; jump_dest) h
    simp only [poolManagerBlocks.poolManager_block_19372_stack] at rd1
    rcases mostSignificantBitTrace v (by simp; omega)
      (by rw [poolManagerPatchedValidJumps v]; jump_dest) rd1 with ⟨hzero, _⟩ | ⟨_, rd2⟩
    · exact False.elim (hz hzero)
    · have rd3 := poolManagerBlocks.poolManager_block_19383 (by simp; omega) rd2
      simp only [poolManagerBlocks.poolManager_block_19383_stack] at rd3
      have rd4 := poolManagerBlocks.poolManager_block_19399 (by simp; omega) rd3
      simp only [poolManagerBlocks.poolManager_block_19399_stack] at rd4
      refine ⟨k+6+54+13+2, C+23+172+45+4, by omega, ?_⟩
      simpa only [tickScanResultWord, if_neg hz, tickScanDistance, tickScanIndex, if_true, tickScanNextWord] using rd4

end Benchmarks.UniswapV4PoolManager
