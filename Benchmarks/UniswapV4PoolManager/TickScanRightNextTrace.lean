import Benchmarks.UniswapV4PoolManager.TickScanWords
import Benchmarks.UniswapV4PoolManager.LeastSignificantBitTrace
import Benchmarks.UniswapV4PoolManager.RuntimeBlocks_062

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables
open Benchmarks.UniswapV4PoolManager.Immutables
namespace Benchmarks.UniswapV4PoolManager
set_option maxRecDepth 5000

/-- The repeated caller words are the copies made by block 19169 before the scan. -/
theorem tickScanRightNextTrace {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem rdata : ByteArray} {aw masked compressed spacing initialized step state fee direction pool
      x0 x1 params x3 x4 x6 x7 : UInt256} {σ : AccountMap} {k C : Nat} {R : List UInt256}
    (v : PoolManagerImmutables) (hstack : R.length+31 ≤ 1024)
    (h : RD (deployedRuntime v) I g s0 (if masked = ⟨0⟩ then ⟨21441⟩ else ⟨21205⟩)
      ([step, state, fee, direction, UInt256.isZero masked, masked, spacing, compressed, initialized,
        x0, x1, params, x3, x4, fee, x6, x7, direction, step, pool, state] ++ R) mem aw rdata σ k C) :
    ∃ k' C', C ≤ C' ∧ RD (deployedRuntime v) I g s0 ⟨19401⟩
      ([initialized, tickScanResultWord compressed spacing masked false, UInt256.ofNat (2^256-887272),
        step, UInt256.ofNat 96, UInt256.ofNat 1, UInt256.ofNat 64, UInt256.ofNat (2^128-1),
        state, fee, direction, x0, x1, params, x3, x4, fee, x6, x7, direction, step, pool, state] ++ R)
      mem aw rdata σ k' C' := by
  by_cases hz : masked = ⟨0⟩
  · rw [if_pos hz] at h
    have rd1 := poolManagerBlocks.poolManager_block_21441 (by simp; omega)
      (by rw [poolManagerPatchedValidJumpsRuntime v]; jump_dest) h
    simp only [poolManagerBlocks.poolManager_block_21441_stack] at rd1
    rw [u256_land_comm (UInt256.ofNat 255) compressed] at rd1
    have rd2 := poolManagerBlocks.poolManager_block_21435 (by simp; omega)
      (by rw [poolManagerPatchedValidJumpsRuntime v]; jump_dest) rd1
    simp only [poolManagerBlocks.poolManager_block_21435_stack] at rd2
    refine ⟨k+37+4, C+122+15, by omega, ?_⟩
    simpa only [tickScanResultWord, if_pos hz, tickScanNextWord, tickScanDefaultDistance,
      tickPositionBit, Bool.false_eq_true, if_false] using rd2
  · rw [if_neg hz] at h
    have rd1 := poolManagerBlocks.poolManager_block_21205_fallthrough (by simp; omega)
      (isZero_eq_zero_of_ne hz) h
    simp only [poolManagerBlocks.poolManager_block_21205_fallthrough_stack] at rd1
    have rd2 := leastSignificantBitNextTrace v hstack hz rd1
    rw [u256_land_comm (⟨255⟩ : UInt256) compressed] at rd2
    have rd3 := poolManagerBlocks.poolManager_block_21435 (by simp; omega)
      (by rw [poolManagerPatchedValidJumpsRuntime v]; jump_dest) rd2
    simp only [poolManagerBlocks.poolManager_block_21435_stack] at rd3
    refine ⟨k+6+61+4, C+21+196+15, by omega, ?_⟩
    simpa only [tickScanResultWord, if_neg hz, tickScanNextWord, tickScanDistance, tickScanIndex,
      tickPositionBit, Bool.false_eq_true, if_false] using rd3

end Benchmarks.UniswapV4PoolManager
