import Benchmarks.UniswapV4PoolManager.TickScanStorageTrace
import Benchmarks.UniswapV4PoolManager.WordBoolean
import Benchmarks.UniswapV4PoolManager.ReachCost
import Benchmarks.UniswapV4PoolManager.Routines
import Benchmarks.UniswapV4PoolManager.RuntimeBlocks_054

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables
open Benchmarks.UniswapV4PoolManager.Immutables
namespace Benchmarks.UniswapV4PoolManager
set_option maxRecDepth 5000

theorem tickScanLeftReadTrace {I : ExecutionEnv} {g : Sat256} {s0 evm : State}
    {mem rdata : ByteArray} {aw id compressed spacing step : UInt256} {k C : Nat} {R : List UInt256}
    (v : PoolManagerImmutables) (hstack : R.length+13 ≤ 1024) (hI : evm.executionEnv = I)
    (h : RD (deployedRuntime v) I g s0 ⟨19234⟩ (compressed :: spacing :: poolSlot id :: step :: R)
      mem aw rdata evm.accountMap k C) :
    ∃ k' C', C ≤ C' ∧ RD (deployedRuntime v) I g s0
      (if tickScanMasked evm id compressed true = ⟨0⟩ then ⟨21091⟩ else ⟨19372⟩)
      ([tickScanMasked evm id compressed true, tickPositionBit compressed, compressed, spacing,
        (decide (tickScanMasked evm id compressed true ≠ ⟨0⟩)).toUInt256,
        UInt256.ofNat (2^256-887272), step, UInt256.ofNat 96, UInt256.ofNat 1, UInt256.ofNat 64,
        UInt256.ofNat (2^128-1)] ++ R)
      (tickScanMemory mem id compressed)
      (M (M (M aw ⟨0⟩ ⟨32⟩) (UInt256.ofNat 32) ⟨32⟩) ⟨0⟩ (UInt256.ofNat 64))
      rdata evm.accountMap k' C' := by
  have hload := tickScanStorageLoad_compiled hI mem id compressed
  have hmask := tickScanMask_compiled_left (tickPositionBit compressed)
  change UInt256.shiftRight (UInt256.ofNat 0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff)
    (UInt256.sub (UInt256.ofNat 255) (UInt256.land compressed (UInt256.ofNat 255))) = _ at hmask
  apply RD_retainCost ?_ h
  intro budget start rd
  by_cases hz : tickScanMasked evm id compressed true = ⟨0⟩
  · rw [if_pos hz]
    have hcond : UInt256.eq ⟨0⟩ (UInt256.isZero (UInt256.isZero (tickScanMasked evm id compressed true))) ≠
        UInt256.ofNat 0 := by rw [hz]; decide
    obtain ⟨k1, C1, rd1⟩ := poolManagerBlocks.poolManager_block_19234_taken hstack
      (by rw [hload, hmask]; exact hcond)
      (by rw [poolManagerPatchedValidJumpsRuntime v]; jump_dest) rd
    refine ⟨k1, C1, ?_⟩
    simp only [poolManagerBlocks.poolManager_block_19234_taken_stack,
      poolManagerBlocks.poolManager_block_19234_taken_memory, hload, hmask] at rd1
    change RD (deployedRuntime v) I budget start ⟨21091⟩
      ([tickScanMasked evm id compressed true, tickPositionBit compressed, compressed, spacing,
        UInt256.isZero (UInt256.isZero (tickScanMasked evm id compressed true)),
        UInt256.ofNat (2^256-887272), step, UInt256.ofNat 96, UInt256.ofNat 1, UInt256.ofNat 64,
        UInt256.ofNat (2^128-1)] ++ R) _ _ _ _ _ _ at rd1
    rw [wordNonzeroBool] at rd1
    exact rd1
  · rw [if_neg hz]
    have hcond : UInt256.eq ⟨0⟩ (UInt256.isZero (UInt256.isZero (tickScanMasked evm id compressed true))) =
        UInt256.ofNat 0 := by rw [isZero_eq_zero_of_ne hz]; rfl
    obtain ⟨k1, C1, rd1⟩ := poolManagerBlocks.poolManager_block_19234_fallthrough hstack
      (by rw [hload, hmask]; exact hcond) rd
    refine ⟨k1, C1, ?_⟩
    simp only [poolManagerBlocks.poolManager_block_19234_fallthrough_stack,
      poolManagerBlocks.poolManager_block_19234_fallthrough_memory, hload, hmask] at rd1
    change RD (deployedRuntime v) I budget start ⟨19372⟩
      ([tickScanMasked evm id compressed true, tickPositionBit compressed, compressed, spacing,
        UInt256.isZero (UInt256.isZero (tickScanMasked evm id compressed true)),
        UInt256.ofNat (2^256-887272), step, UInt256.ofNat 96, UInt256.ofNat 1, UInt256.ofNat 64,
        UInt256.ofNat (2^128-1)] ++ R) _ _ _ _ _ _ at rd1
    rw [wordNonzeroBool] at rd1
    exact rd1

end Benchmarks.UniswapV4PoolManager
