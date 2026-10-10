import Benchmarks.UniswapV4PoolManager.TickScanStorageTrace
import Benchmarks.UniswapV4PoolManager.WordBoolean
import Benchmarks.UniswapV4PoolManager.ReachCost
import Benchmarks.UniswapV4PoolManager.Routines
import Benchmarks.UniswapV4PoolManager.RuntimeBlocks_061

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables
open Benchmarks.UniswapV4PoolManager.Immutables
namespace Benchmarks.UniswapV4PoolManager
set_option maxRecDepth 5000

theorem tickScanRightReadTrace {I : ExecutionEnv} {g : Sat256} {s0 evm : State}
    {mem rdata : ByteArray} {aw id compressed spacing step x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 : UInt256}
    {k C : Nat} {R : List UInt256}
    (v : PoolManagerImmutables) (hstack : R.length+20 ≤ 1024) (hI : evm.executionEnv = I)
    (h : RD (deployedRuntime v) I g s0 ⟨21109⟩
      ([compressed, spacing, poolSlot id, step, x4, x5, x6, x7, x8, x9, x10, x11, x12, x13, x14, x15] ++ R)
      mem aw rdata evm.accountMap k C) :
    ∃ k' C', C ≤ C' ∧ RD (deployedRuntime v) I g s0
      (if tickScanMasked evm id (compressed+UInt256.ofNat 1) false = ⟨0⟩ then ⟨21441⟩ else ⟨21205⟩)
      ([step, x4, x12, x15, UInt256.isZero (tickScanMasked evm id (compressed+UInt256.ofNat 1) false),
        tickScanMasked evm id (compressed+UInt256.ofNat 1) false, spacing, compressed+UInt256.ofNat 1,
        (decide (tickScanMasked evm id (compressed+UInt256.ofNat 1) false ≠ ⟨0⟩)).toUInt256,
        x7, x8, x9, x10, x11, x12, x13, x14, x15] ++ R)
      (tickScanMemory mem id (compressed+UInt256.ofNat 1))
      (M (M (M aw ⟨0⟩ ⟨32⟩) (UInt256.ofNat 32) ⟨32⟩) ⟨0⟩ (UInt256.ofNat 64))
      rdata evm.accountMap k' C' := by
  have hload := tickScanStorageLoad_compiled hI mem id (compressed+UInt256.ofNat 1)
  have hmask := tickScanMask_compiled_right (tickPositionBit (compressed+UInt256.ofNat 1))
  change UInt256.lnot (UInt256.shiftLeft (UInt256.ofNat 1)
    (UInt256.land (compressed+UInt256.ofNat 1) (UInt256.ofNat 255)) +
    UInt256.ofNat 0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff) = _ at hmask
  apply RD_retainCost ?_ h
  intro budget start rd
  by_cases hz : tickScanMasked evm id (compressed+UInt256.ofNat 1) false = ⟨0⟩
  · rw [if_pos hz]
    have hcond : UInt256.eq ⟨0⟩ (UInt256.isZero (UInt256.isZero
        (tickScanMasked evm id (compressed+UInt256.ofNat 1) false))) ≠ UInt256.ofNat 0 := by rw [hz]; decide
    obtain ⟨k1, C1, rd1⟩ := poolManagerBlocks.poolManager_block_21109_taken hstack
      (by rw [hload, hmask]; exact hcond)
      (by rw [poolManagerPatchedValidJumpsRuntime v]; jump_dest) rd
    refine ⟨k1, C1, ?_⟩
    simp only [poolManagerBlocks.poolManager_block_21109_taken_stack,
      poolManagerBlocks.poolManager_block_21109_taken_memory, hload, hmask] at rd1
    change RD (deployedRuntime v) I budget start ⟨21441⟩
      ([step, x4, x12, x15, UInt256.isZero (tickScanMasked evm id (compressed+UInt256.ofNat 1) false),
        tickScanMasked evm id (compressed+UInt256.ofNat 1) false, spacing, compressed+UInt256.ofNat 1,
        UInt256.isZero (UInt256.isZero (tickScanMasked evm id (compressed+UInt256.ofNat 1) false)),
        x7, x8, x9, x10, x11, x12, x13, x14, x15] ++ R) _ _ _ _ _ _ at rd1
    rw [wordNonzeroBool] at rd1
    exact rd1
  · rw [if_neg hz]
    have hcond : UInt256.eq ⟨0⟩ (UInt256.isZero (UInt256.isZero
        (tickScanMasked evm id (compressed+UInt256.ofNat 1) false))) = UInt256.ofNat 0 := by
      rw [isZero_eq_zero_of_ne hz]; rfl
    obtain ⟨k1, C1, rd1⟩ := poolManagerBlocks.poolManager_block_21109_fallthrough hstack
      (by rw [hload, hmask]; exact hcond) rd
    refine ⟨k1, C1, ?_⟩
    simp only [poolManagerBlocks.poolManager_block_21109_fallthrough_stack,
      poolManagerBlocks.poolManager_block_21109_fallthrough_memory, hload, hmask] at rd1
    change RD (deployedRuntime v) I budget start ⟨21205⟩
      ([step, x4, x12, x15, UInt256.isZero (tickScanMasked evm id (compressed+UInt256.ofNat 1) false),
        tickScanMasked evm id (compressed+UInt256.ofNat 1) false, spacing, compressed+UInt256.ofNat 1,
        UInt256.isZero (UInt256.isZero (tickScanMasked evm id (compressed+UInt256.ofNat 1) false)),
        x7, x8, x9, x10, x11, x12, x13, x14, x15] ++ R) _ _ _ _ _ _ at rd1
    rw [wordNonzeroBool] at rd1
    exact rd1

end Benchmarks.UniswapV4PoolManager
