import Benchmarks.UniswapV4PoolManager.SwapStepRemainingWords
import Benchmarks.UniswapV4PoolManager.FullMathPPMResultTrace
import Benchmarks.UniswapV4PoolManager.RuntimeBlocks_055
import Benchmarks.UniswapV4PoolManager.RuntimeBlocks_059

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables
open Benchmarks.UniswapV4PoolManager.Immutables
namespace Benchmarks.UniswapV4PoolManager
set_option maxRecDepth 5000

theorem swapStepAvailableTrace {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem rdata : ByteArray} {aw price j dir target fee liquidity remaining : UInt256}
    {σ : AccountMap} {k C : Nat} {R : List UInt256}
    (v : PoolManagerImmutables) (hstack : R.length+17 ≤ 1024) (hf : fee.toNat < 2^24)
    (h : RD (deployedRuntime v) I g s0 ⟨19593⟩
      ([price, j, dir, target, fee, liquidity, remaining] ++ R) mem aw rdata σ k C) :
    (swapStepAvailableFits remaining fee → ∃ k' C', C ≤ C' ∧
      RD (deployedRuntime v) I g s0 ⟨19615⟩
        ([swapStepAvailableWord remaining fee, swapStepFeeComplement fee,
          price, j, dir, target, fee, liquidity, remaining] ++ R) mem aw rdata σ k' C') ∧
    (¬swapStepAvailableFits remaining fee → RDrev (deployedRuntime v) g s0) := by
  have hclean := u256LandMaskCleanOfToNat fee (UInt256.ofNat 16777215) rfl hf
  have rd1 := poolManagerBlocks.poolManager_block_19593 (by change R.length+12 ≤ 1024; omega)
    (by rw [poolManagerPatchedValidJumpsRuntime v]; jump_dest) h
  simp only [poolManagerBlocks.poolManager_block_19593_stack, hclean] at rd1
  have hr := fullMathPPMResultTrace (a := swapStepRemainingWord remaining) (b := swapStepFeeComplement fee)
    v (by change R.length+17 ≤ 1024; exact hstack) (by rw [deployedRuntime_jumps]; jump_dest) rd1
  constructor
  · intro hfit
    obtain ⟨k2, C2, hC2, rd2⟩ := hr.1 hfit
    exact ⟨k2, C2, by omega, rd2⟩
  · intro hfit
    exact hr.2 hfit

theorem swapStepRemainingFeeTrace {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem rdata : ByteArray} {aw next liquidity price j0 j1 dir amount mask remaining : UInt256}
    {σ : AccountMap} {k C : Nat} {R : List UInt256}
    (v : PoolManagerImmutables) (hstack : R.length+12 ≤ 1024)
    (h : RD (deployedRuntime v) I g s0 ⟨20464⟩
      ([next, liquidity, price, j0, j1, dir, amount, amount, mask, remaining] ++ R) mem aw rdata σ k C) :
    ∃ k' C', C ≤ C' ∧ RD (deployedRuntime v) I g s0 ⟨19697⟩
      ([dir, next, liquidity, price, j0, j1, swapStepRemainingFeeWord remaining amount,
        amount, next, mask, remaining] ++ R) mem aw rdata σ k' C' := by
  have rd1 := poolManagerBlocks.poolManager_block_20464 hstack
    (by rw [poolManagerPatchedValidJumpsRuntime v]; jump_dest) h
  simp only [poolManagerBlocks.poolManager_block_20464_stack] at rd1
  rw [swapStepRemainingFeeWord_eq]
  exact ⟨_, _, by omega, rd1⟩

end Benchmarks.UniswapV4PoolManager
