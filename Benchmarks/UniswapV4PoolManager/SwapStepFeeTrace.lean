import Benchmarks.UniswapV4PoolManager.SwapStepFeeWords
import Benchmarks.UniswapV4PoolManager.FullMathRoundCostTrace
import Benchmarks.UniswapV4PoolManager.RuntimeBlocks_058
import Benchmarks.UniswapV4PoolManager.RuntimeBlocks_060

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables
open Benchmarks.UniswapV4PoolManager.Immutables
namespace Benchmarks.UniswapV4PoolManager
set_option maxRecDepth 5000

theorem swapStepInputFeeTrace {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem rdata : ByteArray} {aw amount fee x0 x1 x2 x3 x4 x5 : UInt256}
    {σ : AccountMap} {k C : Nat} {R : List UInt256}
    (v : PoolManagerImmutables) (hstack : R.length+21 ≤ 1024) (hf : fee.toNat < 2^24)
    (h : RD (deployedRuntime v) I g s0 ⟨20382⟩
      ([swapStepFeeComplement fee, fee, x0, x1, x2, x3, x4, x5, amount] ++ R) mem aw rdata σ k C) :
    (swapStepFeeFits amount fee → ∃ k' C', C ≤ C' ∧
      RD (deployedRuntime v) I g s0 ⟨19695⟩
        ([swapStepFeeWord amount fee, x0, x1, x2, x3, x4, x5, amount] ++ R)
        mem aw rdata σ k' C') ∧
    (¬swapStepFeeFits amount fee → RDrev (deployedRuntime v) g s0) := by
  have hclean := u256LandMaskCleanOfToNat fee (UInt256.ofNat 16777215) rfl hf
  have rd1 := poolManagerBlocks.poolManager_block_20382 (by change R.length+12 ≤ 1024; omega)
    (by rw [poolManagerPatchedValidJumpsRuntime v]; jump_dest) h
  simp only [poolManagerBlocks.poolManager_block_20382_stack, hclean] at rd1
  have hr := fullMathRoundCostTrace (a := amount) (b := fee) (d := swapStepFeeComplement fee) v
    (by change R.length+21 ≤ 1024; exact hstack) (by rw [deployedRuntime_jumps]; jump_dest) rd1
  constructor
  · intro hfit
    obtain ⟨k2, C2, hC2, rd2⟩ := hr.1 hfit
    have rd3 := poolManagerBlocks.poolManager_block_20397 (by change R.length+9 ≤ 1024; omega)
      (by rw [poolManagerPatchedValidJumpsRuntime v]; jump_dest) rd2
    exact ⟨_, _, by omega, rd3⟩
  · intro hfit
    exact hr.2 hfit

theorem swapStepOutputFeeTrace {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem rdata : ByteArray} {aw amount fee j0 j1 j2 x0 x1 x2 x3 x4 x5 x6 : UInt256}
    {σ : AccountMap} {k C : Nat} {R : List UInt256}
    (v : PoolManagerImmutables) (hstack : R.length+26 ≤ 1024) (hf : fee.toNat < 2^24)
    (h : RD (deployedRuntime v) I g s0 ⟨20684⟩
      ([j0, j1, j2, amount, x0, x1, x2, x3, x4, x5, x6, fee] ++ R) mem aw rdata σ k C) :
    (swapStepFeeFits amount fee → ∃ k' C', C ≤ C' ∧
      RD (deployedRuntime v) I g s0 ⟨19714⟩
        ([swapStepFeeWord amount fee, j0, j1, j2, amount, x0, x1, x2, x3, x4, x5, x6, fee] ++ R)
        mem aw rdata σ k' C') ∧
    (¬swapStepFeeFits amount fee → RDrev (deployedRuntime v) g s0) := by
  have hclean := u256LandMaskCleanOfToNat fee (UInt256.ofNat 16777215) rfl hf
  have rd1 := poolManagerBlocks.poolManager_block_20684 (by change R.length+17 ≤ 1024; omega)
    (by rw [poolManagerPatchedValidJumpsRuntime v]; jump_dest) h
  simp only [poolManagerBlocks.poolManager_block_20684_stack, hclean] at rd1
  have hr := fullMathRoundCostTrace (a := amount) (b := fee) (d := swapStepFeeComplement fee) v
    (by change R.length+26 ≤ 1024; exact hstack) (by rw [deployedRuntime_jumps]; jump_dest) rd1
  constructor
  · intro hfit
    obtain ⟨k2, C2, hC2, rd2⟩ := hr.1 hfit
    have rd3 := poolManagerBlocks.poolManager_block_20707 (by change R.length+14 ≤ 1024; omega)
      (by rw [poolManagerPatchedValidJumpsRuntime v]; jump_dest) rd2
    exact ⟨_, _, by omega, rd3⟩
  · intro hfit
    exact hr.2 hfit

end Benchmarks.UniswapV4PoolManager
