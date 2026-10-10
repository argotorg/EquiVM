import Benchmarks.UniswapV4PoolManager.AmountDeltaTrace
import Benchmarks.UniswapV4PoolManager.RuntimeBlocks_055
import Benchmarks.UniswapV4PoolManager.RuntimeBlocks_056
import Benchmarks.UniswapV4PoolManager.RuntimeBlocks_058
import Benchmarks.UniswapV4PoolManager.RuntimeBlocks_059
import Benchmarks.UniswapV4PoolManager.RuntimeBlocks_060

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables
open Benchmarks.UniswapV4PoolManager.Immutables
namespace Benchmarks.UniswapV4PoolManager
set_option maxRecDepth 5000

theorem swapStepTailDeltaTrace {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem rdata : ByteArray} {aw price next liquidity x0 x1 x2 : UInt256}
    {σ : AccountMap} {k C : Nat} {R : List UInt256}
    (v : PoolManagerImmutables) (input zeroForOne : Bool) (hstack : R.length+19 ≤ 1024)
    (hp : price.toNat < 2^160) (hn : next.toNat < 2^160) (hl : liquidity.toNat < 2^128)
    (h : RD (deployedRuntime v) I g s0 (if input then ⟨20667⟩ else ⟨19697⟩)
      ([if zeroForOne then ⟨1⟩ else ⟨0⟩, next, liquidity, price, x0, x1, x2] ++ R) mem aw rdata σ k C) :
    if swapStepDeltaFits price next liquidity input zeroForOne then ∃ k' C', C ≤ C' ∧
      RD (deployedRuntime v) I g s0 (if input then ⟨20684⟩ else ⟨19714⟩)
        ([x2, x0, x1, swapStepDeltaWord price next liquidity input zeroForOne] ++ R) mem aw rdata σ k' C'
    else RDrev (deployedRuntime v) g s0 := by
  cases input with
  | false =>
    cases zeroForOne with
    | false =>
      simp only [swapStepDeltaFits, swapStepDeltaWord, Bool.false_eq_true, if_false, Bool.not_false] at h ⊢
      have rd1 := poolManagerBlocks.poolManager_block_19697_taken (by change R.length+8 ≤ 1024; omega)
        (by decide) (by rw [poolManagerPatchedValidJumpsRuntime v]; jump_dest) h
      have rd2 := poolManagerBlocks.poolManager_block_20368 (by change R.length+8 ≤ 1024; omega)
        (by rw [poolManagerPatchedValidJumpsRuntime v]; jump_dest) rd1
      have hc := amountDeltaCostTrace v true false (by change R.length+19 ≤ 1024; exact hstack) hp hn hl
        (by rw [deployedRuntime_jumps]; jump_dest) rd2
      by_cases hf : amountDeltaFits price next liquidity true false
      · rw [if_pos hf] at hc ⊢
        obtain ⟨k3, C3, hC3, rd3⟩ := hc
        have rd4 := poolManagerBlocks.poolManager_block_20377 (by change R.length+5 ≤ 1024; omega)
          (by rw [poolManagerPatchedValidJumpsRuntime v]; jump_dest) rd3
        have rd5 := poolManagerBlocks.poolManager_block_19712 (by change R.length+4 ≤ 1024; omega) rd4
        exact ⟨_, _, by omega, rd5⟩
      · rw [if_neg hf] at hc ⊢
        exact hc
    | true =>
      simp only [swapStepDeltaFits, swapStepDeltaWord, Bool.false_eq_true, if_false, if_true] at h ⊢
      have rd1 := poolManagerBlocks.poolManager_block_19697_fallthrough (by change R.length+8 ≤ 1024; omega)
        (by decide) h
      have rd2 := poolManagerBlocks.poolManager_block_19703 (by change R.length+8 ≤ 1024; omega)
        (by rw [poolManagerPatchedValidJumpsRuntime v]; jump_dest) rd1
      have hc := amountDeltaCostTrace v false false (by change R.length+19 ≤ 1024; exact hstack) hn hp hl
        (by rw [deployedRuntime_jumps]; jump_dest) rd2
      by_cases hf : amountDeltaFits next price liquidity false false
      · rw [if_pos hf] at hc ⊢
        obtain ⟨k3, C3, hC3, rd3⟩ := hc
        have rd4 := poolManagerBlocks.poolManager_block_19712 (by change R.length+4 ≤ 1024; omega) rd3
        exact ⟨_, _, by omega, rd4⟩
      · rw [if_neg hf] at hc ⊢
        exact hc
  | true =>
    cases zeroForOne with
    | false =>
      simp only [swapStepDeltaFits, swapStepDeltaWord, Bool.false_eq_true, if_false, if_true, Bool.not_true] at h ⊢
      have rd1 := poolManagerBlocks.poolManager_block_20667_taken (by change R.length+8 ≤ 1024; omega)
        (by decide) (by rw [poolManagerPatchedValidJumpsRuntime v]; jump_dest) h
      have rd2 := poolManagerBlocks.poolManager_block_20712 (by change R.length+8 ≤ 1024; omega)
        (by rw [poolManagerPatchedValidJumpsRuntime v]; jump_dest) rd1
      have hc := amountDeltaCostTrace v false true (by change R.length+19 ≤ 1024; exact hstack) hp hn hl
        (by rw [deployedRuntime_jumps]; jump_dest) rd2
      by_cases hf : amountDeltaFits price next liquidity false true
      · rw [if_pos hf] at hc ⊢
        obtain ⟨k3, C3, hC3, rd3⟩ := hc
        have rd4 := poolManagerBlocks.poolManager_block_20721 (by change R.length+5 ≤ 1024; omega)
          (by rw [poolManagerPatchedValidJumpsRuntime v]; jump_dest) rd3
        exact ⟨_, _, by omega, rd4⟩
      · rw [if_neg hf] at hc ⊢
        exact hc
    | true =>
      simp only [swapStepDeltaFits, swapStepDeltaWord, if_true] at h ⊢
      have rd1 := poolManagerBlocks.poolManager_block_20667_fallthrough (by change R.length+8 ≤ 1024; omega)
        (by decide) h
      have rd2 := poolManagerBlocks.poolManager_block_20673 (by change R.length+8 ≤ 1024; omega)
        (by rw [poolManagerPatchedValidJumpsRuntime v]; jump_dest) rd1
      have hc := amountDeltaCostTrace v true true (by change R.length+19 ≤ 1024; exact hstack) hn hp hl
        (by rw [deployedRuntime_jumps]; jump_dest) rd2
      by_cases hf : amountDeltaFits next price liquidity true true
      · rw [if_pos hf] at hc ⊢
        obtain ⟨k3, C3, hC3, rd3⟩ := hc
        have rd4 := poolManagerBlocks.poolManager_block_20682 (by change R.length+4 ≤ 1024; omega) rd3
        exact ⟨_, _, by omega, rd4⟩
      · rw [if_neg hf] at hc ⊢
        exact hc

end Benchmarks.UniswapV4PoolManager
