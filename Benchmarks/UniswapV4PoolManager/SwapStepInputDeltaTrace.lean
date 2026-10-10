import Benchmarks.UniswapV4PoolManager.AmountDeltaTrace
import Benchmarks.UniswapV4PoolManager.RuntimeBlocks_055
import Benchmarks.UniswapV4PoolManager.RuntimeBlocks_059

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables
open Benchmarks.UniswapV4PoolManager.Immutables
namespace Benchmarks.UniswapV4PoolManager
set_option maxRecDepth 5000

theorem swapStepInputDeltaTrace {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem rdata : ByteArray} {aw price target liquidity available feeComplement j fee : UInt256}
    {σ : AccountMap} {k C : Nat} {R : List UInt256}
    (v : PoolManagerImmutables) (zeroForOne : Bool) (hstack : R.length+24 ≤ 1024)
    (hp : price.toNat < 2^160) (ht : target.toNat < 2^160) (hl : liquidity.toNat < 2^128)
    (h : RD (deployedRuntime v) I g s0 ⟨19615⟩
      ([available, feeComplement, price, j, if zeroForOne then ⟨1⟩ else ⟨0⟩, target, fee, liquidity] ++ R)
      mem aw rdata σ k C) :
    if swapStepDeltaFits price target liquidity true zeroForOne then ∃ k' C', C ≤ C' ∧
      RD (deployedRuntime v) I g s0 ⟨19635⟩
        ([available, target, feeComplement, price, j, if zeroForOne then ⟨1⟩ else ⟨0⟩,
          swapStepDeltaWord price target liquidity true zeroForOne, fee, liquidity] ++ R) mem aw rdata σ k' C'
    else RDrev (deployedRuntime v) g s0 := by
  cases zeroForOne with
  | false =>
    simp only [swapStepDeltaFits, swapStepDeltaWord, Bool.false_eq_true, if_false, Bool.not_true] at h ⊢
    have rd1 := poolManagerBlocks.poolManager_block_19615_taken (by change R.length+10 ≤ 1024; omega)
      (by decide) (by rw [poolManagerPatchedValidJumpsRuntime v]; jump_dest) h
    have rd2 := poolManagerBlocks.poolManager_block_20590 (by change R.length+13 ≤ 1024; omega)
      (by rw [poolManagerPatchedValidJumpsRuntime v]; jump_dest) rd1
    have hc := amountDeltaCostTrace v false true (by change R.length+24 ≤ 1024; exact hstack) hp ht hl
      (by rw [deployedRuntime_jumps]; jump_dest) rd2
    by_cases hf : amountDeltaFits price target liquidity false true
    · rw [if_pos hf] at hc ⊢
      obtain ⟨k3, C3, hC3, rd3⟩ := hc
      have rd4 := poolManagerBlocks.poolManager_block_20601 (by change R.length+10 ≤ 1024; omega)
        (by rw [poolManagerPatchedValidJumpsRuntime v]; jump_dest) rd3
      exact ⟨_, _, by omega, rd4⟩
    · rw [if_neg hf] at hc ⊢
      exact hc
  | true =>
    simp only [swapStepDeltaFits, swapStepDeltaWord, if_true] at h ⊢
    have rd1 := poolManagerBlocks.poolManager_block_19615_fallthrough (by change R.length+10 ≤ 1024; omega)
      (by decide) h
    have rd2 := poolManagerBlocks.poolManager_block_19623 (by change R.length+13 ≤ 1024; omega)
      (by rw [poolManagerPatchedValidJumpsRuntime v]; jump_dest) rd1
    have hc := amountDeltaCostTrace v true true (by change R.length+24 ≤ 1024; exact hstack) ht hp hl
      (by rw [deployedRuntime_jumps]; jump_dest) rd2
    by_cases hf : amountDeltaFits target price liquidity true true
    · rw [if_pos hf] at hc ⊢
      obtain ⟨k3, C3, hC3, rd3⟩ := hc
      have rd4 := poolManagerBlocks.poolManager_block_19633 (by change R.length+9 ≤ 1024; omega) rd3
      exact ⟨_, _, by omega, rd4⟩
    · rw [if_neg hf] at hc ⊢
      exact hc

end Benchmarks.UniswapV4PoolManager
