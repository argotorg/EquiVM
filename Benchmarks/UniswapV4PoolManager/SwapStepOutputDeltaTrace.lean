import Benchmarks.UniswapV4PoolManager.AmountDeltaTrace
import Benchmarks.UniswapV4PoolManager.RuntimeBlocks_059
import Benchmarks.UniswapV4PoolManager.RuntimeBlocks_061

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables
open Benchmarks.UniswapV4PoolManager.Immutables
namespace Benchmarks.UniswapV4PoolManager
set_option maxRecDepth 5000

theorem swapStepOutputDeltaTrace {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem rdata : ByteArray} {aw price target liquidity j fee : UInt256}
    {σ : AccountMap} {k C : Nat} {R : List UInt256}
    (v : PoolManagerImmutables) (zeroForOne : Bool) (hstack : R.length+21 ≤ 1024)
    (hp : price.toNat < 2^160) (ht : target.toNat < 2^160) (hl : liquidity.toNat < 2^128)
    (h : RD (deployedRuntime v) I g s0 ⟨20607⟩
      ([price, j, if zeroForOne then ⟨1⟩ else ⟨0⟩, target, fee, liquidity] ++ R) mem aw rdata σ k C) :
    if swapStepDeltaFits price target liquidity false zeroForOne then ∃ k' C', C ≤ C' ∧
      RD (deployedRuntime v) I g s0 ⟨20631⟩
        ([target, price, swapStepDeltaWord price target liquidity false zeroForOne,
          j, if zeroForOne then ⟨1⟩ else ⟨0⟩, liquidity] ++ R) mem aw rdata σ k' C'
    else RDrev (deployedRuntime v) g s0 := by
  cases zeroForOne with
  | false =>
    simp only [swapStepDeltaFits, swapStepDeltaWord, Bool.false_eq_true, if_false, Bool.not_false] at h ⊢
    have rd1 := poolManagerBlocks.poolManager_block_20607_taken (by change R.length+7 ≤ 1024; omega)
      (by decide) (by rw [poolManagerPatchedValidJumpsRuntime v]; jump_dest) h
    have rd2 := poolManagerBlocks.poolManager_block_21017 (by change R.length+10 ≤ 1024; omega)
      (by rw [poolManagerPatchedValidJumpsRuntime v]; jump_dest) rd1
    have hc := amountDeltaCostTrace v true false (by change R.length+21 ≤ 1024; exact hstack) hp ht hl
      (by rw [deployedRuntime_jumps]; jump_dest) rd2
    by_cases hf : amountDeltaFits price target liquidity true false
    · rw [if_pos hf] at hc ⊢
      obtain ⟨k3, C3, hC3, rd3⟩ := hc
      have rd4 := poolManagerBlocks.poolManager_block_21028 (by change R.length+7 ≤ 1024; omega)
        (by rw [poolManagerPatchedValidJumpsRuntime v]; jump_dest) rd3
      exact ⟨_, _, by omega, rd4⟩
    · rw [if_neg hf] at hc ⊢
      exact hc
  | true =>
    simp only [swapStepDeltaFits, swapStepDeltaWord, if_true] at h ⊢
    have rd1 := poolManagerBlocks.poolManager_block_20607_fallthrough (by change R.length+7 ≤ 1024; omega)
      (by decide) h
    have rd2 := poolManagerBlocks.poolManager_block_20619 (by change R.length+10 ≤ 1024; omega)
      (by rw [poolManagerPatchedValidJumpsRuntime v]; jump_dest) rd1
    have hc := amountDeltaCostTrace v false false (by change R.length+21 ≤ 1024; exact hstack) ht hp hl
      (by rw [deployedRuntime_jumps]; jump_dest) rd2
    by_cases hf : amountDeltaFits target price liquidity false false
    · rw [if_pos hf] at hc ⊢
      obtain ⟨k3, C3, hC3, rd3⟩ := hc
      have rd4 := poolManagerBlocks.poolManager_block_20629 (by change R.length+6 ≤ 1024; omega) rd3
      exact ⟨_, _, by omega, rd4⟩
    · rw [if_neg hf] at hc ⊢
      exact hc

end Benchmarks.UniswapV4PoolManager
