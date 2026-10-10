import Benchmarks.UniswapV4PoolManager.PoolSwapAmountWords
import Benchmarks.UniswapV4PoolManager.SafeCast256Trace
import Benchmarks.UniswapV4PoolManager.SignedAddTrace
import Benchmarks.UniswapV4PoolManager.ReachCost
import Benchmarks.UniswapV4PoolManager.RuntimeBlocks_058

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables
open Benchmarks.UniswapV4PoolManager.Immutables
namespace Benchmarks.UniswapV4PoolManager
set_option maxRecDepth 5000

theorem poolSwapInputAmountTrace {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem rdata : ByteArray} {s : PoolSwapStepWords}
    {aw remaining calculated step x1 params tag fee protocol amountToProtocol dir : UInt256}
    {σ : AccountMap} {k C : Nat} {R : List UInt256}
    (v : PoolManagerImmutables) (hstack : R.length+15 ≤ 1024)
    (hi : memLoad (step+UInt256.ofNat 128) mem = s.amountIn)
    (ho : memLoad (step+UInt256.ofNat 160) mem = s.amountOut)
    (hf : memLoad (step+UInt256.ofNat 192) mem = s.feeAmount)
    (h : RD (deployedRuntime v) I g s0 ⟨20320⟩
      ([remaining, x1, params, calculated, tag, fee, protocol, amountToProtocol, dir, step] ++ R) mem aw rdata σ k C) :
    if poolSwapInputAmountFits s calculated then ∃ k' C', C ≤ C' ∧
      RD (deployedRuntime v) I g s0 ⟨19794⟩
        ([tag, x1, params, remaining+(s.amountIn+s.feeAmount), calculated+s.amountOut,
          fee, protocol, amountToProtocol, dir, step] ++ R)
        mem (M (M (M aw (step+UInt256.ofNat 128) ⟨32⟩) (step+UInt256.ofNat 192) ⟨32⟩)
          (step+UInt256.ofNat 160) ⟨32⟩) rdata σ k' C'
    else RDrev (deployedRuntime v) g s0 := by
  have htotal : memLoad (step+UInt256.ofNat 192) mem + memLoad (step+UInt256.ofNat 128) mem = s.amountIn+s.feeAmount := by
    rw [hf, hi, u256_add_comm]
  by_cases ht : (s.amountIn+s.feeAmount).toNat < 2^255
  · have rd1 := poolManagerBlocks.poolManager_block_20320_fallthrough (by change R.length+13 ≤ 1024; omega)
      (by rw [htotal, uintToInt256_guard, decide_eq_false (not_not_intro ht)]; rfl) h
    simp only [poolManagerBlocks.poolManager_block_20320_fallthrough_stack, htotal] at rd1
    by_cases hout : s.amountOut.toNat < 2^255
    · have rd2 := poolManagerBlocks.poolManager_block_20340_fallthrough (by change R.length+13 ≤ 1024; omega)
        (by rw [ho, uintToInt256_guard, decide_eq_false (not_not_intro hout)]; rfl) rd1
      simp only [poolManagerBlocks.poolManager_block_20340_fallthrough_stack, ho] at rd2
      have rd3 := poolManagerBlocks.poolManager_block_20354 (by change R.length+9+4 ≤ 1024; omega)
        (by rw [poolManagerPatchedValidJumpsRuntime v]; jump_dest) rd2
      simp only [poolManagerBlocks.poolManager_block_20354_stack] at rd3
      by_cases hfit : int256Fits (EVM.signed calculated+EVM.signed s.amountOut)
      · rw [if_pos (show poolSwapInputAmountFits s calculated from ⟨ht, hout, hfit⟩)]
        obtain ⟨k4, C4, hC4, rd4⟩ := RD_retainCost (fun budget start rd =>
          checkedSignedAddPass v (by change R.length+9+6 ≤ 1024; omega) hfit
            (by rw [poolManagerPatchedValidJumps v]; jump_dest) rd) rd3
        have rd5 := poolManagerBlocks.poolManager_block_20362 (by change R.length+5+6 ≤ 1024; omega)
          (by rw [poolManagerPatchedValidJumpsRuntime v]; jump_dest) rd4
        simp only [poolManagerBlocks.poolManager_block_20362_stack] at rd5
        exact ⟨_, _, by omega, rd5⟩
      · rw [if_neg (show ¬poolSwapInputAmountFits s calculated from fun h => hfit h.2.2)]
        exact checkedSignedAddReverts v (by change R.length+9+6 ≤ 1024; omega) hfit rd3
    · rw [if_neg (show ¬poolSwapInputAmountFits s calculated from fun h => hout h.2.1)]
      have rd2 := poolManagerBlocks.poolManager_block_20340_taken (by change R.length+13 ≤ 1024; omega)
        (by rw [ho, uintToInt256_guard, decide_eq_true hout]; decide)
        (by rw [poolManagerPatchedValidJumpsRuntime v]; jump_dest) rd1
      exact poolManagerBlocks.poolManager_block_12488 (by change R.length+13 ≤ 1024; omega) rd2
  · rw [if_neg (show ¬poolSwapInputAmountFits s calculated from fun h => ht h.1)]
    have rd1 := poolManagerBlocks.poolManager_block_20320_taken (by change R.length+13 ≤ 1024; omega)
      (by rw [htotal, uintToInt256_guard, decide_eq_true ht]; decide)
      (by rw [poolManagerPatchedValidJumpsRuntime v]; jump_dest) h
    exact poolManagerBlocks.poolManager_block_12488 (by change R.length+13 ≤ 1024; omega) rd1

end Benchmarks.UniswapV4PoolManager
