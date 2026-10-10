import Benchmarks.UniswapV4PoolManager.PoolSwapAmountWords
import Benchmarks.UniswapV4PoolManager.SafeCast256Trace
import Benchmarks.UniswapV4PoolManager.SignedSubGuard
import Benchmarks.UniswapV4PoolManager.Arithmetic
import Benchmarks.UniswapV4PoolManager.ReachCost
import Benchmarks.UniswapV4PoolManager.RuntimeBlocks_056

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables
open Benchmarks.UniswapV4PoolManager.Immutables
namespace Benchmarks.UniswapV4PoolManager
set_option maxRecDepth 5000

theorem poolSwapOutputAmountTrace {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem rdata : ByteArray} {s : PoolSwapStepWords}
    {aw remaining calculated step x1 params tag fee protocol amountToProtocol dir : UInt256}
    {σ : AccountMap} {k C : Nat} {R : List UInt256}
    (v : PoolManagerImmutables) (hstack : R.length+14 ≤ 1024)
    (hi : memLoad (step+UInt256.ofNat 128) mem = s.amountIn)
    (ho : memLoad (step+UInt256.ofNat 160) mem = s.amountOut)
    (hf : memLoad (step+UInt256.ofNat 192) mem = s.feeAmount)
    (h : RD (deployedRuntime v) I g s0 ⟨19740⟩
      ([remaining, x1, params, calculated, tag, fee, protocol, amountToProtocol, dir, step] ++ R) mem aw rdata σ k C) :
    if poolSwapOutputAmountFits s calculated then ∃ k' C', C ≤ C' ∧
      RD (deployedRuntime v) I g s0 ⟨19794⟩
        ([tag, x1, params, UInt256.sub remaining s.amountOut, UInt256.sub calculated (s.amountIn+s.feeAmount),
          fee, protocol, amountToProtocol, dir, step] ++ R)
        mem (M (M (M aw (step+UInt256.ofNat 160) ⟨32⟩) (step+UInt256.ofNat 128) ⟨32⟩)
          (step+UInt256.ofNat 192) ⟨32⟩) rdata σ k' C'
    else RDrev (deployedRuntime v) g s0 := by
  by_cases hout : s.amountOut.toNat < 2^255
  · have rd1 := poolManagerBlocks.poolManager_block_19740_fallthrough (by change R.length+13 ≤ 1024; omega)
      (by rw [ho, uintToInt256_guard, decide_eq_false (not_not_intro hout)]; rfl) h
    simp only [poolManagerBlocks.poolManager_block_19740_fallthrough_stack, ho] at rd1
    have rd2 := poolManagerBlocks.poolManager_block_19753 (by change R.length+14 ≤ 1024; omega)
      (by rw [poolManagerPatchedValidJumpsRuntime v]; jump_dest) rd1
    simp only [poolManagerBlocks.poolManager_block_19753_stack, hi, hf] at rd2
    by_cases hsum : s.amountIn.toNat+s.feeAmount.toNat < UInt256.size
    · obtain ⟨k3, C3, hC3, rd3⟩ := RD_retainCost (fun budget start rd =>
        checkedAddPass v (by change R.length+10+4 ≤ 1024; omega) hsum
          (by rw [poolManagerPatchedValidJumps v]; jump_dest) rd) rd2
      by_cases ht : (s.amountIn+s.feeAmount).toNat < 2^255
      · have rd4 := poolManagerBlocks.poolManager_block_19773_fallthrough (by change R.length+10+3 ≤ 1024; omega)
          (by rw [uintToInt256_guard, decide_eq_false (not_not_intro ht)]; rfl) rd3
        have hb : 0 ≤ EVM.signed (s.amountIn+s.feeAmount) :=
          le_of_not_gt (fun hh => (signedNegative_iff _).mp hh ht)
        by_cases hfit : int256Fits (EVM.signed calculated-EVM.signed (s.amountIn+s.feeAmount))
        · rw [if_pos (show poolSwapOutputAmountFits s calculated from ⟨hout, hsum, ht, hfit⟩)]
          have rd5 := poolManagerBlocks.poolManager_block_19781_fallthrough (by change R.length+9+3 ≤ 1024; omega)
            (by rw [signedSubNonnegGuard _ _ hb, decide_eq_false (not_not_intro hfit)]; rfl) rd4
          have rd6 := poolManagerBlocks.poolManager_block_19793 (by change R.length+5+5 ≤ 1024; omega) rd5
          simp only [poolManagerBlocks.poolManager_block_19793_stack] at rd6
          exact ⟨_, _, by omega, rd6⟩
        · rw [if_neg (show ¬poolSwapOutputAmountFits s calculated from fun h => hfit h.2.2.2)]
          have rd5 := poolManagerBlocks.poolManager_block_19781_taken (by change R.length+9+3 ≤ 1024; omega)
            (by rw [signedSubNonnegGuard _ _ hb, decide_eq_true hfit]; decide)
            (by rw [poolManagerPatchedValidJumpsRuntime v]; jump_dest) rd4
          exact poolManagerBlocks.poolManager_block_7572 (by change R.length+12 ≤ 1024; omega) rd5
      · rw [if_neg (show ¬poolSwapOutputAmountFits s calculated from fun h => ht h.2.2.1)]
        have rd4 := poolManagerBlocks.poolManager_block_19773_taken (by change R.length+10+3 ≤ 1024; omega)
          (by rw [uintToInt256_guard, decide_eq_true ht]; decide)
          (by rw [poolManagerPatchedValidJumpsRuntime v]; jump_dest) rd3
        exact poolManagerBlocks.poolManager_block_12488 (by change R.length+13 ≤ 1024; omega) rd4
    · rw [if_neg (show ¬poolSwapOutputAmountFits s calculated from fun h => hsum h.2.1)]
      exact checkedAddReverts v (by change R.length+10+4 ≤ 1024; omega) (Nat.le_of_not_gt hsum) rd2
  · rw [if_neg (show ¬poolSwapOutputAmountFits s calculated from fun h => hout h.1)]
    have rd1 := poolManagerBlocks.poolManager_block_19740_taken (by change R.length+13 ≤ 1024; omega)
      (by rw [ho, uintToInt256_guard, decide_eq_true hout]; decide)
      (by rw [poolManagerPatchedValidJumpsRuntime v]; jump_dest) h
    exact poolManagerBlocks.poolManager_block_12488 (by change R.length+13 ≤ 1024; omega) rd1

end Benchmarks.UniswapV4PoolManager
