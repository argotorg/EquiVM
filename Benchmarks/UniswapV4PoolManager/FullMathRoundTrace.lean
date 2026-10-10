import Benchmarks.UniswapV4PoolManager.FullMathTrace
import Benchmarks.UniswapV4PoolManager.FullMathRoundWords
import Benchmarks.UniswapV4PoolManager.RuntimeBlocks_066

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables
open Benchmarks.UniswapV4PoolManager.Immutables
namespace Benchmarks.UniswapV4PoolManager
set_option maxRecDepth 5000

theorem fullMathRoundTrace {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem rdata : ByteArray} {aw a b d ret : UInt256} {σ : AccountMap} {k C : Nat} {R : List UInt256}
    (v : PoolManagerImmutables) (hstack : R.length+14 ≤ 1024)
    (hret : (D_J (deployedRuntime v) 0).contains ret = true)
    (h : RD (deployedRuntime v) I g s0 ⟨23656⟩ (a :: b :: d :: ret :: R) mem aw rdata σ k C) :
    if fullMathRoundFits a b d then ∃ k' C', RD (deployedRuntime v) I g s0 ret
      (fullMathRoundWord a b d :: R) mem aw rdata σ k' C'
    else RDrev (deployedRuntime v) g s0 := by
  have rd1 := poolManagerBlocks.poolManager_block_23656
    (by change R.length+9 ≤ 1024; omega)
    (by rw [poolManagerPatchedValidJumpsRuntime v]; jump_dest) h
  have hfull := fullMathTrace v (by change R.length+4+10 ≤ 1024; omega)
    (by rw [poolManagerPatchedValidJumps v]; jump_dest) rd1
  by_cases hf : fullMathFits a b d
  · rw [if_pos hf] at hfull
    obtain ⟨k2, C2, rd2⟩ := hfull
    have rd3 := poolManagerBlocks.poolManager_block_23670_fallthrough
      (by change R.length+7 ≤ 1024; omega) (isZero_eq_zero_of_ne (fullMathFits_ne hf)) rd2
    by_cases hz : fullMathRemainder a b d = ⟨0⟩
    · have hfit : fullMathRoundFits a b d := ⟨hf, Or.inl hz⟩
      rw [if_pos hfit, fullMathRoundWord, if_pos hz]
      have rd4 := poolManagerBlocks.poolManager_block_23678_fallthrough
        (by change R.length+5 ≤ 1024; omega) hz rd3
      have rd5 := poolManagerBlocks.poolManager_block_23683
        (by change R.length+2 ≤ 1024; omega) hret rd4
      exact ⟨_, _, rd5⟩
    · have rd4 := poolManagerBlocks.poolManager_block_23678_taken
        (by change R.length+5 ≤ 1024; omega) hz
        (by rw [poolManagerPatchedValidJumpsRuntime v]; jump_dest) rd3
      by_cases ho : fullMathWord a b d + ⟨1⟩ = ⟨0⟩
      · have hfit : ¬fullMathRoundFits a b d := fun hh => hh.2.elim hz (fun hn => hn ho)
        rw [if_neg hfit]
        have hzero : UInt256.ofNat 1 + fullMathWord a b d = ⟨0⟩ := by
          rw [u256_add_comm]; exact ho
        have rd5 := poolManagerBlocks.poolManager_block_23684_taken
          (by change R.length+4 ≤ 1024; omega)
          (by rw [hzero]; decide)
          (by rw [poolManagerPatchedValidJumpsRuntime v]; jump_dest) rd4
        exact emptyRevert v (by change R.length+4 ≤ 1024; omega) rd5
      · have hfit : fullMathRoundFits a b d := ⟨hf, Or.inr ho⟩
        rw [if_pos hfit, fullMathRoundWord, if_neg hz]
        have hnz : UInt256.ofNat 1 + fullMathWord a b d ≠ ⟨0⟩ := by
          rw [u256_add_comm]; exact ho
        have rd5 := poolManagerBlocks.poolManager_block_23684_fallthrough
          (by change R.length+4 ≤ 1024; omega) (isZero_eq_zero_of_ne hnz) rd4
        have rd6 := poolManagerBlocks.poolManager_block_23696
          (by change R.length+2 ≤ 1024; omega) hret rd5
        simp only [poolManagerBlocks.poolManager_block_23696_stack,
          poolManagerBlocks.poolManager_block_23684_fallthrough_stack] at rd6
        rw [u256_add_comm (UInt256.ofNat 1)] at rd6
        exact ⟨_, _, rd6⟩
  · rw [if_neg hf] at hfull
    have hfit : ¬fullMathRoundFits a b d := fun hh => hf hh.1
    rw [if_neg hfit]
    exact hfull

end Benchmarks.UniswapV4PoolManager
