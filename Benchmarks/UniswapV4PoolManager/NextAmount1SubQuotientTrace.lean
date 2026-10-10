import Benchmarks.UniswapV4PoolManager.NextAmount1Words
import Benchmarks.UniswapV4PoolManager.FullMathTrace
import Benchmarks.UniswapV4PoolManager.ReachCost
import Benchmarks.UniswapV4PoolManager.RuntimeBlocks_060
import Benchmarks.UniswapV4PoolManager.RuntimeBlocks_061

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables
open Benchmarks.UniswapV4PoolManager.Immutables
namespace Benchmarks.UniswapV4PoolManager
set_option maxRecDepth 5000

theorem nextAmount1SubQuotientTrace {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem rdata : ByteArray} {aw price liquidity amount junk j0 j1 : UInt256}
    {σ : AccountMap} {k C : Nat} {R : List UInt256}
    (v : PoolManagerImmutables) (hstack : R.length+16 ≤ 1024) (hl : liquidity.toNat < 2^128)
    (h : RD (deployedRuntime v) I g s0 ⟨20749⟩
      ([junk, j0, price, j1, liquidity, amount] ++ R) mem aw rdata σ k C) :
    if nextAmount1QuotientFits liquidity amount false then ∃ k' C', C ≤ C' ∧
      RD (deployedRuntime v) I g s0 ⟨20808⟩
        ([nextAmount1Quotient liquidity amount false, j0, price, j1, liquidity, amount] ++ R)
        mem aw rdata σ k' C'
    else RDrev (deployedRuntime v) g s0 := by
  have hclean : UInt256.land liquidity (UInt256.ofNat 340282366920938463463374607431768211455) = liquidity :=
    u256LandMaskCleanOfToNat liquidity _ (bits := 128) rfl hl
  by_cases hs : amount.toNat < 2^160
  · simp only [nextAmount1QuotientFits, nextAmount1Quotient, hs, if_true, Bool.false_eq_true, if_false]
    have hg : UInt256.gt amount solcAddrMask = ⟨0⟩ := ugt_zero (by change amount.toNat ≤ 2^160-1; omega)
    have rd1 := poolManagerBlocks.poolManager_block_20749_fallthrough (by change R.length+7 ≤ 1024; omega) hg h
    have rd2 := poolManagerBlocks.poolManager_block_20777 (by change R.length+9 ≤ 1024; omega) rd1
    simp only [poolManagerBlocks.poolManager_block_20777_stack, hclean] at rd2
    exact ⟨_, _, by omega, rd2⟩
  · simp only [nextAmount1QuotientFits, nextAmount1Quotient, hs, if_false, Bool.false_eq_true]
    have hg : UInt256.gt amount solcAddrMask ≠ ⟨0⟩ := by
      have he : UInt256.gt amount solcAddrMask = ⟨1⟩ := ugt_one (by change 2^160-1 < amount.toNat; omega)
      rw [he]; decide
    have rd1 := poolManagerBlocks.poolManager_block_20749_taken (by change R.length+7 ≤ 1024; omega) hg
      (by rw [poolManagerPatchedValidJumpsRuntime v]; jump_dest) h
    have rd2 := poolManagerBlocks.poolManager_block_20892 (by change R.length+11 ≤ 1024; omega)
      (by rw [poolManagerPatchedValidJumpsRuntime v]; jump_dest) rd1
    simp only [poolManagerBlocks.poolManager_block_20892_stack, hclean] at rd2
    by_cases hf : fullMathFits amount fullMathQ96 liquidity
    · obtain ⟨k3, C3, hC3, rd3⟩ := RD_retainCost (fun _ _ hin => by
        have hr := fullMathTrace (b := fullMathQ96) v (by change R.length+16 ≤ 1024; exact hstack)
          (by rw [deployedRuntime_jumps]; jump_dest) hin
        rw [if_pos hf] at hr
        exact hr) rd2
      have rd4 := poolManagerBlocks.poolManager_block_20935_fallthrough
        (by change R.length+9 ≤ 1024; omega) (isZero_eq_zero_of_ne (fullMathFits_ne hf)) rd3
      by_cases hz : fullMathRemainder amount fullMathQ96 liquidity = ⟨0⟩
      · have hfit : fullMathRoundFits amount fullMathQ96 liquidity := ⟨hf, Or.inl hz⟩
        rw [if_pos hfit, fullMathRoundWord, if_pos hz]
        have rd5 := poolManagerBlocks.poolManager_block_20943_taken
          (by change R.length+9 ≤ 1024; omega)
          (by change UInt256.isZero (fullMathRemainder amount fullMathQ96 liquidity) ≠ ⟨0⟩; rw [hz]; decide)
          (by rw [poolManagerPatchedValidJumpsRuntime v]; jump_dest) rd4
        exact ⟨_, _, by omega, rd5⟩
      · have rd5 := poolManagerBlocks.poolManager_block_20943_fallthrough
          (by change R.length+9 ≤ 1024; omega) (isZero_eq_zero_of_ne hz) rd4
        by_cases ho : fullMathWord amount fullMathQ96 liquidity+⟨1⟩ = ⟨0⟩
        · have hfit : ¬fullMathRoundFits amount fullMathQ96 liquidity := fun hh => hh.2.elim hz (fun hn => hn ho)
          rw [if_neg hfit]
          have hzero : UInt256.ofNat 1+fullMathWord amount fullMathQ96 liquidity = ⟨0⟩ := by
            rw [u256_add_comm]; exact ho
          have rd6 := poolManagerBlocks.poolManager_block_20964_fallthrough
            (by change R.length+8 ≤ 1024; omega) hzero rd5
          exact poolManagerBlocks.poolManager_block_20972 (by change R.length+8 ≤ 1024; omega) rd6
        · have hfit : fullMathRoundFits amount fullMathQ96 liquidity := ⟨hf, Or.inr ho⟩
          rw [if_pos hfit, fullMathRoundWord, if_neg hz]
          have hnonzero : UInt256.ofNat 1+fullMathWord amount fullMathQ96 liquidity ≠ ⟨0⟩ := by
            rw [u256_add_comm]; exact ho
          have rd6 := poolManagerBlocks.poolManager_block_20964_taken
            (by change R.length+8 ≤ 1024; omega) hnonzero
            (by rw [poolManagerPatchedValidJumpsRuntime v]; jump_dest) rd5
          simp only [poolManagerBlocks.poolManager_block_20964_taken_stack] at rd6
          rw [u256_add_comm (UInt256.ofNat 1)] at rd6
          exact ⟨_, _, by omega, rd6⟩
    · have hfit : ¬fullMathRoundFits amount fullMathQ96 liquidity := fun hh => hf hh.1
      rw [if_neg hfit]
      have hr := fullMathTrace (b := fullMathQ96) v (by change R.length+16 ≤ 1024; exact hstack)
        (by rw [deployedRuntime_jumps]; jump_dest) rd2
      rw [if_neg hf] at hr
      exact hr

end Benchmarks.UniswapV4PoolManager
