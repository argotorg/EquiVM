import Benchmarks.UniswapV4PoolManager.Amount0Words
import Benchmarks.UniswapV4PoolManager.FullMathRoundTrace
import Benchmarks.UniswapV4PoolManager.DivRoundTrace
import Benchmarks.UniswapV4PoolManager.RuntimeBlocks_052
import Benchmarks.UniswapV4PoolManager.RuntimeBlocks_038

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables
open Benchmarks.UniswapV4PoolManager.Immutables
namespace Benchmarks.UniswapV4PoolManager
set_option maxRecDepth 5000

theorem amount0UpCoreTrace {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem rdata : ByteArray} {aw lo hi liquidity ret : UInt256} {σ : AccountMap} {k C : Nat} {R : List UInt256}
    (v : PoolManagerImmutables) (hstack : R.length+16 ≤ 1024)
    (ho : lo.toNat ≤ hi.toNat) (hh : hi.toNat < 2^160) (hl : liquidity.toNat < 2^128)
    (hret : (D_J (deployedRuntime v) 0).contains ret = true)
    (h : RD (deployedRuntime v) I g s0 ⟨23218⟩ (hi :: lo :: liquidity :: ret :: R) mem aw rdata σ k C) :
    if amount0CoreFits lo hi liquidity true then ∃ k' C', RD (deployedRuntime v) I g s0 ret
      (amount0CoreWord lo hi liquidity true :: R) mem aw rdata σ k' C'
    else RDrev (deployedRuntime v) g s0 := by
  have hlo := u256LandMaskCleanOfToNat lo (UInt256.ofNat 1461501637330902918203684832716283019655932542975) rfl (lt_of_le_of_lt ho hh)
  have hhi := u256LandMaskCleanOfToNat hi (UInt256.ofNat 1461501637330902918203684832716283019655932542975) rfl hh
  have hn2 := u256LandMaskCleanOfToNat (amount0Numerator2 lo hi) (UInt256.ofNat 1461501637330902918203684832716283019655932542975) rfl
    (amount0Numerator2_bound ho hh)
  change UInt256.land (UInt256.sub hi lo) (UInt256.ofNat 1461501637330902918203684832716283019655932542975) =
    amount0Numerator2 lo hi at hn2
  by_cases hz : lo = ⟨0⟩
  · have hn : ¬amount0CoreFits lo hi liquidity true := fun hh => hh.1 hz
    rw [if_neg hn]
    have rd1 := poolManagerBlocks.poolManager_block_23218_taken
      (by change R.length+7 ≤ 1024; omega)
      (by rw [hlo, hz]; decide)
      (by rw [poolManagerPatchedValidJumpsRuntime v]; jump_dest) h
    exact poolManagerBlocks.poolManager_block_23330 (by change R.length+7 ≤ 1024; omega) rd1
  · have rd1 := poolManagerBlocks.poolManager_block_23218_fallthrough
      (by change R.length+7 ≤ 1024; omega) (by rw [hlo]; exact isZero_eq_zero_of_ne hz) h
    have rd2 := poolManagerBlocks.poolManager_block_23249
      (by change R.length+10 ≤ 1024; omega)
      (by rw [poolManagerPatchedValidJumpsRuntime v]; jump_dest) rd1
    simp only [poolManagerBlocks.poolManager_block_23249_stack] at rd2
    rw [amount0Numerator1_clean hl, hn2, hhi, hlo] at rd2
    have hfull := fullMathRoundTrace v (by change R.length+2+14 ≤ 1024; omega)
      (by rw [poolManagerPatchedValidJumps v]; jump_dest) rd2
    by_cases hf : fullMathRoundFits (amount0Numerator1 liquidity) (amount0Numerator2 lo hi) hi
    · rw [if_pos hf] at hfull
      obtain ⟨k3, C3, rd3⟩ := hfull
      have hfit : amount0CoreFits lo hi liquidity true := ⟨hz, hf⟩
      rw [if_pos hfit]
      exact ⟨_, _, divRoundTrace v (by change R.length+5 ≤ 1024; omega) hret rd3⟩
    · rw [if_neg hf] at hfull
      have hfit : ¬amount0CoreFits lo hi liquidity true := fun hh => hf hh.2
      rw [if_neg hfit]
      exact hfull

theorem amount0DownCoreTrace {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem rdata : ByteArray} {aw lo hi liquidity ret : UInt256} {σ : AccountMap} {k C : Nat} {R : List UInt256}
    (v : PoolManagerImmutables) (hstack : R.length+13 ≤ 1024)
    (ho : lo.toNat ≤ hi.toNat) (hh : hi.toNat < 2^160) (hl : liquidity.toNat < 2^128)
    (hret : (D_J (deployedRuntime v) 0).contains ret = true)
    (h : RD (deployedRuntime v) I g s0 ⟨23400⟩ (lo :: hi :: liquidity :: ret :: R) mem aw rdata σ k C) :
    if amount0CoreFits lo hi liquidity false then ∃ k' C', RD (deployedRuntime v) I g s0 ret
      (amount0CoreWord lo hi liquidity false :: R) mem aw rdata σ k' C'
    else RDrev (deployedRuntime v) g s0 := by
  have hlo := u256LandMaskCleanOfToNat lo (UInt256.ofNat 1461501637330902918203684832716283019655932542975) rfl (lt_of_le_of_lt ho hh)
  have hhi := u256LandMaskCleanOfToNat hi (UInt256.ofNat 1461501637330902918203684832716283019655932542975) rfl hh
  have hn2 := u256LandMaskCleanOfToNat (amount0Numerator2 lo hi) (UInt256.ofNat 1461501637330902918203684832716283019655932542975) rfl
    (amount0Numerator2_bound ho hh)
  change UInt256.land (UInt256.sub hi lo) (UInt256.ofNat 1461501637330902918203684832716283019655932542975) =
    amount0Numerator2 lo hi at hn2
  by_cases hz : lo = ⟨0⟩
  · have hn : ¬amount0CoreFits lo hi liquidity false := fun hh => hh.1 hz
    rw [if_neg hn]
    have rd1 := poolManagerBlocks.poolManager_block_23400_taken
      (by change R.length+7 ≤ 1024; omega)
      (by rw [hlo, hz]; decide)
      (by rw [poolManagerPatchedValidJumpsRuntime v]; jump_dest) h
    exact poolManagerBlocks.poolManager_block_23330 (by change R.length+7 ≤ 1024; omega) rd1
  · have rd1 := poolManagerBlocks.poolManager_block_23400_fallthrough
      (by change R.length+7 ≤ 1024; omega) (by rw [hlo]; exact isZero_eq_zero_of_ne hz) h
    have rd2 := poolManagerBlocks.poolManager_block_23431
      (by change R.length+11 ≤ 1024; omega)
      (by rw [poolManagerPatchedValidJumpsRuntime v]; jump_dest) rd1
    simp only [poolManagerBlocks.poolManager_block_23431_stack] at rd2
    rw [amount0Numerator1_clean hl, hn2, hhi, hlo] at rd2
    have hfull := fullMathTrace v (by change R.length+3+10 ≤ 1024; omega)
      (by rw [poolManagerPatchedValidJumps v]; jump_dest) rd2
    by_cases hf : fullMathFits (amount0Numerator1 liquidity) (amount0Numerator2 lo hi) hi
    · rw [if_pos hf] at hfull
      obtain ⟨k3, C3, rd3⟩ := hfull
      have hfit : amount0CoreFits lo hi liquidity false := ⟨hz, hf⟩
      rw [if_pos hfit]
      have rd4 := poolManagerBlocks.poolManager_block_23504
        (by change R.length+5 ≤ 1024; omega)
        (by rw [poolManagerPatchedValidJumpsRuntime v]; jump_dest) rd3
      have rd5 := poolManagerBlocks.poolManager_block_18722_fallthrough
        (by change R.length+6 ≤ 1024; omega) (isZero_eq_zero_of_ne hz) rd4
      have rd6 := poolManagerBlocks.poolManager_block_18729
        (by change R.length+4 ≤ 1024; omega)
        (by rw [poolManagerPatchedValidJumpsRuntime v]; jump_dest) rd5
      exact ⟨_, _, poolManagerBlocks.poolManager_block_13903
        (by change R.length+2 ≤ 1024; omega) hret rd6⟩
    · rw [if_neg hf] at hfull
      have hfit : ¬amount0CoreFits lo hi liquidity false := fun hh => hf hh.2
      rw [if_neg hfit]
      exact hfull

end Benchmarks.UniswapV4PoolManager
