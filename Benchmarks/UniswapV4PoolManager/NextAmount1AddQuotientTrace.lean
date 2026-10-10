import Benchmarks.UniswapV4PoolManager.NextAmount1Words
import Benchmarks.UniswapV4PoolManager.FullMathShift96Trace
import Benchmarks.UniswapV4PoolManager.RuntimeBlocks_059
import Benchmarks.UniswapV4PoolManager.RuntimeBlocks_052

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables
open Benchmarks.UniswapV4PoolManager.Immutables
namespace Benchmarks.UniswapV4PoolManager
set_option maxRecDepth 5000

theorem nextAmount1AddQuotientTrace {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem rdata : ByteArray} {aw price liquidity amount j0 j1 j2 j3 : UInt256}
    {σ : AccountMap} {k C : Nat} {R : List UInt256}
    (v : PoolManagerImmutables) (hstack : R.length+20 ≤ 1024)
    (hl : liquidity.toNat < 2^128) (hn : liquidity ≠ ⟨0⟩)
    (h : RD (deployedRuntime v) I g s0 ⟨20476⟩
      ([liquidity, price, j0, j1, j2, j3, amount, solcAddrMask] ++ R) mem aw rdata σ k C) :
    if nextAmount1QuotientFits liquidity amount true then ∃ k' C', C ≤ C' ∧
      RD (deployedRuntime v) I g s0 ⟨20520⟩
        ([nextAmount1Quotient liquidity amount true, ⟨20528⟩, ⟨20533⟩,
          liquidity, price, j0, j1, j2, j3, amount, solcAddrMask] ++ R) mem aw rdata σ k' C'
    else RDrev (deployedRuntime v) g s0 := by
  have hclean : UInt256.land liquidity (UInt256.ofNat 340282366920938463463374607431768211455) = liquidity :=
    u256LandMaskCleanOfToNat liquidity _ (bits := 128) rfl hl
  by_cases hs : amount.toNat < 2^160
  · simp only [nextAmount1QuotientFits, nextAmount1Quotient, hs, if_true]
    have hg : UInt256.gt amount solcAddrMask = ⟨0⟩ := ugt_zero (by change amount.toNat ≤ 2^160-1; omega)
    have rd1 := poolManagerBlocks.poolManager_block_20476_fallthrough (by change R.length+10 ≤ 1024; omega) hg h
    have rd2 := poolManagerBlocks.poolManager_block_20484 (by change R.length+14 ≤ 1024; omega)
      (by rw [poolManagerPatchedValidJumpsRuntime v]; jump_dest) rd1
    simp only [poolManagerBlocks.poolManager_block_20484_stack, hclean] at rd2
    have rd3 := poolManagerBlocks.poolManager_block_18722_fallthrough
      (by change R.length+15 ≤ 1024; omega) (isZero_eq_zero_of_ne hn) rd2
    have rd4 := poolManagerBlocks.poolManager_block_18729
      (by change R.length+13 ≤ 1024; omega)
      (by rw [poolManagerPatchedValidJumpsRuntime v]; jump_dest) rd3
    exact ⟨_, _, by omega, rd4⟩
  · simp only [nextAmount1QuotientFits, nextAmount1Quotient, hs, if_false, if_true]
    have hg : UInt256.gt amount solcAddrMask ≠ ⟨0⟩ := by
      have he : UInt256.gt amount solcAddrMask = ⟨1⟩ := ugt_one (by change 2^160-1 < amount.toNat; omega)
      rw [he]; decide
    have rd1 := poolManagerBlocks.poolManager_block_20476_taken (by change R.length+10 ≤ 1024; omega) hg
      (by rw [poolManagerPatchedValidJumpsRuntime v]; jump_dest) h
    have rd2 := poolManagerBlocks.poolManager_block_20538 (by change R.length+14 ≤ 1024; omega)
      (by rw [poolManagerPatchedValidJumpsRuntime v]; jump_dest) rd1
    simp only [poolManagerBlocks.poolManager_block_20538_stack, hclean] at rd2
    have hfull := fullMathShift96CostTrace v (by change R.length+20 ≤ 1024; exact hstack)
      (by rw [deployedRuntime_jumps]; jump_dest) rd2
    by_cases hf : fullMathFits amount fullMathQ96 liquidity
    · rw [if_pos hf] at hfull ⊢
      obtain ⟨k3, C3, hC, rd3⟩ := hfull
      have rd4 := poolManagerBlocks.poolManager_block_20572
        (by change R.length+12 ≤ 1024; omega)
        (by rw [poolManagerPatchedValidJumpsRuntime v]; jump_dest) rd3
      exact ⟨_, _, by omega, rd4⟩
    · rw [if_neg hf] at hfull ⊢
      exact hfull

end Benchmarks.UniswapV4PoolManager
