import Benchmarks.UniswapV4PoolManager.NextAmount1Source
import Benchmarks.UniswapV4PoolManager.NextAmount1AddQuotientTrace
import Benchmarks.UniswapV4PoolManager.NextAmount1AddTailTrace
import Benchmarks.UniswapV4PoolManager.NextAmount1SubQuotientTrace
import Benchmarks.UniswapV4PoolManager.NextAmount1SubGuardTrace

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables
open Benchmarks.UniswapV4PoolManager.Immutables
namespace Benchmarks.UniswapV4PoolManager
set_option maxRecDepth 5000

theorem nextAmount1AddTrace {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem rdata : ByteArray} {aw price liquidity amount j0 j1 j2 j3 : UInt256}
    {σ : AccountMap} {k C : Nat} {R : List UInt256}
    (v : PoolManagerImmutables) (hstack : R.length+20 ≤ 1024)
    (hp : price.toNat < 2^160) (hl : liquidity.toNat < 2^128) (hn : liquidity ≠ ⟨0⟩)
    (h : RD (deployedRuntime v) I g s0 ⟨20476⟩
      ([liquidity, price, j0, j1, j2, j3, amount, solcAddrMask] ++ R) mem aw rdata σ k C) :
    if nextAmount1Fits price liquidity amount true then ∃ k' C', C ≤ C' ∧
      RD (deployedRuntime v) I g s0 ⟨20464⟩
        ([nextAmount1Word price liquidity amount true, liquidity, price, j0, j1, j2, j3, amount, solcAddrMask] ++ R)
        mem aw rdata σ k' C'
    else RDrev (deployedRuntime v) g s0 := by
  have hq := nextAmount1AddQuotientTrace v hstack hl hn h
  by_cases hf : nextAmount1QuotientFits liquidity amount true
  · rw [if_pos hf] at hq
    obtain ⟨k1, C1, hC1, rd1⟩ := hq
    have ht := nextAmount1AddTailTrace v (by omega) hp rd1
    simp only [nextAmount1Fits, hf, true_and, if_true, nextAmount1Word]
    by_cases hs : price.toNat+(nextAmount1Quotient liquidity amount true).toNat < 2^160
    · rw [if_pos hs] at ht ⊢
      obtain ⟨k2, C2, hC2, rd2⟩ := ht
      exact ⟨k2, C2, Nat.le_trans hC1 hC2, rd2⟩
    · rw [if_neg hs] at ht ⊢
      exact ht
  · rw [if_neg hf] at hq
    simpa only [nextAmount1Fits, hf, false_and, if_false] using hq

theorem nextAmount1SubTrace {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem rdata : ByteArray} {aw price liquidity amount junk j0 j1 x0 x1 x2 x3 x4 x5 x6 x7 x8 : UInt256}
    {σ : AccountMap} {k C : Nat} {R : List UInt256}
    (v : PoolManagerImmutables) (hstack : R.length+25 ≤ 1024)
    (hp : price.toNat < 2^160) (hl : liquidity.toNat < 2^128)
    (h : RD (deployedRuntime v) I g s0 ⟨20749⟩
      ([junk, j0, price, j1, liquidity, amount, x0, x1, x2, x3, x4, x5, x6, x7, x8] ++ R)
      mem aw rdata σ k C) :
    if nextAmount1Fits price liquidity amount false then ∃ k' C', C ≤ C' ∧
      RD (deployedRuntime v) I g s0 ⟨20872⟩
        ([nextAmount1Word price liquidity amount false, liquidity, price, ⟨160⟩, j0, x8, j1, solcAddrMask,
          amount, x0, x1, x2, x3, x4, x5, x6, x7, x8] ++ R) mem aw rdata σ k' C'
    else RDrev (deployedRuntime v) g s0 := by
  have hq := nextAmount1SubQuotientTrace v (by change R.length+25 ≤ 1024; exact hstack) hl h
  by_cases hf : nextAmount1QuotientFits liquidity amount false
  · rw [if_pos hf] at hq
    obtain ⟨k1, C1, hC1, rd1⟩ := hq
    have hg := nextAmount1SubGuardTrace v (by change R.length+18 ≤ 1024; omega) hp rd1
    simp only [nextAmount1Fits, hf, true_and, Bool.false_eq_true, if_false, nextAmount1Word]
    by_cases hs : (nextAmount1Quotient liquidity amount false).toNat < price.toNat
    · rw [if_pos hs] at hg ⊢
      obtain ⟨k2, C2, hC2, rd2⟩ := hg
      have rd3 := poolManagerBlocks.poolManager_block_20841 (by change R.length+20 ≤ 1024; omega) rd2
      simp only [poolManagerBlocks.poolManager_block_20841_stack] at rd3
      have hc : (UInt256.sub price (nextAmount1Quotient liquidity amount false)).toNat < 2^160 := by
        rw [usub_toNat (Nat.le_of_lt hs)]
        omega
      have hm := solcAddrMask_clean hc
      change UInt256.land (UInt256.sub price (nextAmount1Quotient liquidity amount false))
        (UInt256.ofNat 1461501637330902918203684832716283019655932542975) = _ at hm
      rw [hm] at rd3
      exact ⟨_, _, by omega, rd3⟩
    · rw [if_neg hs] at hg ⊢
      exact hg
  · rw [if_neg hf] at hq
    simpa only [nextAmount1Fits, hf, false_and, if_false] using hq

end Benchmarks.UniswapV4PoolManager
