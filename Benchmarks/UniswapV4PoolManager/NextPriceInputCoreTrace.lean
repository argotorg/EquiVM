import Benchmarks.UniswapV4PoolManager.NextPriceWords
import Benchmarks.UniswapV4PoolManager.NextAmount0Trace
import Benchmarks.UniswapV4PoolManager.NextAmount1Trace
import Benchmarks.UniswapV4PoolManager.RuntimeBlocks_058

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables
open Benchmarks.UniswapV4PoolManager.Immutables
namespace Benchmarks.UniswapV4PoolManager
set_option maxRecDepth 5000

theorem nextPriceInputCoreTrace {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem rdata : ByteArray} {aw price liquidity amount j x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 : UInt256}
    {σ : AccountMap} {k C : Nat} {R : List UInt256}
    (v : PoolManagerImmutables) (zeroForOne : Bool) (hstack : R.length+34 ≤ 1024)
    (hp : price.toNat < 2^160) (hl : liquidity.toNat < 2^128) (hn : nextPriceValid price liquidity)
    (h : RD (deployedRuntime v) I g s0 ⟨20421⟩
      ([price, if zeroForOne then ⟨1⟩ else ⟨0⟩, j, amount, liquidity,
        x0, x1, x2, x3, x4, x5, x6, x7, x8, x9] ++ R) mem aw rdata σ k C) :
    if nextPriceCalcFits price liquidity amount zeroForOne true then ∃ k' C', C ≤ C' ∧
      RD (deployedRuntime v) I g s0 ⟨20464⟩
        ([nextPriceCalcWord price liquidity amount zeroForOne true, liquidity, price, x9, ⟨160⟩,
          if zeroForOne then ⟨1⟩ else ⟨0⟩, j, amount, solcAddrMask,
          x0, x1, x2, x3, x4, x5, x6, x7, x8, x9] ++ R) mem aw rdata σ k' C'
    else RDrev (deployedRuntime v) g s0 := by
  cases zeroForOne with
  | false =>
    simp only [nextPriceCalcFits, nextPriceCalcWord, Bool.false_eq_true, if_false] at h ⊢
    have rd1 := poolManagerBlocks.poolManager_block_20421_taken (by change R.length+20 ≤ 1024; omega)
      (by decide) (by rw [poolManagerPatchedValidJumpsRuntime v]; jump_dest) h
    have hr := nextAmount1AddTrace (price := price) (liquidity := liquidity) (amount := amount) v
      (by change R.length+30 ≤ 1024; omega) hp hl hn.2 rd1
    by_cases hf : nextAmount1Fits price liquidity amount true
    · rw [if_pos hf] at hr ⊢
      obtain ⟨k2, C2, hC2, rd2⟩ := hr
      exact ⟨k2, C2, by omega, rd2⟩
    · rw [if_neg hf] at hr ⊢
      exact hr
  | true =>
    simp only [nextPriceCalcFits, nextPriceCalcWord, if_true] at h ⊢
    have rd1 := poolManagerBlocks.poolManager_block_20421_fallthrough (by change R.length+20 ≤ 1024; omega)
      (by decide) h
    have rd2 := poolManagerBlocks.poolManager_block_20454 (by change R.length+23 ≤ 1024; omega)
      (by rw [poolManagerPatchedValidJumpsRuntime v]; jump_dest) rd1
    have hr := nextAmount0AddTrace (price := price) (liquidity := liquidity) (amount := amount) v
      (by change R.length+34 ≤ 1024; exact hstack) hp hl hn.1
      (by rw [deployedRuntime_jumps]; jump_dest) rd2
    by_cases hf : nextAmount0Fits price liquidity amount true
    · rw [if_pos hf] at hr ⊢
      obtain ⟨k3, C3, hC3, rd3⟩ := hr
      exact ⟨k3, C3, by omega, rd3⟩
    · rw [if_neg hf] at hr ⊢
      exact hr

end Benchmarks.UniswapV4PoolManager
