import Benchmarks.UniswapV4PoolManager.NextPriceInputCoreTrace
import Benchmarks.UniswapV4PoolManager.RuntimeBlocks_061

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables
open Benchmarks.UniswapV4PoolManager.Immutables
namespace Benchmarks.UniswapV4PoolManager
set_option maxRecDepth 5000

theorem nextPriceOutputCoreTrace {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem rdata : ByteArray} {aw price liquidity amount j x0 x1 x2 x3 x4 x5 x6 x7 x8 : UInt256}
    {σ : AccountMap} {k C : Nat} {R : List UInt256}
    (v : PoolManagerImmutables) (zeroForOne : Bool) (hstack : R.length+33 ≤ 1024)
    (hp : price.toNat < 2^160) (hl : liquidity.toNat < 2^128)
    (h : RD (deployedRuntime v) I g s0 ⟨20742⟩
      ([j, price, if zeroForOne then ⟨1⟩ else ⟨0⟩, liquidity, amount,
        x0, x1, x2, x3, x4, x5, x6, x7, x8] ++ R) mem aw rdata σ k C) :
    if nextPriceCalcFits price liquidity amount (!zeroForOne) false then ∃ k' C', C ≤ C' ∧
      RD (deployedRuntime v) I g s0 ⟨20872⟩
        ([nextPriceCalcWord price liquidity amount (!zeroForOne) false, liquidity, price, ⟨160⟩, j, x8,
          if zeroForOne then ⟨1⟩ else ⟨0⟩, solcAddrMask, amount,
          x0, x1, x2, x3, x4, x5, x6, x7, x8] ++ R) mem aw rdata σ k' C'
    else RDrev (deployedRuntime v) g s0 := by
  cases zeroForOne with
  | false =>
    simp only [nextPriceCalcFits, nextPriceCalcWord, Bool.not_false, Bool.false_eq_true, if_false, if_true] at h ⊢
    have rd1 := poolManagerBlocks.poolManager_block_20742_taken (by change R.length+17 ≤ 1024; omega)
      (by decide) (by rw [poolManagerPatchedValidJumpsRuntime v]; jump_dest) h
    have rd2 := poolManagerBlocks.poolManager_block_20975 (by change R.length+22 ≤ 1024; omega)
      (by rw [poolManagerPatchedValidJumpsRuntime v]; jump_dest) rd1
    have hr := nextAmount0SubTrace (price := price) (liquidity := liquidity) (amount := amount) v
      (by change R.length+33 ≤ 1024; exact hstack) hp hl
      (by rw [deployedRuntime_jumps]; jump_dest) rd2
    by_cases hf : nextAmount0Fits price liquidity amount false
    · rw [if_pos hf] at hr ⊢
      obtain ⟨k3, C3, hC3, rd3⟩ := hr
      have rd4 := poolManagerBlocks.poolManager_block_21012 (by change R.length+19 ≤ 1024; omega)
        (by rw [poolManagerPatchedValidJumpsRuntime v]; jump_dest) rd3
      exact ⟨_, _, by omega, rd4⟩
    · rw [if_neg hf] at hr ⊢
      exact hr
  | true =>
    simp only [nextPriceCalcFits, nextPriceCalcWord, Bool.not_true, Bool.false_eq_true, if_false, if_true] at h ⊢
    have rd1 := poolManagerBlocks.poolManager_block_20742_fallthrough (by change R.length+17 ≤ 1024; omega)
      (by decide) h
    have hr := nextAmount1SubTrace (price := price) (liquidity := liquidity) (amount := amount) v
      (by change R.length+25 ≤ 1024; omega) hp hl rd1
    by_cases hf : nextAmount1Fits price liquidity amount false
    · rw [if_pos hf] at hr ⊢
      obtain ⟨k2, C2, hC2, rd2⟩ := hr
      exact ⟨k2, C2, by omega, rd2⟩
    · rw [if_neg hf] at hr ⊢
      exact hr

end Benchmarks.UniswapV4PoolManager
