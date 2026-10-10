import Benchmarks.UniswapV4PoolManager.NextPriceInputCoreTrace
import Benchmarks.UniswapV4PoolManager.NextPriceGuardWords

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables
open Benchmarks.UniswapV4PoolManager.Immutables
namespace Benchmarks.UniswapV4PoolManager
set_option maxRecDepth 5000

theorem nextPriceInputTrace {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem rdata : ByteArray} {aw price liquidity amount j0 j1 j2 j3 j4 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 : UInt256}
    {σ : AccountMap} {k C : Nat} {R : List UInt256}
    (v : PoolManagerImmutables) (zeroForOne : Bool) (hstack : R.length+34 ≤ 1024)
    (hp : price.toNat < 2^160) (hl : liquidity.toNat < 2^128)
    (h : RD (deployedRuntime v) I g s0 ⟨20402⟩
      ([amount, j0, j1, price, j2, if zeroForOne then ⟨1⟩ else ⟨0⟩, j3, j4, liquidity,
        x0, x1, x2, x3, x4, x5, x6, x7, x8, x9] ++ R) mem aw rdata σ k C) :
    if nextPriceFits price liquidity amount true zeroForOne then ∃ k' C', C ≤ C' ∧
      RD (deployedRuntime v) I g s0 ⟨20464⟩
        ([nextPriceWord price liquidity amount true zeroForOne, liquidity, price, x9, ⟨160⟩,
          if zeroForOne then ⟨1⟩ else ⟨0⟩, amount, amount, solcAddrMask,
          x0, x1, x2, x3, x4, x5, x6, x7, x8, x9] ++ R) mem aw rdata σ k' C'
    else RDrev (deployedRuntime v) g s0 := by
  have hd : (if zeroForOne then true else !true) = zeroForOne := by cases zeroForOne <;> rfl
  by_cases hv : nextPriceValid price liquidity
  · simp only [nextPriceFits, nextPriceWord, hv, true_and, hd]
    have rd1 := poolManagerBlocks.poolManager_block_20402_fallthrough
      (by change R.length+19 ≤ 1024; omega) (nextPriceValid_test hv) h
    have hr := nextPriceInputCoreTrace (price := price) (liquidity := liquidity) (amount := amount)
      v zeroForOne hstack hp hl hv rd1
    by_cases hf : nextPriceCalcFits price liquidity amount zeroForOne true
    · rw [if_pos hf] at hr ⊢
      obtain ⟨k2, C2, hC2, rd2⟩ := hr
      exact ⟨k2, C2, by omega, rd2⟩
    · rw [if_neg hf] at hr ⊢
      exact hr
  · simp only [nextPriceFits, hv, false_and, if_false]
    have rd1 := poolManagerBlocks.poolManager_block_20402_taken
      (by change R.length+19 ≤ 1024; omega) (nextPriceInvalid_test hv)
      (by rw [poolManagerPatchedValidJumpsRuntime v]; jump_dest) h
    exact poolManagerBlocks.poolManager_block_20577 (by change R.length+17 ≤ 1024; omega) rd1

end Benchmarks.UniswapV4PoolManager
