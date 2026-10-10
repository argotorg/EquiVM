import Benchmarks.UniswapV4PoolManager.NextPriceOutputCoreTrace
import Benchmarks.UniswapV4PoolManager.NextPriceGuardWords

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables
open Benchmarks.UniswapV4PoolManager.Immutables
namespace Benchmarks.UniswapV4PoolManager
set_option maxRecDepth 5000

theorem nextPriceOutputTrace {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem rdata : ByteArray} {aw price liquidity amount j0 j1 j2 x0 x1 x2 x3 x4 x5 x6 x7 x8 : UInt256}
    {σ : AccountMap} {k C : Nat} {R : List UInt256}
    (v : PoolManagerImmutables) (zeroForOne : Bool) (hstack : R.length+33 ≤ 1024)
    (hp : price.toNat < 2^160) (hl : liquidity.toNat < 2^128)
    (h : RD (deployedRuntime v) I g s0 ⟨20727⟩
      ([j0, price, j1, j2, if zeroForOne then ⟨1⟩ else ⟨0⟩, liquidity, amount,
        x0, x1, x2, x3, x4, x5, x6, x7, x8] ++ R) mem aw rdata σ k C) :
    if nextPriceFits price liquidity amount false zeroForOne then ∃ k' C', C ≤ C' ∧
      RD (deployedRuntime v) I g s0 ⟨20872⟩
        ([nextPriceWord price liquidity amount false zeroForOne, liquidity, price, ⟨160⟩, amount, x8,
          if zeroForOne then ⟨1⟩ else ⟨0⟩, solcAddrMask, amount,
          x0, x1, x2, x3, x4, x5, x6, x7, x8] ++ R) mem aw rdata σ k' C'
    else RDrev (deployedRuntime v) g s0 := by
  have hd : (if zeroForOne then false else !false) = !zeroForOne := by cases zeroForOne <;> rfl
  by_cases hv : nextPriceValid price liquidity
  · simp only [nextPriceFits, nextPriceWord, hv, true_and, hd]
    have rd1 := poolManagerBlocks.poolManager_block_20727_fallthrough
      (by change R.length+16 ≤ 1024; omega) (nextPriceValid_test hv) h
    have hr := nextPriceOutputCoreTrace (price := price) (liquidity := liquidity) (amount := amount)
      v zeroForOne hstack hp hl rd1
    by_cases hf : nextPriceCalcFits price liquidity amount (!zeroForOne) false
    · rw [if_pos hf] at hr ⊢
      obtain ⟨k2, C2, hC2, rd2⟩ := hr
      exact ⟨k2, C2, by omega, rd2⟩
    · rw [if_neg hf] at hr ⊢
      exact hr
  · simp only [nextPriceFits, hv, false_and, if_false]
    have rd1 := poolManagerBlocks.poolManager_block_20727_taken
      (by change R.length+16 ≤ 1024; omega) (nextPriceInvalid_test hv)
      (by rw [poolManagerPatchedValidJumpsRuntime v]; jump_dest) h
    exact poolManagerBlocks.poolManager_block_20577 (by change R.length+16 ≤ 1024; omega) rd1

end Benchmarks.UniswapV4PoolManager
