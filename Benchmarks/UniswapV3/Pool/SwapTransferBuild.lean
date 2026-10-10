import Benchmarks.UniswapV3.Pool.SwapTransferSource
import Benchmarks.UniswapV3.Pool.SwapLoopGuardTrace
import Benchmarks.UniswapV3.Pool.RuntimeBlocks_018
import Benchmarks.UniswapV3.Pool.RuntimeBlocks_019

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables Benchmarks.UniswapV3.Pool.Immutables
open uniswapV3PoolBlocks
namespace Benchmarks.UniswapV3.Pool
set_option maxRecDepth 10000

def swapTransferEntry (second : Bool) : UInt256 := if second then ⟨4538⟩ else ⟨4839⟩
def swapTransferExit (second : Bool) : UInt256 := if second then ⟨4592⟩ else ⟨4894⟩

def swapPaymentWords (a : SwapArgs) (p exactWord cache snap dataStart dataLength ret : UInt256)
    (amount0 amount1 : Int) (R : List UInt256) : List UInt256 :=
  [p, exactWord, cache, snap, EVM.wordOfInt amount1, EVM.wordOfInt amount0] ++
    swapWords a dataStart dataLength ++ ret :: R

theorem swapPaymentGuardX {σ : AccountMap} {ee : ExecutionEnv} {g : Sat256}
    {s0 : EVM.State} {k C : Nat} {aw p exactWord cache snap dataStart dataLength ret : UInt256}
    {mem rdata : ByteArray} {R : List UInt256} {v : UniswapV3PoolImmutables}
    (a : SwapArgs) (amount0 amount1 : Int)
    (rd : RD (deployedRuntime v) ee g s0 ⟨4526⟩
      ([EVM.wordOfInt amount1, EVM.wordOfInt amount0] ++
        swapLoopWords a p exactWord cache snap dataStart dataLength ret R) mem aw rdata σ k C)
    (hov : R.length + 15 ≤ 1024) :
    ∃ k' C', RD (deployedRuntime v) ee g s0 (swapTransferEntry a.zeroForOne)
      (swapPaymentWords a p exactWord cache snap dataStart dataLength ret amount0 amount1 R)
      mem aw rdata σ k' C' := by
  cases hz : a.zeroForOne
  · have rr := uniswapV3Pool_block_4526_taken (immWords := wordsOf (immStore v))
      (by change R.length + 2 + 13 ≤ 1024; omega)
      (by change UInt256.isZero a.zeroForOne.toUInt256 ≠ _; rw [hz]; decide)
      (by rw [uniswapV3PoolPatchedValidJumpsRuntime v]; native_decide) rd
    refine ⟨k + 10, C + 33, ?_⟩
    simpa only [uniswapV3Pool_block_4526_taken_stack, swapPaymentWords, swapLoopWords,
      swapWords, List.cons_append, List.nil_append, swapTransferEntry, hz,
      Bool.false_eq_true, if_false] using rr
  · have rr := uniswapV3Pool_block_4526_fallthrough (immWords := wordsOf (immStore v))
      (by change R.length + 2 + 13 ≤ 1024; omega)
      (by change UInt256.isZero a.zeroForOne.toUInt256 = _; rw [hz]; decide) rd
    refine ⟨k + 10, C + 33, ?_⟩
    simpa only [uniswapV3Pool_block_4526_fallthrough_stack, swapPaymentWords, swapLoopWords,
      swapWords, List.cons_append, List.nil_append, swapTransferEntry, hz, if_true] using rr

theorem swapTransferBuildX {σ : AccountMap} {ee : ExecutionEnv} {g : Sat256}
    {s0 : EVM.State} {k C : Nat} {aw p exactWord cache snap dataStart dataLength ret : UInt256}
    {mem rdata : ByteArray} {R : List UInt256} {v : UniswapV3PoolImmutables}
    (second : Bool) (a : SwapArgs) (amount0 amount1 : Int)
    (rd : RD (deployedRuntime v) ee g s0 (swapTransferEntry second)
      (swapPaymentWords a p exactWord cache snap dataStart dataLength ret amount0 amount1 R)
      mem aw rdata σ k C)
    (hfit : -(2 ^ 255 : Int) ≤ (if second then amount1 else amount0) ∧
      (if second then amount1 else amount0) < 2 ^ 255) (hov : R.length + 18 ≤ 1024) :
    (¬ (if second then amount1 else amount0) < 0) ∧
      (∃ k' C', RD (deployedRuntime v) ee g s0 (swapTransferExit second)
        (swapPaymentWords a p exactWord cache snap dataStart dataLength ret amount0 amount1 R)
        mem aw rdata σ k' C') ∨
    (if second then amount1 else amount0) < 0 ∧
      (∃ k' C', RD (deployedRuntime v) ee g s0 ⟨15238⟩
        ([swapTransferValue (if second then amount1 else amount0), EVM.word a.recipient.val,
            EVM.word (poolToken v second).val, swapTransferExit second] ++
          swapPaymentWords a p exactWord cache snap dataStart dataLength ret amount0 amount1 R)
        mem aw rdata σ k' C') := by
  have hcmp : UInt256.slt (EVM.wordOfInt (if second then amount1 else amount0))
      (UInt256.ofNat 0) = if (if second then amount1 else amount0) < 0 then ⟨1⟩ else ⟨0⟩ :=
    slt_wordOfInt _ 0 hfit.1 hfit.2 (by decide) (by decide)
  cases second
  · simp only [Bool.false_eq_true, if_false] at hcmp ⊢
    by_cases hneg : amount0 < 0
    · have r1 := uniswapV3Pool_block_4839_fallthrough (immWords := wordsOf (immStore v))
        (by change R.length + 7 + 8 ≤ 1024; omega) (by rw [hcmp, if_pos hneg]; rfl) rd
      have r2 := uniswapV3Pool_block_4849 (immWords := wordsOf (immStore v))
        (by change R.length + 1 + 17 ≤ 1024; omega)
        (by rw [uniswapV3PoolPatchedValidJumpsRuntime v]; native_decide) r1
      simp only [uniswapV3Pool_block_4849_stack, wordsOf_immStore_token0] at r2
      exact Or.inr ⟨hneg, _, _, r2⟩
    · have r1 := uniswapV3Pool_block_4839_taken (immWords := wordsOf (immStore v))
        (by change R.length + 7 + 8 ≤ 1024; omega) (by rw [hcmp, if_neg hneg]; decide)
        (by rw [uniswapV3PoolPatchedValidJumpsRuntime v]; native_decide) rd
      exact Or.inl ⟨hneg, _, _, r1⟩
  · simp only [if_true] at hcmp ⊢
    by_cases hneg : amount1 < 0
    · have r1 := uniswapV3Pool_block_4538_fallthrough (immWords := wordsOf (immStore v))
        (by change R.length + 8 + 7 ≤ 1024; omega) (by rw [hcmp, if_pos hneg]; rfl) rd
      have r2 := uniswapV3Pool_block_4547 (immWords := wordsOf (immStore v))
        (by change R.length + 1 + 17 ≤ 1024; omega)
        (by rw [uniswapV3PoolPatchedValidJumpsRuntime v]; native_decide) r1
      simp only [uniswapV3Pool_block_4547_stack, wordsOf_immStore_token1] at r2
      exact Or.inr ⟨hneg, _, _, r2⟩
    · have r1 := uniswapV3Pool_block_4538_taken (immWords := wordsOf (immStore v))
        (by change R.length + 8 + 7 ≤ 1024; omega) (by rw [hcmp, if_neg hneg]; decide)
        (by rw [uniswapV3PoolPatchedValidJumpsRuntime v]; native_decide) rd
      exact Or.inl ⟨hneg, _, _, r1⟩

end Benchmarks.UniswapV3.Pool
