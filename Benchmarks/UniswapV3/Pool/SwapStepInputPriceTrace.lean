import Benchmarks.UniswapV3.Pool.SwapStepPriceTraceModel
import Benchmarks.UniswapV3.Pool.NextPriceTrace

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables Benchmarks.UniswapV3.Pool.Immutables
open uniswapV3PoolBlocks
namespace Benchmarks.UniswapV3.Pool
set_option maxRecDepth 10000

theorem swapStepInputPriceX {σ : AccountMap} {ee : ExecutionEnv} {g : Sat256}
    {s0 : EVM.State} {k C : Nat} {aw currentRaw targetRaw liquidityRaw feeRaw : UInt256}
    {mem rdata : ByteArray} {R : List UInt256} {v : UniswapV3PoolImmutables} (a : SwapStepArgs)
    (rd : RD (deployedRuntime v) ee g s0 ⟨12542⟩
      (swapStepInitialDelta a :: swapStepBudget a ::
        swapStepReadyWords a currentRaw targetRaw liquidityRaw feeRaw ++ R) mem aw rdata σ k C)
    (hc : UInt256.land currentRaw (UInt256.ofNat (2 ^ 160 - 1)) = a.current)
    (hl : UInt256.land liquidityRaw (UInt256.ofNat (2 ^ 128 - 1)) = a.liquidity)
    (hi : swapStepExactIn a = true) (hov : R.length + 49 ≤ 1024) :
    (¬swapStepChoiceValid a ∧
      (RDrev (deployedRuntime v) g s0 ∨ RDinvalid (deployedRuntime v) g s0)) ∨
    (swapStepChoiceValid a ∧ ∃ k' C', RD (deployedRuntime v) ee g s0 ⟨12654⟩
      (swapStepPriceWords a currentRaw targetRaw liquidityRaw feeRaw ++ R)
      mem aw rdata σ k' C') := by
  simp only [swapStepReadyWords, swapStepRawWords, List.cons_append, List.nil_append] at rd
  cases hr : swapStepReachTarget a
  · have hcond : UInt256.lt (swapStepBudget a) (swapStepInitialDelta a) ≠ UInt256.ofNat 0 := by
      rw [ult_one (swapStepReachTarget_false a hr)]
      decide
    have r1 := uniswapV3Pool_block_12542_taken (immWords := wordsOf (immStore v))
      (by evm_ov) hcond (by rw [uniswapV3PoolPatchedValidJumpsRuntime v]; jump_dest) rd
    have r2 := uniswapV3Pool_block_12559 (immWords := wordsOf (immStore v))
      (by evm_ov) (by rw [uniswapV3PoolPatchedValidJumpsRuntime v]; jump_dest) r1
    have rcall : RD (deployedRuntime v) ee g s0 (nextPriceEntry true)
        ((if (swapStepNextArgs a).zeroForOne then ⟨1⟩ else ⟨0⟩) ::
          (swapStepNextArgs a).amount :: liquidityRaw :: currentRaw :: ⟨12571⟩ ::
          swapStepBudget a :: swapStepUnpricedWords a currentRaw targetRaw liquidityRaw feeRaw ++ R)
        mem aw rdata σ (k + 8 + 8) (C + 28 + 27) := by
      simpa only [uniswapV3Pool_block_12559_stack, swapStepUnpricedWords,
        swapStepRawWords, swapStepNextArgs, swapStepBeforeAmount, hi,
        Bool.true_eq_false, if_false, if_true, Bool.toUInt256,
        List.cons_append, List.nil_append] using r2
    rcases nextPriceX (v := v) true (swapStepNextArgs a) rcall hc hl
      (by rw [uniswapV3PoolPatchedValidJumps v]; jump_dest)
      (by change R.length + 12 + 37 ≤ 1024; omega) with ⟨hb, rr⟩ | ⟨hv, kr, Cr, rr⟩
    · refine Or.inl ⟨?_, rr⟩
      intro hv
      apply hb
      simpa only [swapStepChoiceValid, hr, Bool.false_eq_true, if_false, hi] using hv
    · have r3 := uniswapV3Pool_block_12571 (immWords := wordsOf (immStore v))
        (by change R.length + 5 + 8 ≤ 1024; omega) rr
      have r4 := uniswapV3Pool_block_12574 (immWords := wordsOf (immStore v))
        (by change R.length + 11 + 1 ≤ 1024; omega)
        (by rw [uniswapV3PoolPatchedValidJumpsRuntime v]; jump_dest) r3
      refine Or.inr ⟨?_, ?_⟩
      · simpa only [swapStepChoiceValid, hr, Bool.false_eq_true, if_false, hi] using hv
      · have packed := RD.pack r4
        simpa only [uniswapV3Pool_block_12571_stack, uniswapV3Pool_block_12574_stack,
          swapStepUnpricedWords, swapStepPriceWords, swapStepRawWords, swapStepRawPrice,
          hr, hi, Bool.false_eq_true, if_false, swapStepBeforeAmount, Bool.true_eq_false,
          if_true, List.cons_append, List.nil_append] using packed
  · have hcond := ult_zero (swapStepReachTarget_true a hr)
    have r1 := uniswapV3Pool_block_12542_fallthrough (immWords := wordsOf (immStore v))
      (by evm_ov) hcond rd
    have r2 := uniswapV3Pool_block_12552 (immWords := wordsOf (immStore v))
      (by evm_ov) (by rw [uniswapV3PoolPatchedValidJumpsRuntime v]; jump_dest) r1
    have r3 := uniswapV3Pool_block_12574 (immWords := wordsOf (immStore v))
      (by evm_ov) (by rw [uniswapV3PoolPatchedValidJumpsRuntime v]; jump_dest) r2
    refine Or.inr ⟨by simp only [swapStepChoiceValid, hr, if_true], ?_⟩
    have packed := RD.pack r3
    simpa only [uniswapV3Pool_block_12552_stack, uniswapV3Pool_block_12574_stack,
      swapStepPriceWords, swapStepRawWords, swapStepRawPrice, swapStepBeforeAmount,
      hr, hi, Bool.true_eq_false, if_false, if_true, List.cons_append, List.nil_append] using packed

end Benchmarks.UniswapV3.Pool
