import Benchmarks.UniswapV3.Pool.SwapStepPriceTraceModel
import Benchmarks.UniswapV3.Pool.NextPriceTrace
import Benchmarks.UniswapV3.Pool.RuntimeBlocks_041

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables Benchmarks.UniswapV3.Pool.Immutables
open uniswapV3PoolBlocks
namespace Benchmarks.UniswapV3.Pool
set_option maxRecDepth 10000

theorem swapStepOutputPriceX {σ : AccountMap} {ee : ExecutionEnv} {g : Sat256}
    {s0 : EVM.State} {k C : Nat} {aw currentRaw targetRaw liquidityRaw feeRaw : UInt256}
    {mem rdata : ByteArray} {R : List UInt256} {v : UniswapV3PoolImmutables} (a : SwapStepArgs)
    (rd : RD (deployedRuntime v) ee g s0 ⟨12616⟩
      (swapStepInitialDelta a :: swapStepReadyWords a currentRaw targetRaw liquidityRaw feeRaw ++ R)
      mem aw rdata σ k C)
    (hc : UInt256.land currentRaw (UInt256.ofNat (2 ^ 160 - 1)) = a.current)
    (hl : UInt256.land liquidityRaw (UInt256.ofNat (2 ^ 128 - 1)) = a.liquidity)
    (hi : swapStepExactIn a = false) (hov : R.length + 48 ≤ 1024) :
    (¬swapStepChoiceValid a ∧
      (RDrev (deployedRuntime v) g s0 ∨ RDinvalid (deployedRuntime v) g s0)) ∨
    (swapStepChoiceValid a ∧ ∃ k' C', RD (deployedRuntime v) ee g s0 ⟨12654⟩
      (swapStepPriceWords a currentRaw targetRaw liquidityRaw feeRaw ++ R)
      mem aw rdata σ k' C') := by
  have hb : UInt256.sub (UInt256.ofNat 0) (EVM.wordOfInt a.remaining) = swapStepBudget a := by
    simp only [swapStepBudget, hi, Bool.false_eq_true, if_false]
    rfl
  simp only [swapStepReadyWords, swapStepRawWords, List.cons_append, List.nil_append] at rd
  cases hr : swapStepReachTarget a
  · have hcond : UInt256.lt (UInt256.sub (UInt256.ofNat 0) (EVM.wordOfInt a.remaining))
        (swapStepInitialDelta a) ≠ UInt256.ofNat 0 := by
      rw [hb, ult_one (swapStepReachTarget_false a hr)]
      decide
    have r1 := uniswapV3Pool_block_12616_taken (immWords := wordsOf (immStore v))
      (by evm_ov) hcond (by rw [uniswapV3PoolPatchedValidJumpsRuntime v]; jump_dest) rd
    have r2 := uniswapV3Pool_block_12636 (immWords := wordsOf (immStore v))
      (by evm_ov) (by rw [uniswapV3PoolPatchedValidJumpsRuntime v]; jump_dest) r1
    have rcall : RD (deployedRuntime v) ee g s0 (nextPriceEntry false)
        ((if (swapStepNextArgs a).zeroForOne then ⟨1⟩ else ⟨0⟩) ::
          (swapStepNextArgs a).amount :: liquidityRaw :: currentRaw :: ⟨12651⟩ ::
          swapStepUnpricedWords a currentRaw targetRaw liquidityRaw feeRaw ++ R)
        mem aw rdata σ (k + 10 + 10) (C + 34 + 33) := by
      simpa only [uniswapV3Pool_block_12636_stack, swapStepUnpricedWords,
        swapStepRawWords, swapStepNextArgs, swapStepBeforeAmount, hi, hb,
        Bool.false_eq_true, if_false, if_true, Bool.toUInt256,
        List.cons_append, List.nil_append] using r2
    rcases nextPriceX (v := v) false (swapStepNextArgs a) rcall hc hl
      (by rw [uniswapV3PoolPatchedValidJumps v]; jump_dest)
      (by change R.length + 11 + 37 ≤ 1024; omega) with ⟨hbad, rr⟩ | ⟨hv, kr, Cr, rr⟩
    · refine Or.inl ⟨?_, rr⟩
      intro hv
      apply hbad
      simpa only [swapStepChoiceValid, hr, Bool.false_eq_true, if_false, hi] using hv
    · have r3 := uniswapV3Pool_block_12651 (immWords := wordsOf (immStore v))
        (by change R.length + 5 + 7 ≤ 1024; omega) rr
      refine Or.inr ⟨?_, ?_⟩
      · simpa only [swapStepChoiceValid, hr, Bool.false_eq_true, if_false, hi] using hv
      · have packed := RD.pack r3
        simpa only [uniswapV3Pool_block_12651_stack, swapStepUnpricedWords,
          swapStepPriceWords, swapStepRawWords, swapStepRawPrice, hr, hi,
          Bool.false_eq_true, if_false, swapStepBeforeAmount, if_true,
          List.cons_append, List.nil_append] using packed
  · have hcond : UInt256.lt (UInt256.sub (UInt256.ofNat 0) (EVM.wordOfInt a.remaining))
        (swapStepInitialDelta a) = UInt256.ofNat 0 := by
      rw [hb, ult_zero (swapStepReachTarget_true a hr)]
      rfl
    have r1 := uniswapV3Pool_block_12616_fallthrough (immWords := wordsOf (immStore v))
      (by evm_ov) hcond rd
    have r2 := uniswapV3Pool_block_12629 (immWords := wordsOf (immStore v))
      (by evm_ov) (by rw [uniswapV3PoolPatchedValidJumpsRuntime v]; jump_dest) r1
    refine Or.inr ⟨by simp only [swapStepChoiceValid, hr, if_true], ?_⟩
    have packed := RD.pack r2
    simpa only [uniswapV3Pool_block_12629_stack, swapStepPriceWords, swapStepRawWords,
      swapStepRawPrice, swapStepBeforeAmount, hr, hi, Bool.false_eq_true, if_false, if_true,
      List.cons_append, List.nil_append] using packed

end Benchmarks.UniswapV3.Pool
