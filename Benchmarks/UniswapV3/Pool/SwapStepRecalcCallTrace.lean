import Benchmarks.UniswapV3.Pool.SwapStepRecalcTraceModel
import Benchmarks.UniswapV3.Pool.SwapStepDeltaTrace
import Benchmarks.UniswapV3.Pool.RuntimeBlocks_041
import Benchmarks.UniswapV3.Pool.RuntimeBlocks_042

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables Benchmarks.UniswapV3.Pool.Immutables
open uniswapV3PoolBlocks
namespace Benchmarks.UniswapV3.Pool
set_option maxRecDepth 10000

theorem swapStepRecalcCallX {σ : AccountMap} {ee : ExecutionEnv} {g : Sat256}
    {s0 : EVM.State} {k C : Nat} {aw currentRaw targetRaw liquidityRaw feeRaw other : UInt256}
    {mem rdata : ByteArray} {R : List UInt256} {v : UniswapV3PoolImmutables}
    (a : SwapStepArgs) (input : Bool)
    (rd : RD (deployedRuntime v) ee g s0 (swapStepRecalcCallPC (swapStepZeroForOne a) input)
      (swapStepRecalcWords a input currentRaw targetRaw liquidityRaw feeRaw other ++ R)
      mem aw rdata σ k C)
    (hc : UInt256.land currentRaw (UInt256.ofNat (2 ^ 160 - 1)) = a.current)
    (ht : UInt256.land targetRaw (UInt256.ofNat (2 ^ 160 - 1)) = a.target)
    (hl : UInt256.land liquidityRaw (UInt256.ofNat (2 ^ 128 - 1)) = a.liquidity)
    (ha : a.Fits) (hv : swapStepPriceValid a) (hov : R.length + 42 ≤ 1024) :
    (¬amountDeltaValid (swapStepDeltaOne a input) (swapStepDeltaArgs a (swapStepPrice a) input) ∧
      RDrev (deployedRuntime v) g s0) ∨
    (amountDeltaValid (swapStepDeltaOne a input) (swapStepDeltaArgs a (swapStepPrice a) input) ∧
      ∃ k' C', RD (deployedRuntime v) ee g s0 (swapStepRecalcJoinPC (swapStepZeroForOne a) input)
        (swapStepRecalcDelta a input ::
          swapStepRecalcWords a input currentRaw targetRaw liquidityRaw feeRaw other ++ R)
        mem aw rdata σ k' C') := by
  have rcall : RD (deployedRuntime v) ee g s0
      (UInt256.ofNat (amountDeltaEntry (swapStepDeltaOne a input)))
      (swapStepDeltaRawWords a input currentRaw (swapStepRawPrice a currentRaw targetRaw)
        liquidityRaw ++ swapStepRecalcCallRet (swapStepZeroForOne a) input ::
        swapStepRecalcWords a input currentRaw targetRaw liquidityRaw feeRaw other ++ R)
      mem aw rdata σ (k + 7) (C + 26) := by
    cases input <;> cases hz : swapStepZeroForOne a
    · simp only [swapStepRecalcCallPC, hz, Bool.false_eq_true, if_false, if_true] at rd
      have rr := uniswapV3Pool_block_12805 (immWords := wordsOf (immStore v))
        (by change R.length + 18 ≤ 1024; omega)
        (by rw [uniswapV3PoolPatchedValidJumpsRuntime v]; jump_dest) rd
      simpa only [uniswapV3Pool_block_12805_stack, swapStepDeltaRawWords, swapStepDeltaOne,
        amountDeltaEntry, swapStepRecalcCallRet, swapStepRecalcWords, swapStepCalcWords,
        swapStepRawWords, hz, Bool.false_eq_true, if_false, if_true, Bool.not_false, Bool.not_true,
        List.cons_append, List.nil_append] using rr
    · simp only [swapStepRecalcCallPC, hz, Bool.false_eq_true, if_false, if_true] at rd
      have rr := uniswapV3Pool_block_12727 (immWords := wordsOf (immStore v))
        (by change R.length + 18 ≤ 1024; omega)
        (by rw [uniswapV3PoolPatchedValidJumpsRuntime v]; jump_dest) rd
      simpa only [uniswapV3Pool_block_12727_stack, swapStepDeltaRawWords, swapStepDeltaOne,
        amountDeltaEntry, swapStepRecalcCallRet, swapStepRecalcWords, swapStepCalcWords,
        swapStepRawWords, hz, Bool.false_eq_true, if_false, if_true, Bool.not_false, Bool.not_true,
        List.cons_append, List.nil_append] using rr
    · simp only [swapStepRecalcCallPC, hz, Bool.false_eq_true, if_false, if_true] at rd
      have rr := uniswapV3Pool_block_12768 (immWords := wordsOf (immStore v))
        (by change R.length + 18 ≤ 1024; omega)
        (by rw [uniswapV3PoolPatchedValidJumpsRuntime v]; jump_dest) rd
      simpa only [uniswapV3Pool_block_12768_stack, swapStepDeltaRawWords, swapStepDeltaOne,
        amountDeltaEntry, swapStepRecalcCallRet, swapStepRecalcWords, swapStepCalcWords,
        swapStepRawWords, hz, Bool.false_eq_true, if_false, if_true, Bool.not_false, Bool.not_true,
        List.cons_append, List.nil_append] using rr
    · simp only [swapStepRecalcCallPC, hz, Bool.false_eq_true, if_false, if_true] at rd
      have rr := uniswapV3Pool_block_12690 (immWords := wordsOf (immStore v))
        (by change R.length + 18 ≤ 1024; omega)
        (by rw [uniswapV3PoolPatchedValidJumpsRuntime v]; jump_dest) rd
      simpa only [uniswapV3Pool_block_12690_stack, swapStepDeltaRawWords, swapStepDeltaOne,
        amountDeltaEntry, swapStepRecalcCallRet, swapStepRecalcWords, swapStepCalcWords,
        swapStepRawWords, hz, Bool.false_eq_true, if_false, if_true, Bool.not_false, Bool.not_true,
        List.cons_append, List.nil_append] using rr
  have hp := swapStepRawPrice_clean a currentRaw targetRaw hc ht ha hv.2.2
  have hret : (D_J (deployedRuntime v) 0).contains
      (swapStepRecalcCallRet (swapStepZeroForOne a) input) = true := by
    cases input <;> cases hz : swapStepZeroForOne a <;>
      simp only [swapStepRecalcCallRet, hz, Bool.false_eq_true, if_false, if_true] <;>
      rw [uniswapV3PoolPatchedValidJumps v] <;> jump_dest
  rcases swapStepDeltaX (v := v) a (swapStepPrice a) input currentRaw
    (swapStepRawPrice a currentRaw targetRaw) liquidityRaw rcall hc hp hl ha
    (swapStepPrice_fits a ha hv) hret (by change R.length + 12 + 30 ≤ 1024; omega) with
    ⟨hbad, rr⟩ | ⟨hd, kr, Cr, rr⟩
  · exact Or.inl ⟨hbad, rr⟩
  · refine Or.inr ⟨hd, kr + 3, Cr + 12, ?_⟩
    cases input <;> cases hz : swapStepZeroForOne a
    · simp only [swapStepRecalcCallRet, hz, Bool.false_eq_true, if_false, if_true] at rr
      exact uniswapV3Pool_block_12817 (immWords := wordsOf (immStore v))
        (by change R.length + 13 + 1 ≤ 1024; omega)
        (by rw [uniswapV3PoolPatchedValidJumpsRuntime v]; jump_dest) rr
    · simp only [swapStepRecalcCallRet, hz, Bool.false_eq_true, if_false, if_true] at rr
      exact uniswapV3Pool_block_12739 (immWords := wordsOf (immStore v))
        (by change R.length + 13 + 1 ≤ 1024; omega)
        (by rw [uniswapV3PoolPatchedValidJumpsRuntime v]; jump_dest) rr
    · simp only [swapStepRecalcCallRet, hz, Bool.false_eq_true, if_false, if_true] at rr
      exact uniswapV3Pool_block_12780 (immWords := wordsOf (immStore v))
        (by change R.length + 13 + 1 ≤ 1024; omega)
        (by rw [uniswapV3PoolPatchedValidJumpsRuntime v]; jump_dest) rr
    · simp only [swapStepRecalcCallRet, hz, Bool.false_eq_true, if_false, if_true] at rr
      exact uniswapV3Pool_block_12702 (immWords := wordsOf (immStore v))
        (by change R.length + 13 + 1 ≤ 1024; omega)
        (by rw [uniswapV3PoolPatchedValidJumpsRuntime v]; jump_dest) rr

end Benchmarks.UniswapV3.Pool
