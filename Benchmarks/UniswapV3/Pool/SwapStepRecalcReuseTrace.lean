import Benchmarks.UniswapV3.Pool.SwapStepRecalcTraceModel
import Benchmarks.UniswapV3.Pool.RuntimeBlocks_041
import Benchmarks.UniswapV3.Pool.RuntimeBlocks_042

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables Benchmarks.UniswapV3.Pool.Immutables
open uniswapV3PoolBlocks
namespace Benchmarks.UniswapV3.Pool
set_option maxRecDepth 10000

theorem swapStepRecalcReuseX {σ : AccountMap} {ee : ExecutionEnv} {g : Sat256}
    {s0 : EVM.State} {k C : Nat} {aw currentRaw targetRaw liquidityRaw feeRaw other : UInt256}
    {mem rdata : ByteArray} {R : List UInt256} {v : UniswapV3PoolImmutables}
    (a : SwapStepArgs) (input : Bool)
    (rd : RD (deployedRuntime v) ee g s0 (swapStepRecalcReusePC (swapStepZeroForOne a) input)
      (swapStepRecalcWords a input currentRaw targetRaw liquidityRaw feeRaw other ++ R)
      mem aw rdata σ k C)
    (hov : R.length + 13 ≤ 1024) :
    RD (deployedRuntime v) ee g s0 (swapStepRecalcJoinPC (swapStepZeroForOne a) input)
      (swapStepBeforeAmount a input ::
        swapStepRecalcWords a input currentRaw targetRaw liquidityRaw feeRaw other ++ R)
      mem aw rdata σ (k + 2) (C + 4) := by
  cases input <;> cases hz : swapStepZeroForOne a
  · simp only [swapStepRecalcReusePC, hz, Bool.false_eq_true, if_false, if_true] at rd
    have rr := uniswapV3Pool_block_12822 (immWords := wordsOf (immStore v)) 
      (by change R.length + 7 + 6 ≤ 1024; omega) rd
    simpa only [uniswapV3Pool_block_12822_stack, swapStepRecalcJoinPC, swapStepRecalcWords,
      swapStepCalcWords, swapStepRawWords, hz, Bool.false_eq_true, if_false, if_true,
      List.cons_append, List.nil_append] using rr
  · simp only [swapStepRecalcReusePC, hz, Bool.false_eq_true, if_false, if_true] at rd
    have rr := uniswapV3Pool_block_12744 (immWords := wordsOf (immStore v)) 
      (by change R.length + 7 + 6 ≤ 1024; omega) rd
    simpa only [uniswapV3Pool_block_12744_stack, swapStepRecalcJoinPC, swapStepRecalcWords,
      swapStepCalcWords, swapStepRawWords, hz, Bool.false_eq_true, if_false, if_true,
      List.cons_append, List.nil_append] using rr
  · simp only [swapStepRecalcReusePC, hz, Bool.false_eq_true, if_false, if_true] at rd
    have rr := uniswapV3Pool_block_12785 (immWords := wordsOf (immStore v)) 
      (by change R.length + 6 + 7 ≤ 1024; omega) rd
    simpa only [uniswapV3Pool_block_12785_stack, swapStepRecalcJoinPC, swapStepRecalcWords,
      swapStepCalcWords, swapStepRawWords, hz, Bool.false_eq_true, if_false, if_true,
      List.cons_append, List.nil_append] using rr
  · simp only [swapStepRecalcReusePC, hz, Bool.false_eq_true, if_false, if_true] at rd
    have rr := uniswapV3Pool_block_12707 (immWords := wordsOf (immStore v)) 
      (by change R.length + 6 + 7 ≤ 1024; omega) rd
    simpa only [uniswapV3Pool_block_12707_stack, swapStepRecalcJoinPC, swapStepRecalcWords,
      swapStepCalcWords, swapStepRawWords, hz, Bool.false_eq_true, if_false, if_true,
      List.cons_append, List.nil_append] using rr

end Benchmarks.UniswapV3.Pool
