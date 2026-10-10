import Benchmarks.UniswapV3.Pool.SwapStepRecalcGet

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.UniswapV3.Pool
set_option maxRecDepth 1000

theorem swapStepRecalcCallReverts (locals imms : Store) (evm : EVM.State) (a : SwapStepArgs)
    (input : Bool) (hg : SwapStepCalcGet locals a) (ha : a.Fits) (hp : swapStepPriceValid a)
    (hv : ¬amountDeltaValid (swapStepDeltaOne a input)
      (swapStepDeltaArgs a (swapStepPrice a) input)) :
    ExecStmt config (swapStepCalcFrame imms (swapStepRecalcZeroLocals locals a input)) evm
      (.internalCall (amountDeltaName (swapStepDeltaOne a input))
        (swapStepDeltaCallArgs a input "sqrtRatioNextX96") (swapStepRecalcCallName a input))
      .reverted := by
  have hz := swapStepRecalcZeroGet locals a input hg
  exact swapStepDeltaCallReverts _ imms evm a (swapStepPrice a) input "sqrtRatioNextX96"
    (swapStepRecalcCallName a input) hz.current hz.price hz.liquidity
    (swapStepDeltaArgs_fits a _ input ha (swapStepPrice_fits a ha hp)) hv

theorem swapStepRecalcReverts (locals imms : Store) (evm : EVM.State) (a : SwapStepArgs)
    (input : Bool) (hg : SwapStepCalcGet locals a) (ha : a.Fits) (hp : swapStepPriceValid a)
    (hv : ¬swapStepRecalcValid a input) :
    ExecBlock config (swapStepCalcFrame imms locals) evm (swapStepRecalcBlock a input)
      .reverted := by
  have hk : swapStepKeep a input = false := by
    cases h : swapStepKeep a input
    · rfl
    · exact False.elim (hv (by simp only [swapStepRecalcValid, h, if_true]))
  have hd : ¬amountDeltaValid (swapStepDeltaOne a input)
      (swapStepDeltaArgs a (swapStepPrice a) input) := by
    simpa only [swapStepRecalcValid, hk, Bool.false_eq_true, if_false] using hv
  have he := evalSwapStepRecalcTest
    (swapStepCalcFrame imms (swapStepRecalcZeroLocals locals a input)) evm a input
    (swapStepRecalcZeroGet locals a input hg)
  refine ExecBlock.consNormal
    (solm' := swapStepCalcFrame imms (swapStepRecalcZeroLocals locals a input))
    (ExecStmt.letDecl (by simp only [evalExpr?, pure])) ?_
  exact ExecBlock.consRevert (ExecStmt.iteFalse (by simpa only [hk] using he)
    (ExecBlock.consRevert (swapStepRecalcCallReverts locals imms evm a input hg ha hp hd)))

end Benchmarks.UniswapV3.Pool
