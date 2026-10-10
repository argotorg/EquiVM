import Benchmarks.UniswapV3.Pool.SwapStepInitialSource

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.UniswapV3.Pool
set_option maxRecDepth 1000

theorem swapStepInitialCallReverts (imms : Store) (evm : EVM.State) (a : SwapStepArgs)
    (input : Bool) (ha : a.Fits)
    (hv : ¬amountDeltaValid (swapStepDeltaOne a input) (swapStepDeltaArgs a a.target input)) :
    ExecStmt config (swapStepInitialZeroFrame imms a input) evm
      (.internalCall (amountDeltaName (swapStepDeltaOne a input))
        (swapStepDeltaCallArgs a input "sqrtRatioTargetX96") (swapStepInitialCallName a input))
      .reverted := by
  have hg := swapStepInitialZeroGet imms a input
  exact swapStepDeltaCallReverts _ imms evm a a.target input "sqrtRatioTargetX96"
    (swapStepInitialCallName a input) hg.1 hg.2.1 hg.2.2.1
    (swapStepDeltaArgs_fits a a.target input ha ha.2.1) hv

theorem swapStepInitialChoiceReverts (imms : Store) (evm : EVM.State) (a : SwapStepArgs)
    (input : Bool) (ha : a.Fits)
    (hv : ¬amountDeltaValid (swapStepDeltaOne a input) (swapStepDeltaArgs a a.target input)) :
    ExecStmt config (swapStepInitialZeroFrame imms a input) evm
      ((swapStepPriceBranch input)[if input then 2 else 1]!) .reverted := by
  have he := evalExpr_var_get (cfg := config) (evm := evm)
    (swapStepInitialZeroGet imms a input).2.2.2.1
  have hc := swapStepInitialCallReverts imms evm a input ha hv
  cases hz : swapStepZeroForOne a
  · cases input <;> apply ExecStmt.iteFalse (by simpa only [hz] using he)
    all_goals
      apply ExecBlock.consRevert
      simpa only [swapStepDeltaOne, swapStepDeltaCallArgs, swapStepInitialCallName,
        amountDeltaName, hz, Bool.not_false, Bool.false_eq_true, if_false, if_true] using hc
  · cases input <;> apply ExecStmt.iteTrue (by simpa only [hz] using he)
    all_goals
      apply ExecBlock.consRevert
      simpa only [swapStepDeltaOne, swapStepDeltaCallArgs, swapStepInitialCallName,
        amountDeltaName, hz, Bool.not_true, Bool.false_eq_true, if_false, if_true] using hc

theorem swapStepInitialBranchReverts (imms : Store) (evm : EVM.State) (a : SwapStepArgs)
    (input : Bool) (ha : a.Fits)
    (hb : if input then fullMathValid (EVM.wordOfInt a.remaining) (swapStepComplement a)
      (UInt256.ofNat 1000000) else True)
    (hv : ¬amountDeltaValid (swapStepDeltaOne a input) (swapStepDeltaArgs a a.target input)) :
    ExecBlock config (swapStepReadyFrame imms a) evm (swapStepPriceBranch input) .reverted := by
  rw [← List.take_append_drop (if input then 2 else 1) (swapStepPriceBranch input)]
  apply execBlock_append_ok (swapStepInitialPrefix imms evm a input hb)
  have hc := swapStepInitialChoiceReverts imms evm a input ha hv
  cases input <;> exact ExecBlock.consRevert hc

theorem swapStepBudgetFunctionReverts (imms : Store) (evm : EVM.State) (a : SwapStepArgs)
    (hv : ¬swapStepBudgetValid a) :
    ExecFuncBody config (swapStepFrame imms a) evm swapStepFunction.body .reverted := by
  have hi : swapStepExactIn a = true := by
    cases h : swapStepExactIn a
    · exact False.elim (hv (by simp only [swapStepBudgetValid, h, Bool.false_eq_true, if_false]))
    · rfl
  have hb : ¬fullMathValid (EVM.wordOfInt a.remaining) (swapStepComplement a)
      (UInt256.ofNat 1000000) := by simpa only [swapStepBudgetValid, hi, if_true] using hv
  have he := evalExpr_var_get (cfg := config) (evm := evm) (swapStepReadyGet imms a).2.2.2.2.2.2
  apply ExecFuncBody.execBlockRevert
  rw [← List.take_append_drop 6 swapStepFunction.body]
  apply execBlock_append_ok (swapStepPrefixSource imms evm a)
  apply ExecBlock.consRevert
  apply ExecStmt.iteTrue (by simpa only [hi] using he)
  exact ExecBlock.consRevert (swapStepBudgetReverts imms evm a hb)

theorem swapStepInitialFunctionReverts (imms : Store) (evm : EVM.State) (a : SwapStepArgs)
    (ha : a.Fits) (hb : swapStepBudgetValid a) (hv : ¬swapStepInitialValid a) :
    ExecFuncBody config (swapStepFrame imms a) evm swapStepFunction.body .reverted := by
  have he := evalExpr_var_get (cfg := config) (evm := evm) (swapStepReadyGet imms a).2.2.2.2.2.2
  have hr := swapStepInitialBranchReverts imms evm a (swapStepExactIn a) ha hb hv
  apply ExecFuncBody.execBlockRevert
  rw [← List.take_append_drop 6 swapStepFunction.body]
  apply execBlock_append_ok (swapStepPrefixSource imms evm a)
  apply ExecBlock.consRevert
  cases hi : swapStepExactIn a
  · exact ExecStmt.iteFalse (by simpa only [hi] using he) (by simpa only [hi] using hr)
  · exact ExecStmt.iteTrue (by simpa only [hi] using he) (by simpa only [hi] using hr)

end Benchmarks.UniswapV3.Pool
