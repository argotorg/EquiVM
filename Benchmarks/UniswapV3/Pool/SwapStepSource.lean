import Benchmarks.UniswapV3.Pool.SwapStepFeeSource

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.UniswapV3.Pool
set_option maxRecDepth 1000

theorem swapStepResultGet_other (imms : Store) (a : SwapStepArgs) (name : Ident)
    (hf : ("feeAmount" == name) = false) (hc : ("__c17" == name) = false) :
    (swapStepResultFrame imms a).locals.get? name = (swapStepCapFrame imms a).locals.get? name := by
  cases hu : swapStepUnusedFee a <;>
    simp only [swapStepResultFrame, swapStepFeeCallFrame, hu, Bool.false_eq_true, if_false,
      if_true, Std.HashMap.get?_eq_getElem?, Std.HashMap.getElem?_insert, hf, hc]

theorem swapStepResultGet (imms : Store) (a : SwapStepArgs) :
    (swapStepResultFrame imms a).locals.get? "sqrtRatioNextX96" =
      some (.int (Int.ofNat (swapStepPrice a).toNat)) ∧
    (swapStepResultFrame imms a).locals.get? "amountIn" =
      some (.int (Int.ofNat (swapStepAmount a true).toNat)) ∧
    (swapStepResultFrame imms a).locals.get? "amountOut" =
      some (.int (Int.ofNat (swapStepOutput a).toNat)) ∧
    (swapStepResultFrame imms a).locals.get? "feeAmount" =
      some (.int (Int.ofNat (swapStepFee a).toNat)) := by
  repeat' apply And.intro
  · rw [swapStepResultGet_other imms a _ rfl rfl]
    exact (swapStepCapCalcGet imms a).price
  · rw [swapStepResultGet_other imms a _ rfl rfl]
    exact (swapStepCapAmountsGet imms a).1
  · rw [swapStepResultGet_other imms a _ rfl rfl]
    exact (swapStepCapAmountsGet imms a).2
  · exact Std.HashMap.getElem?_insert_self

theorem swapStepReturns (imms : Store) (evm : EVM.State) (a : SwapStepArgs)
    (ha : a.Fits) (hv : swapStepValid a) :
    ExecFuncBody config (swapStepFrame imms a) evm swapStepFunction.body
      (.returned (swapStepResultFrame imms a) evm (some (swapStepResults a))) := by
  apply ExecFuncBody.execBlockRet
  rw [← List.take_append_drop 10 swapStepFunction.body]
  apply execBlock_append_ok (swapStepCapPrefixSource imms evm a ha hv.1)
  refine ExecBlock.consNormal (swapStepFeeSource imms evm a hv.2)
    (ExecBlock.consReturn (ExecStmt.return ?_))
  have hg := swapStepResultGet imms a
  have hp := evalExpr_var_get (cfg := config) (evm := evm) hg.1
  have hi := evalExpr_var_get (cfg := config) (evm := evm) hg.2.1
  have ho := evalExpr_var_get (cfg := config) (evm := evm) hg.2.2.1
  have hf := evalExpr_var_get (cfg := config) (evm := evm) hg.2.2.2
  simp only [evalExprs?, hp, hi, ho, hf, bind, EvalResult.bind, pure, swapStepResults]

theorem swapStepReverts (imms : Store) (evm : EVM.State) (a : SwapStepArgs)
    (ha : a.Fits) (hv : ¬swapStepValid a) :
    ExecFuncBody config (swapStepFrame imms a) evm swapStepFunction.body .reverted := by
  classical
  by_cases hm : swapStepAmountsValid a
  · apply ExecFuncBody.execBlockRevert
    rw [← List.take_append_drop 10 swapStepFunction.body]
    exact execBlock_append_ok (swapStepCapPrefixSource imms evm a ha hm)
      (ExecBlock.consRevert (swapStepFeeReverts imms evm a (fun h ↦ hv ⟨hm, h⟩)))
  · exact swapStepAmountsReverts imms evm a ha hm

end Benchmarks.UniswapV3.Pool
