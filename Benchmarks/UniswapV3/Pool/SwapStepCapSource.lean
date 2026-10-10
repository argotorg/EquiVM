import Benchmarks.UniswapV3.Pool.SwapStepFinishModel
import Benchmarks.UniswapV3.Pool.SwapStepAmountsGet

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.UniswapV3.Pool
set_option maxRecDepth 1000

def swapStepCapTest : Expr :=
  .binary .and (.unary .not (.var "exactIn"))
    (.binary .gt (.var "amountOut") swapStepAbsExpr)

theorem evalSwapStepCapTest (imms : Store) (evm : EVM.State) (a : SwapStepArgs) :
    evalExpr? config (swapStepAmountsFrame imms a) evm swapStepCapTest =
      .ok (.bool (swapStepCap a)) := by
  have hi := evalExpr_var_get (cfg := config) (evm := evm)
    (swapStepAmountsGet imms a).exactIn
  have ho := evalExpr_var_get (cfg := config) (evm := evm)
    (swapStepAmountsAmountGet imms a).2
  have ha := evalSwapStepAbs (swapStepAmountsFrame imms a) evm a
    (swapStepAmountsExtraGet imms a).1
  have ht : evalExpr? config (swapStepAmountsFrame imms a) evm
      (.binary .gt (.var "amountOut") swapStepAbsExpr) =
      .ok (.bool (decide ((swapStepAbsRemaining a).toNat < (swapStepAmount a false).toNat))) := by
    simp only [evalExpr?, ho, ha, evalBinaryOp?, bind, EvalResult.bind]
    apply congrArg (fun b : Bool ↦ EvalResult.ok (Value.bool b))
    apply Bool.eq_iff_iff.mpr
    simp only [decide_eq_true_eq]
    exact Int.ofNat_lt
  cases he : swapStepExactIn a <;>
    simp only [swapStepCapTest, evalExpr?, hi, ht, he, evalUnaryOp?, bind, EvalResult.bind,
      pure, EvalResult.ofOption, swapStepCap, Bool.not_false, Bool.not_true,
      Bool.true_and, Bool.false_and]

theorem swapStepCapSource (imms : Store) (evm : EVM.State) (a : SwapStepArgs) :
    ExecStmt config (swapStepAmountsFrame imms a) evm swapStepFunction.body[9]!
      (.ok (swapStepCapFrame imms a) evm) := by
  have he := evalSwapStepCapTest imms evm a
  cases hc : swapStepCap a
  · simp only [swapStepCapFrame, hc, Bool.false_eq_true, if_false]
    exact ExecStmt.iteFalse (by simpa only [hc] using he) ExecBlock.nil
  · simp only [swapStepCapFrame, swapStepOutput, hc, if_true]
    exact ExecStmt.iteTrue (by simpa only [hc] using he)
      (ExecBlock.consNormal
        (ExecStmt.assign (evalSwapStepAbs _ evm a (swapStepAmountsExtraGet imms a).1)
          (assignLocalVarBase_frame (swapStepAmountsAmountGet imms a).2)) ExecBlock.nil)

theorem swapStepCapGet_other (imms : Store) (a : SwapStepArgs) (name : Ident)
    (h : ("amountOut" == name) = false) :
    (swapStepCapFrame imms a).locals.get? name =
      (swapStepAmountsFrame imms a).locals.get? name := by
  cases hc : swapStepCap a <;>
    simp only [swapStepCapFrame, hc, Bool.false_eq_true, if_false, if_true,
      Std.HashMap.get?_eq_getElem?, Std.HashMap.getElem?_insert, h]

theorem swapStepCapCalcGet (imms : Store) (a : SwapStepArgs) :
    SwapStepCalcGet (swapStepCapFrame imms a).locals a := by
  constructor
  · rw [swapStepCapGet_other imms a _ rfl]
    exact (swapStepAmountsGet imms a).current
  · rw [swapStepCapGet_other imms a _ rfl]
    exact (swapStepAmountsGet imms a).price
  · rw [swapStepCapGet_other imms a _ rfl]
    exact (swapStepAmountsGet imms a).liquidity
  · rw [swapStepCapGet_other imms a _ rfl]
    exact (swapStepAmountsGet imms a).max
  · rw [swapStepCapGet_other imms a _ rfl]
    exact (swapStepAmountsGet imms a).exactIn

theorem swapStepCapExtraGet (imms : Store) (a : SwapStepArgs) :
    (swapStepCapFrame imms a).locals.get? "amountRemaining" = some (.int a.remaining) ∧
    (swapStepCapFrame imms a).locals.get? "feePips" = some (.int (Int.ofNat a.fee.toNat)) ∧
    (swapStepCapFrame imms a).locals.get? "sqrtRatioTargetX96" =
      some (.int (Int.ofNat a.target.toNat)) ∧
    (swapStepCapFrame imms a).locals.get? "feeAmount" = some (.int 0) := by
  repeat' apply And.intro
  all_goals rw [swapStepCapGet_other imms a _ rfl]
  · exact (swapStepAmountsExtraGet imms a).1
  · exact (swapStepAmountsExtraGet imms a).2.1
  · exact (swapStepAmountsExtraGet imms a).2.2.1
  · exact (swapStepAmountsExtraGet imms a).2.2.2

theorem swapStepCapAmountsGet (imms : Store) (a : SwapStepArgs) :
    (swapStepCapFrame imms a).locals.get? "amountIn" =
      some (.int (Int.ofNat (swapStepAmount a true).toNat)) ∧
    (swapStepCapFrame imms a).locals.get? "amountOut" =
      some (.int (Int.ofNat (swapStepOutput a).toNat)) := by
  constructor
  · rw [swapStepCapGet_other imms a _ rfl]
    exact (swapStepAmountsAmountGet imms a).1
  · cases hc : swapStepCap a
    · simpa only [swapStepCapFrame, swapStepOutput, hc, Bool.false_eq_true, if_false] using
        (swapStepAmountsAmountGet imms a).2
    · simp only [swapStepCapFrame, hc, if_true]
      exact Std.HashMap.getElem?_insert_self

theorem swapStepCapPrefixSource (imms : Store) (evm : EVM.State) (a : SwapStepArgs)
    (ha : a.Fits) (hv : swapStepAmountsValid a) :
    ExecBlock config (swapStepFrame imms a) evm (swapStepFunction.body.take 10)
      (.ok (swapStepCapFrame imms a) evm) :=
  execBlock_append_ok (swapStepAmountsSource imms evm a ha hv)
    (ExecBlock.consNormal (swapStepCapSource imms evm a) ExecBlock.nil)

end Benchmarks.UniswapV3.Pool
