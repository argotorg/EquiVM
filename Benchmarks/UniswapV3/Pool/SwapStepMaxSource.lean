import Benchmarks.UniswapV3.Pool.SwapStepRecalcModel

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.UniswapV3.Pool
set_option maxRecDepth 1000

theorem swapStepPriceGet_other (imms : Store) (a : SwapStepArgs) (input : Bool) (name : Ident)
    (hp : ("sqrtRatioNextX96" == name) = false) (h4 : ("__c4" == name) = false)
    (h8 : ("__c8" == name) = false) :
    (swapStepPriceFrame imms a input).locals.get? name =
      (swapStepInitialFrame imms a input).locals.get? name := by
  cases hr : swapStepReachTarget a <;> cases input <;>
    simp only [swapStepPriceFrame, swapStepPriceCallFrame, swapStepPriceCallName, hr,
      Bool.false_eq_true, if_false, if_true, Std.HashMap.get?_eq_getElem?,
      Std.HashMap.getElem?_insert, hp, h4, h8]

theorem swapStepInitialExactGet (imms : Store) (a : SwapStepArgs) (input : Bool) :
    (swapStepInitialFrame imms a input).locals.get? "exactIn" =
      some (.bool (swapStepExactIn a)) := by
  cases input <;> cases hz : swapStepZeroForOne a <;>
    simp only [swapStepInitialFrame, swapStepInitialChosenFrame, swapStepInitialCallFrame,
      swapStepInitialZeroFrame, swapStepInitialBaseFrame, swapStepBudgetFrame,
      swapStepInitialCallName, swapStepInitialCondName, swapStepAmountName, hz,
      Bool.false_eq_true, if_false, if_true, Std.HashMap.get?_eq_getElem?,
      Std.HashMap.getElem?_insert]
  all_goals swap_step_get

theorem swapStepInitialOtherAmountGet (imms : Store) (a : SwapStepArgs) (input : Bool) :
    (swapStepInitialFrame imms a input).locals.get? (swapStepAmountName (!input)) =
      some (.int 0) := by
  cases input <;> cases hz : swapStepZeroForOne a <;>
    simp only [swapStepInitialFrame, swapStepInitialChosenFrame, swapStepInitialCallFrame,
      swapStepInitialZeroFrame, swapStepInitialBaseFrame, swapStepBudgetFrame,
      swapStepInitialCallName, swapStepInitialCondName, swapStepAmountName, hz,
      Bool.not_false, Bool.not_true, Bool.false_eq_true, if_false, if_true,
      Std.HashMap.get?_eq_getElem?, Std.HashMap.getElem?_insert]
  all_goals swap_step_get

theorem swapStepPriceAmountGet (imms : Store) (a : SwapStepArgs) (input : Bool) :
    (swapStepPriceFrame imms a (swapStepExactIn a)).locals.get? (swapStepAmountName input) =
      some (.int (Int.ofNat (swapStepBeforeAmount a input).toNat)) := by
  rw [swapStepPriceGet_other imms a (swapStepExactIn a) (swapStepAmountName input)
    (by cases input <;> rfl) (by cases input <;> rfl) (by cases input <;> rfl)]
  by_cases hi : swapStepExactIn a = input
  · simpa only [swapStepBeforeAmount, hi, if_pos rfl, swapStepInitialDelta,
      swapStepInitialAmount] using swapStepInitialAmountGet imms a input
  · have ho : input = !(swapStepExactIn a) := by
      cases input <;> cases h : swapStepExactIn a <;> simp_all
    simp only [swapStepBeforeAmount, if_neg hi]
    rw [ho]
    exact swapStepInitialOtherAmountGet imms a (swapStepExactIn a)

theorem swapStepMaxSource (imms : Store) (evm : EVM.State) (a : SwapStepArgs) :
    ExecStmt config (swapStepPriceFrame imms a (swapStepExactIn a)) evm
      swapStepFunction.body[7]! (.ok (swapStepMaxFrame imms a) evm) := by
  have ht : (swapStepPriceFrame imms a (swapStepExactIn a)).locals.get? "sqrtRatioTargetX96" =
      some (.int (Int.ofNat a.target.toNat)) := by
    rw [swapStepPriceGet_other imms a _ "sqrtRatioTargetX96" rfl rfl rfl]
    exact (swapStepInitialGet imms a _).2.1
  have et := evalExpr_var_get (cfg := config) (evm := evm) ht
  have ep := evalExpr_var_get (cfg := config) (evm := evm)
    (frame := swapStepPriceFrame imms a (swapStepExactIn a))
    (name := "sqrtRatioNextX96")
    (value := .int (Int.ofNat (swapStepPrice a).toNat)) Std.HashMap.getElem?_insert_self
  apply ExecStmt.letDecl
  change evalExpr? config _ evm (.binary .eq (.var "sqrtRatioTargetX96")
    (.var "sqrtRatioNextX96")) = _
  simp only [evalExpr?, et, ep, evalBinaryOp?, bind, EvalResult.bind, swapStepMax]
  apply congrArg (fun b : Bool ↦ EvalResult.ok (Value.bool b))
  apply Bool.eq_iff_iff.mpr
  simp only [beq_iff_eq, Value.int.injEq, decide_eq_true_eq, Int.ofNat_eq_natCast]
  omega

theorem swapStepMaxGet (imms : Store) (a : SwapStepArgs) :
    SwapStepCalcGet (swapStepMaxFrame imms a).locals a := by
  constructor
  · simp only [swapStepMaxFrame, Std.HashMap.get?_eq_getElem?, Std.HashMap.getElem?_insert]
    rw [← Std.HashMap.get?_eq_getElem?, swapStepPriceGet_other imms a _ _ rfl rfl rfl]
    exact (swapStepInitialGet imms a _).1
  · exact by
      simp only [swapStepMaxFrame, swapStepPriceFrame, Std.HashMap.get?_eq_getElem?,
        Std.HashMap.getElem?_insert]
      rfl
  · simp only [swapStepMaxFrame, Std.HashMap.get?_eq_getElem?, Std.HashMap.getElem?_insert]
    rw [← Std.HashMap.get?_eq_getElem?, swapStepPriceGet_other imms a _ _ rfl rfl rfl]
    exact (swapStepInitialGet imms a _).2.2.1
  · exact Std.HashMap.getElem?_insert_self
  · simp only [swapStepMaxFrame, Std.HashMap.get?_eq_getElem?, Std.HashMap.getElem?_insert]
    rw [← Std.HashMap.get?_eq_getElem?, swapStepPriceGet_other imms a _ _ rfl rfl rfl]
    exact swapStepInitialExactGet imms a _

theorem swapStepMaxAmountGet (imms : Store) (a : SwapStepArgs) (input : Bool) :
    (swapStepMaxFrame imms a).locals.get? (swapStepAmountName input) =
      some (.int (Int.ofNat (swapStepBeforeAmount a input).toNat)) := by
  have h := swapStepPriceAmountGet imms a input
  cases input <;> simpa only [swapStepMaxFrame, swapStepAmountName, Bool.false_eq_true,
    if_false, if_true, Std.HashMap.get?_eq_getElem?, Std.HashMap.getElem?_insert] using h

theorem swapStepMaxPrefixSource (imms : Store) (evm : EVM.State) (a : SwapStepArgs)
    (ha : a.Fits) (hv : swapStepPriceValid a) :
    ExecBlock config (swapStepFrame imms a) evm (swapStepFunction.body.take 8)
      (.ok (swapStepMaxFrame imms a) evm) :=
  execBlock_append_ok (swapStepPriceSource imms evm a ha hv)
    (ExecBlock.consNormal (swapStepMaxSource imms evm a) ExecBlock.nil)

end Benchmarks.UniswapV3.Pool
