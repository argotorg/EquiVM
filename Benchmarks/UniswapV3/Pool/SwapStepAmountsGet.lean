import Benchmarks.UniswapV3.Pool.SwapStepAmountsSource

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.UniswapV3.Pool
set_option maxRecDepth 1000

theorem swapStepInitialExtraGet (imms : Store) (a : SwapStepArgs) (input : Bool) :
    (swapStepInitialFrame imms a input).locals.get? "feePips" =
      some (.int (Int.ofNat a.fee.toNat)) ∧
    (swapStepInitialFrame imms a input).locals.get? "feeAmount" = some (.int 0) := by
  constructor
  all_goals
    cases input <;> cases hz : swapStepZeroForOne a <;>
      simp only [swapStepInitialFrame, swapStepInitialChosenFrame, swapStepInitialCallFrame,
        swapStepInitialZeroFrame, swapStepInitialBaseFrame, swapStepBudgetFrame,
        swapStepInitialCallName, swapStepInitialCondName, swapStepAmountName, hz,
        Bool.false_eq_true, if_false, if_true, Std.HashMap.get?_eq_getElem?,
        Std.HashMap.getElem?_insert]
  all_goals swap_step_get

macro "swap_step_amounts_preserve" : tactic => `(tactic| (
  dsimp only [swapStepAmountsFrame, swapStepAmountInFrame, swapStepCalcFrame]
  rw [swapStepRecalcGet_other _ _ _ _ (by swap_step_recalc_name)
    (by swap_step_recalc_name) (by swap_step_recalc_name)]
  rw [swapStepRecalcGet_other _ _ _ _ (by swap_step_recalc_name)
    (by swap_step_recalc_name) (by swap_step_recalc_name)]
  simp only [swapStepMaxFrame, Std.HashMap.get?_eq_getElem?, Std.HashMap.getElem?_insert]
  rw [← Std.HashMap.get?_eq_getElem?, swapStepPriceGet_other _ _ _ _ rfl rfl rfl]))

theorem swapStepAmountsExtraGet (imms : Store) (a : SwapStepArgs) :
    (swapStepAmountsFrame imms a).locals.get? "amountRemaining" = some (.int a.remaining) ∧
    (swapStepAmountsFrame imms a).locals.get? "feePips" =
      some (.int (Int.ofNat a.fee.toNat)) ∧
    (swapStepAmountsFrame imms a).locals.get? "sqrtRatioTargetX96" =
      some (.int (Int.ofNat a.target.toNat)) ∧
    (swapStepAmountsFrame imms a).locals.get? "feeAmount" = some (.int 0) := by
  repeat' apply And.intro
  · swap_step_amounts_preserve
    exact (swapStepInitialGet imms a _).2.2.2.1
  · swap_step_amounts_preserve
    exact (swapStepInitialExtraGet imms a _).1
  · swap_step_amounts_preserve
    exact (swapStepInitialGet imms a _).2.1
  · swap_step_amounts_preserve
    exact (swapStepInitialExtraGet imms a _).2

end Benchmarks.UniswapV3.Pool
