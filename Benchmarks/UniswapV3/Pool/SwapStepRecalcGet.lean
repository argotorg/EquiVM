import Benchmarks.UniswapV3.Pool.SwapStepRecalcModel

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.UniswapV3.Pool
set_option maxRecDepth 1000

theorem swapStepRecalcZeroGet_other (locals : Store) (a : SwapStepArgs) (input : Bool)
    (name : Ident) (h : (swapStepRecalcCondName a input == name) = false) :
    (swapStepRecalcZeroLocals locals a input).get? name = locals.get? name := by
  simp only [swapStepRecalcZeroLocals, Std.HashMap.get?_eq_getElem?,
    Std.HashMap.getElem?_insert, h, Bool.false_eq_true, if_false]

theorem swapStepRecalcGet_other (locals : Store) (a : SwapStepArgs) (input : Bool)
    (name : Ident) (hc : (swapStepRecalcCondName a input == name) = false)
    (hr : (swapStepRecalcCallName a input == name) = false)
    (ha : (swapStepAmountName input == name) = false) :
    (swapStepRecalcLocals locals a input).get? name = locals.get? name := by
  cases hk : swapStepKeep a input <;>
    simp only [swapStepRecalcLocals, swapStepRecalcChosenLocals, swapStepRecalcCallLocals,
      swapStepRecalcZeroLocals, hk, Bool.false_eq_true, if_false, if_true,
      Std.HashMap.get?_eq_getElem?, Std.HashMap.getElem?_insert, hc, hr, ha]

macro "swap_step_recalc_name" : tactic => `(tactic| (
  simp only [swapStepRecalcCondName, swapStepRecalcCallName, swapStepAmountName]
  split_ifs <;> rfl))

theorem swapStepRecalcZeroGet (locals : Store) (a : SwapStepArgs) (input : Bool)
    (hg : SwapStepCalcGet locals a) :
    SwapStepCalcGet (swapStepRecalcZeroLocals locals a input) a := by
  constructor
  · rw [swapStepRecalcZeroGet_other _ _ _ _ (by swap_step_recalc_name)]
    exact hg.current
  · rw [swapStepRecalcZeroGet_other _ _ _ _ (by swap_step_recalc_name)]
    exact hg.price
  · rw [swapStepRecalcZeroGet_other _ _ _ _ (by swap_step_recalc_name)]
    exact hg.liquidity
  · rw [swapStepRecalcZeroGet_other _ _ _ _ (by swap_step_recalc_name)]
    exact hg.max
  · rw [swapStepRecalcZeroGet_other _ _ _ _ (by swap_step_recalc_name)]
    exact hg.exactIn

theorem swapStepRecalcGet (locals : Store) (a : SwapStepArgs) (input : Bool)
    (hg : SwapStepCalcGet locals a) : SwapStepCalcGet (swapStepRecalcLocals locals a input) a := by
  constructor
  · rw [swapStepRecalcGet_other _ _ _ _ (by swap_step_recalc_name)
      (by swap_step_recalc_name) (by swap_step_recalc_name)]
    exact hg.current
  · rw [swapStepRecalcGet_other _ _ _ _ (by swap_step_recalc_name)
      (by swap_step_recalc_name) (by swap_step_recalc_name)]
    exact hg.price
  · rw [swapStepRecalcGet_other _ _ _ _ (by swap_step_recalc_name)
      (by swap_step_recalc_name) (by swap_step_recalc_name)]
    exact hg.liquidity
  · rw [swapStepRecalcGet_other _ _ _ _ (by swap_step_recalc_name)
      (by swap_step_recalc_name) (by swap_step_recalc_name)]
    exact hg.max
  · rw [swapStepRecalcGet_other _ _ _ _ (by swap_step_recalc_name)
      (by swap_step_recalc_name) (by swap_step_recalc_name)]
    exact hg.exactIn

theorem evalSwapStepRecalcTest (frame : Frame) (evm : EVM.State) (a : SwapStepArgs)
    (input : Bool) (hg : SwapStepCalcGet frame.locals a) :
    evalExpr? config frame evm (swapStepRecalcTest input) =
      .ok (.bool (swapStepKeep a input)) := by
  have hm := evalExpr_var_get (cfg := config) (frame := frame) (evm := evm) hg.max
  have hi := evalExpr_var_get (cfg := config) (frame := frame) (evm := evm) hg.exactIn
  cases input <;> cases hx : swapStepMax a <;> cases he : swapStepExactIn a <;>
    simp only [swapStepRecalcTest, Bool.false_eq_true, if_false, if_true, evalExpr?, hm, hi,
      hx, he, bind, EvalResult.bind, pure, evalUnaryOp?, EvalResult.ofOption, swapStepKeep,
      Bool.not_false, Bool.not_true, Bool.and_self, Bool.and_false, Bool.and_true]

end Benchmarks.UniswapV3.Pool
