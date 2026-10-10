import Benchmarks.UniswapV3.Pool.SwapStepInitialModel

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.UniswapV3.Pool
set_option maxRecDepth 1000

theorem swapStepInitialGet (imms : Store) (a : SwapStepArgs) (input : Bool) :
    (swapStepInitialFrame imms a input).locals.get? "sqrtRatioCurrentX96" =
      some (.int (Int.ofNat a.current.toNat)) ∧
    (swapStepInitialFrame imms a input).locals.get? "sqrtRatioTargetX96" =
      some (.int (Int.ofNat a.target.toNat)) ∧
    (swapStepInitialFrame imms a input).locals.get? "liquidity" =
      some (.int (Int.ofNat a.liquidity.toNat)) ∧
    (swapStepInitialFrame imms a input).locals.get? "amountRemaining" = some (.int a.remaining) ∧
    (swapStepInitialFrame imms a input).locals.get? "zeroForOne" =
      some (.bool (swapStepZeroForOne a)) ∧
    (swapStepInitialFrame imms a input).locals.get? "sqrtRatioNextX96" = some (.int 0) := by
  repeat' apply And.intro
  all_goals
    cases input <;> cases hz : swapStepZeroForOne a <;>
      simp only [swapStepInitialFrame, swapStepInitialChosenFrame, swapStepInitialCallFrame,
        swapStepInitialZeroFrame, swapStepInitialBaseFrame, swapStepBudgetFrame,
        swapStepReadyFrame, swapStepDirectionFrame, swapStepZeroFrame,
        swapStepFrame, swapStepLocals,
        swapStepInitialCallName, swapStepInitialCondName, swapStepAmountName, hz,
        Bool.false_eq_true, if_false, if_true,
        Std.HashMap.get?_eq_getElem?, Std.HashMap.getElem?_insert]
  all_goals rfl

theorem swapStepInitialBudgetGet (imms : Store) (a : SwapStepArgs) :
    (swapStepInitialFrame imms a true).locals.get? "amountRemainingLessFee" =
      some (.int (Int.ofNat (fullMathResult (EVM.wordOfInt a.remaining)
        (swapStepComplement a) (UInt256.ofNat 1000000)).toNat)) := by
  cases hz : swapStepZeroForOne a <;>
    simp only [swapStepInitialFrame, swapStepInitialChosenFrame, swapStepInitialCallFrame,
      swapStepInitialCallName, swapStepInitialCondName, swapStepAmountName, hz,
      Bool.false_eq_true, if_false, if_true,
      Std.HashMap.get?_eq_getElem?, Std.HashMap.getElem?_insert]
  all_goals swap_step_initial_get

theorem swapStepInitialAmountGet (imms : Store) (a : SwapStepArgs) (input : Bool) :
    (swapStepInitialFrame imms a input).locals.get? (swapStepAmountName input) =
      some (.int (Int.ofNat (swapStepInitialAmount a input).toNat)) :=
  Std.HashMap.getElem?_insert_self

end Benchmarks.UniswapV3.Pool
