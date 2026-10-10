import Benchmarks.UniswapV3.Pool.SwapStepBudgetSource
import Benchmarks.UniswapV3.Pool.SwapStepDeltaCalls

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.UniswapV3.Pool
set_option maxRecDepth 1000

def swapStepInitialCondName (input : Bool) : Ident := if input then "__cond3" else "__cond7"

def swapStepInitialCallName (a : SwapStepArgs) (input : Bool) : Ident :=
  if input then (if swapStepZeroForOne a then "__c1" else "__c2")
  else (if swapStepZeroForOne a then "__c5" else "__c6")

def swapStepAmountName (input : Bool) : Ident := if input then "amountIn" else "amountOut"

noncomputable def swapStepInitialAmount (a : SwapStepArgs) (input : Bool) : UInt256 :=
  amountDeltaResult (swapStepDeltaOne a input) (swapStepDeltaArgs a a.target input)

noncomputable def swapStepInitialBaseFrame (imms : Store) (a : SwapStepArgs) (input : Bool) :
    Frame :=
  {contract := contract
   immutables := imms
   locals := if input then (swapStepBudgetFrame imms a).locals
     else (swapStepReadyFrame imms a).locals}

noncomputable def swapStepInitialZeroFrame (imms : Store) (a : SwapStepArgs) (input : Bool) :
    Frame :=
  {swapStepInitialBaseFrame imms a input with
    locals := (swapStepInitialBaseFrame imms a input).locals.insert
      (swapStepInitialCondName input) (.int 0)}

noncomputable def swapStepInitialCallFrame (imms : Store) (a : SwapStepArgs) (input : Bool) :
    Frame :=
  {swapStepInitialZeroFrame imms a input with
    locals := (swapStepInitialZeroFrame imms a input).locals.insert
      (swapStepInitialCallName a input) (.int (Int.ofNat (swapStepInitialAmount a input).toNat))}

noncomputable def swapStepInitialChosenFrame (imms : Store) (a : SwapStepArgs) (input : Bool) :
    Frame :=
  {swapStepInitialCallFrame imms a input with
    locals := (swapStepInitialCallFrame imms a input).locals.insert
      (swapStepInitialCondName input) (.int (Int.ofNat (swapStepInitialAmount a input).toNat))}

noncomputable def swapStepInitialFrame (imms : Store) (a : SwapStepArgs) (input : Bool) : Frame :=
  {swapStepInitialChosenFrame imms a input with
    locals := (swapStepInitialChosenFrame imms a input).locals.insert
      (swapStepAmountName input) (.int (Int.ofNat (swapStepInitialAmount a input).toNat))}

macro "swap_step_initial_get" : tactic => `(tactic| (
  simp only [swapStepInitialFrame, swapStepInitialChosenFrame, swapStepInitialCallFrame,
    swapStepInitialZeroFrame, swapStepInitialBaseFrame, swapStepBudgetFrame,
    swapStepInitialCondName, swapStepInitialCallName, swapStepAmountName,
    Bool.false_eq_true, if_false, if_true,
    Std.HashMap.get?_eq_getElem?, Std.HashMap.getElem?_insert]
  swap_step_get))

theorem swapStepInitialZeroGet (imms : Store) (a : SwapStepArgs) (input : Bool) :
    (swapStepInitialZeroFrame imms a input).locals.get? "sqrtRatioCurrentX96" =
      some (.int (Int.ofNat a.current.toNat)) ∧
    (swapStepInitialZeroFrame imms a input).locals.get? "sqrtRatioTargetX96" =
      some (.int (Int.ofNat a.target.toNat)) ∧
    (swapStepInitialZeroFrame imms a input).locals.get? "liquidity" =
      some (.int (Int.ofNat a.liquidity.toNat)) ∧
    (swapStepInitialZeroFrame imms a input).locals.get? "zeroForOne" =
      some (.bool (swapStepZeroForOne a)) ∧
    (swapStepInitialZeroFrame imms a input).locals.get? (swapStepInitialCondName input) =
      some (.int 0) := by
  repeat' apply And.intro
  all_goals cases input <;> swap_step_initial_get

end Benchmarks.UniswapV3.Pool
