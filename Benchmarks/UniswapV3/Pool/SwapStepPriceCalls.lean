import Benchmarks.UniswapV3.Pool.SwapStepInitialGet
import Benchmarks.UniswapV3.Pool.NextPriceSource

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.UniswapV3.Pool
set_option maxRecDepth 1000

def swapStepChoiceBudgetExpr (input : Bool) : Expr :=
  if input then .var "amountRemainingLessFee" else swapStepAbsExpr

def swapStepPriceCallArgs (input : Bool) : List Expr :=
  [.var "sqrtRatioCurrentX96", .var "liquidity", swapStepChoiceBudgetExpr input, .var "zeroForOne"]

def swapStepPriceCallName (input : Bool) : Ident := if input then "__c4" else "__c8"

noncomputable def swapStepPriceCallFrame (imms : Store) (a : SwapStepArgs) (input : Bool) : Frame :=
  {swapStepInitialFrame imms a input with
    locals := (swapStepInitialFrame imms a input).locals.insert (swapStepPriceCallName input)
      (.int (Int.ofNat (nextPriceResult input (swapStepNextArgs a)).toNat))}

theorem evalSwapStepChoiceBudget (imms : Store) (evm : EVM.State) (a : SwapStepArgs)
    (input : Bool) (hi : swapStepExactIn a = input) :
    evalExpr? config (swapStepInitialFrame imms a input) evm (swapStepChoiceBudgetExpr input) =
      .ok (.int (Int.ofNat (swapStepBudget a).toNat)) := by
  cases input
  · have he := evalSwapStepAbs (swapStepInitialFrame imms a false) evm a
      (swapStepInitialGet imms a false).2.2.2.1
    simpa only [swapStepChoiceBudgetExpr, swapStepBudget, hi, Bool.false_eq_true, if_false] using he
  · have he := evalExpr_var_get (cfg := config) (evm := evm) (swapStepInitialBudgetGet imms a)
    simpa only [swapStepChoiceBudgetExpr, swapStepBudget, hi, if_true] using he

theorem evalSwapStepPriceArgs (imms : Store) (evm : EVM.State) (a : SwapStepArgs)
    (input : Bool) (hi : swapStepExactIn a = input) :
    evalExprs? config (swapStepInitialFrame imms a input) evm (swapStepPriceCallArgs input) =
      .ok (swapStepNextArgs a).values := by
  have hg := swapStepInitialGet imms a input
  have hc := evalExpr_var_get (cfg := config) (evm := evm) hg.1
  have hl := evalExpr_var_get (cfg := config) (evm := evm) hg.2.2.1
  have hz := evalExpr_var_get (cfg := config) (evm := evm) hg.2.2.2.2.1
  have hb := evalSwapStepChoiceBudget imms evm a input hi
  simp only [swapStepPriceCallArgs, evalExprs?, hc, hl, hz, hb,
    bind, EvalResult.bind, pure, swapStepNextArgs, NextPriceArgs.values]

theorem swapStepPriceCallReturns (imms : Store) (evm : EVM.State) (a : SwapStepArgs)
    (input : Bool) (hi : swapStepExactIn a = input) (ha : a.Fits)
    (hv : nextPriceValid input (swapStepNextArgs a)) :
    ExecStmt config (swapStepInitialFrame imms a input) evm
      (.internalCall (nextPriceName input) (swapStepPriceCallArgs input)
        (swapStepPriceCallName input))
      (.ok (swapStepPriceCallFrame imms a input) evm) := by
  exact internalCallFunctionReturn (callee := nextPriceFunction input)
    (calleeSolm := nextPriceResultFrame imms input (swapStepNextArgs a))
    (locals := nextPriceLocals input (swapStepNextArgs a))
    (value := some [.int (Int.ofNat (nextPriceResult input (swapStepNextArgs a)).toNat)])
    (evalSwapStepPriceArgs imms evm a input hi) (nextPriceLookup input) (nextPriceBind input _)
    (nextPriceReturns imms evm input _ (swapStepNextArgs_fits a ha) hv)

theorem swapStepPriceCallReverts (imms : Store) (evm : EVM.State) (a : SwapStepArgs)
    (input : Bool) (hi : swapStepExactIn a = input)
    (hv : ¬nextPriceValid input (swapStepNextArgs a)) :
    ExecStmt config (swapStepInitialFrame imms a input) evm
      (.internalCall (nextPriceName input) (swapStepPriceCallArgs input)
        (swapStepPriceCallName input))
      .reverted := by
  exact internalCallFunctionRevert (callee := nextPriceFunction input)
    (locals := nextPriceLocals input (swapStepNextArgs a))
    (evalSwapStepPriceArgs imms evm a input hi) (nextPriceLookup input) (nextPriceBind input _)
    (nextPriceReverts imms evm input _ hv)

end Benchmarks.UniswapV3.Pool
