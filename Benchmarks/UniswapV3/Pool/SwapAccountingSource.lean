import Benchmarks.UniswapV3.Pool.SwapAccountingModel

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.UniswapV3.Pool
set_option maxRecDepth 10000

theorem evalSwapAccountingSum {frame : Frame} {evm : EVM.State} (d : SwapIterationData)
    (hd : frame.locals.get? "step" = some d.value) :
    evalExpr? config frame evm swapAccountingSumExpr =
      .ok (.int (Int.ofNat (d.amountIn + d.feeAmount).toNat)) := by
  have he := evalExpr_var_get (cfg := config) (evm := evm) hd
  exact evalExpr_word_add (evalExpr_structField (name := "amountIn") he rfl)
    (evalExpr_structField (name := "feeAmount") he rfl)

theorem evalSwapAccountingFirstArgs {frame : Frame} {evm : EVM.State}
    (exactInput : Bool) (d : SwapIterationData)
    (hd : frame.locals.get? "step" = some d.value) :
    evalExprs? config frame evm (swapAccountingFirstArgs exactInput) =
      .ok [.int (Int.ofNat (swapAccountingFirst exactInput d).toNat)] := by
  have hsum := evalSwapAccountingSum (evm := evm) d hd
  have hout := evalExpr_structField (name := "amountOut")
    (evalExpr_var_get (cfg := config) (evm := evm) hd) rfl
  cases exactInput <;> simp only [swapAccountingFirstArgs, swapAccountingFirst,
    Bool.false_eq_true, if_false, if_true, evalExprs?, hsum, hout, bind, EvalResult.bind, pure]

theorem evalSwapAccountingSecondArgs {frame : Frame} {evm : EVM.State}
    (exactInput : Bool) (d : SwapIterationData)
    (hd : frame.locals.get? "step" = some d.value) :
    evalExprs? config frame evm (swapAccountingSecondArgs exactInput) =
      .ok [.int (Int.ofNat (swapAccountingSecond exactInput d).toNat)] :=
  evalSwapAccountingFirstArgs (!exactInput) d hd

theorem swapAccountingRemainingSource {frame : Frame} {evm : EVM.State}
    (exactInput : Bool) (s : SwapStateData) (d : SwapIterationData)
    (hs : frame.locals.get? "state" = some s.value)
    (hr : frame.locals.get? (swapAccountingFirstName exactInput) =
      some (.int (Int.ofNat (swapAccountingFirst exactInput d).toNat))) :
    ExecStmt config frame evm (swapAccountingBody exactInput)[1]!
      (.ok (swapStateFrame frame {s with remaining := swapAccountingRemaining exactInput s d})
        evm) := by
  have hstate := evalExpr_structField (name := "amountSpecifiedRemaining")
    (evalExpr_var_get (cfg := config) (evm := evm) hs) rfl
  have hvalue := evalExpr_var_get (cfg := config) (evm := evm) hr
  cases exactInput
  all_goals
    simp only [swapAccountingFirstName, Bool.false_eq_true, if_false, if_true] at hvalue
    apply ExecStmt.assign (value := .int (swapAccountingRemaining _ s d)) ?_
      (assignLocalField_frame hs rfl rfl)
    simp only [evalExpr?, hstate, hvalue, bind, EvalResult.bind, evalBinaryOp?, castValue?,
      EvalResult.ofOption, swapAccountingRemaining, safeSignedMathResult,
      Bool.false_eq_true, if_false, if_true]

theorem evalSwapAccountingMathArgs {frame : Frame} {evm : EVM.State}
    (exactInput : Bool) (s : SwapStateData) (d : SwapIterationData)
    (hs : frame.locals.get? "state" = some s.value)
    (hr : frame.locals.get? (swapAccountingSecondName exactInput) =
      some (.int (Int.ofNat (swapAccountingSecond exactInput d).toNat))) :
    evalExprs? config frame evm (swapAccountingMathArgs exactInput) =
      .ok [.int s.calculated, .int (Int.ofNat (swapAccountingSecond exactInput d).toNat)] := by
  have hcalc := evalExpr_structField (name := "amountCalculated")
    (evalExpr_var_get (cfg := config) (evm := evm) hs) rfl
  have hvalue := evalExpr_var_get (cfg := config) (evm := evm) hr
  simp only [swapAccountingMathArgs, evalExprs?, hcalc, hvalue, bind, EvalResult.bind, pure]

theorem swapAccountingCalculatedSource {frame : Frame} {evm : EVM.State}
    (exactInput : Bool) (s : SwapStateData) (value : Int)
    (hs : frame.locals.get? "state" = some s.value)
    (hr : frame.locals.get? (swapAccountingResultName exactInput) = some (.int value)) :
    ExecStmt config frame evm (swapAccountingBody exactInput)[4]!
      (.ok (swapStateFrame frame {s with calculated := value}) evm) := by
  cases exactInput <;>
    exact ExecStmt.assign (evalExpr_var_get hr) (assignLocalField_frame hs rfl rfl)

end Benchmarks.UniswapV3.Pool
