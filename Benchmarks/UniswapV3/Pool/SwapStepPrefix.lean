import Benchmarks.UniswapV3.Pool.SwapStepModel

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.UniswapV3.Pool
set_option maxRecDepth 1000

macro "swap_step_get" : tactic => `(tactic| (
  simp only [swapStepReadyFrame, swapStepDirectionFrame, swapStepZeroFrame, swapStepFrame,
    swapStepLocals, Std.HashMap.get?_eq_getElem?, Std.HashMap.getElem?_insert]
  rfl))

theorem swapStepZerosSource (imms : Store) (evm : EVM.State) (a : SwapStepArgs) :
    ExecBlock config (swapStepFrame imms a) evm (swapStepFunction.body.take 4)
      (.ok (swapStepZeroFrame imms a) evm) := by
  let f1 : Frame := {swapStepFrame imms a with
    locals := (swapStepLocals a).insert "sqrtRatioNextX96" (.int 0)}
  let f2 : Frame := {f1 with locals := f1.locals.insert "amountIn" (.int 0)}
  let f3 : Frame := {f2 with locals := f2.locals.insert "amountOut" (.int 0)}
  refine ExecBlock.consNormal (solm' := f1) (evm' := evm)
    (ExecStmt.letDecl (by simp only [evalExpr?, pure])) ?_
  refine ExecBlock.consNormal (solm' := f2) (evm' := evm)
    (ExecStmt.letDecl (by simp only [evalExpr?, pure])) ?_
  refine ExecBlock.consNormal (solm' := f3) (evm' := evm)
    (ExecStmt.letDecl (by simp only [evalExpr?, pure])) ?_
  exact ExecBlock.consNormal (ExecStmt.letDecl (by simp only [evalExpr?, pure])) ExecBlock.nil

theorem swapStepDirectionSource (imms : Store) (evm : EVM.State) (a : SwapStepArgs) :
    ExecStmt config (swapStepZeroFrame imms a) evm (swapStepFunction.body[4]!)
      (.ok (swapStepDirectionFrame imms a) evm) := by
  have hc := evalExpr_var_get (cfg := config) (evm := evm) (frame := swapStepZeroFrame imms a)
    (name := "sqrtRatioCurrentX96") (value := .int (Int.ofNat a.current.toNat)) (by swap_step_get)
  have ht := evalExpr_var_get (cfg := config) (evm := evm) (frame := swapStepZeroFrame imms a)
    (name := "sqrtRatioTargetX96") (value := .int (Int.ofNat a.target.toNat)) (by swap_step_get)
  apply ExecStmt.letDecl
  simp only [evalExpr?, hc, ht, evalBinaryOp?, bind, EvalResult.bind, swapStepZeroForOne]
  apply congrArg (fun b : Bool ↦ EvalResult.ok (Value.bool b))
  apply Bool.eq_iff_iff.mpr
  simp only [decide_eq_true_eq]
  exact Int.ofNat_le

theorem swapStepPrefixSource (imms : Store) (evm : EVM.State) (a : SwapStepArgs) :
    ExecBlock config (swapStepFrame imms a) evm (swapStepFunction.body.take 6)
      (.ok (swapStepReadyFrame imms a) evm) := by
  change ExecBlock config (swapStepFrame imms a) evm
    (swapStepFunction.body.take 4 ++ [swapStepFunction.body[4]!, swapStepFunction.body[5]!]) _
  apply execBlock_append_ok (swapStepZerosSource imms evm a)
  refine ExecBlock.consNormal (swapStepDirectionSource imms evm a) ?_
  refine ExecBlock.consNormal (ExecStmt.letDecl ?_) ExecBlock.nil
  have hr := evalExpr_var_get (cfg := config) (evm := evm)
    (frame := swapStepDirectionFrame imms a) (name := "amountRemaining")
    (value := .int a.remaining) (by swap_step_get)
  simp only [evalExpr?, hr, evalBinaryOp?, bind, EvalResult.bind, pure, swapStepExactIn]

theorem swapStepReadyGet (imms : Store) (a : SwapStepArgs) :
    (swapStepReadyFrame imms a).locals.get? "sqrtRatioCurrentX96" =
      some (.int (Int.ofNat a.current.toNat)) ∧
    (swapStepReadyFrame imms a).locals.get? "sqrtRatioTargetX96" =
      some (.int (Int.ofNat a.target.toNat)) ∧
    (swapStepReadyFrame imms a).locals.get? "liquidity" =
      some (.int (Int.ofNat a.liquidity.toNat)) ∧
    (swapStepReadyFrame imms a).locals.get? "amountRemaining" = some (.int a.remaining) ∧
    (swapStepReadyFrame imms a).locals.get? "feePips" = some (.int (Int.ofNat a.fee.toNat)) ∧
    (swapStepReadyFrame imms a).locals.get? "zeroForOne" = some (.bool (swapStepZeroForOne a)) ∧
    (swapStepReadyFrame imms a).locals.get? "exactIn" = some (.bool (swapStepExactIn a)) := by
  repeat' apply And.intro
  all_goals swap_step_get

end Benchmarks.UniswapV3.Pool
