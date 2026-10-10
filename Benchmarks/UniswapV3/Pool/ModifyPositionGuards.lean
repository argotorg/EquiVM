import Benchmarks.UniswapV3.Pool.ModifyPositionUpdateSource

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables Benchmarks.UniswapV3.Pool.Immutables
namespace Benchmarks.UniswapV3.Pool
set_option maxRecDepth 10000

theorem evalModifyPositionNonzero (imms : Store) (a : ModifyPositionArgs) (evm evm' : EVM.State) :
    evalExpr? config (modifyPositionUpdatedFrame imms a evm) evm'
      (.binary .ne (.field (.var "params") "liquidityDelta") (.intLit 0)) =
      .ok (.bool (decide (a.delta ≠ 0))) := by
  have hp : evalExpr? config (modifyPositionUpdatedFrame imms a evm) evm' (.var "params") =
      .ok a.value := evalExpr_var_get (by modify_position_updated_get)
  have hd := evalExpr_structField (name := "liquidityDelta") hp rfl
  simp only [evalExpr?, hd, bind, EvalResult.bind, evalBinaryOp?, pure]
  apply congrArg EvalResult.ok
  apply congrArg Value.bool
  apply Bool.eq_iff_iff.mpr
  simp [beq_iff_eq, decide_eq_true_eq, Value.int.injEq]

theorem evalModifyPositionRangeGuard (imms : Store) (a : ModifyPositionArgs)
    (evm evm' : EVM.State) (upper : Bool) :
    evalExpr? config (modifyPositionUpdatedFrame imms a evm) evm'
      (.binary .lt (.field (.var "_slot0") "tick")
        (.field (.var "params") (if upper then "tickUpper" else "tickLower"))) =
      .ok (.bool (decide (slot0TickValue evm.accountMap evm.executionEnv <
        (if upper then a.upper else a.lower)))) := by
  have hp : evalExpr? config (modifyPositionUpdatedFrame imms a evm) evm' (.var "params") =
      .ok a.value := evalExpr_var_get (by modify_position_updated_get)
  have hs : evalExpr? config (modifyPositionUpdatedFrame imms a evm) evm' (.var "_slot0") =
      .ok (slot0StructValue evm.accountMap evm.executionEnv) :=
    evalExpr_var_get (by modify_position_updated_get)
  have ht := evalExpr_structField (name := "tick") hs rfl
  have hb : evalExpr? config (modifyPositionUpdatedFrame imms a evm) evm'
      (.field (.var "params") (if upper then "tickUpper" else "tickLower")) =
      .ok (.int (if upper then a.upper else a.lower)) := by
    cases upper <;> exact evalExpr_structField hp rfl
  simp only [evalExpr?, ht, hb, bind, EvalResult.bind, evalBinaryOp?, pure]

theorem modifyPositionZeroTailSource (imms : Store) (a : ModifyPositionArgs)
    (evm evm' : EVM.State) (hz : a.delta = 0) :
    ExecBlock config (modifyPositionUpdatedFrame imms a evm) evm'
      (modifyPositionFunction.body.drop 8)
      (.returned (modifyPositionUpdatedFrame imms a evm) evm'
        (some [modifyPositionKeyValue a, .int 0, .int 0])) := by
  refine ExecBlock.consNormal (ExecStmt.iteFalse ?_ ExecBlock.nil) ?_
  · simp only [evalModifyPositionNonzero, hz, ne_eq, not_true, decide_false]
  · have hk : evalExpr? config (modifyPositionUpdatedFrame imms a evm) evm' (.var "position") =
        .ok (modifyPositionKeyValue a) := evalExpr_var_get (by modify_position_updated_get)
    have h0 : evalExpr? config (modifyPositionUpdatedFrame imms a evm) evm' (.var "amount0") =
        .ok (.int 0) := evalExpr_var_get (by modify_position_updated_get)
    have h1 : evalExpr? config (modifyPositionUpdatedFrame imms a evm) evm' (.var "amount1") =
        .ok (.int 0) := evalExpr_var_get (by modify_position_updated_get)
    exact ExecBlock.consReturn (ExecStmt.return (by
      simp only [evalExprs?, hk, h0, h1, bind, EvalResult.bind, pure]))

end Benchmarks.UniswapV3.Pool
