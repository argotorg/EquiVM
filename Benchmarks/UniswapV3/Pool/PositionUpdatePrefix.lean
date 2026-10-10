import Benchmarks.UniswapV3.Pool.PositionUpdateModel

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.UniswapV3.Pool
set_option maxRecDepth 1000

macro "position_update_get" : tactic =>
  `(tactic| (simp only [positionUpdateAddFrame, positionUpdateZeroFrame, positionUpdateSnapshotFrame,
    positionUpdateAliasFrame, positionUpdateFrame, positionUpdateLocals,
    Std.HashMap.get?_eq_getElem?, Std.HashMap.getElem?_insert, Std.HashMap.getElem?_empty]; rfl))

theorem positionUpdateSnapshotSource (imms : Store) (evm : EVM.State) (a : PositionUpdateArgs) :
    ExecBlock config (positionUpdateFrame imms a) evm (positionUpdateFunction.body.take 3)
      (.ok (positionUpdateZeroFrame imms a evm) evm) := by
  refine ExecBlock.consNormal (solm' := positionUpdateAliasFrame imms a) (evm' := evm)
    (ExecStmt.letStorage ?_) ?_
  · exact resolvePositionReference (positionUpdateLocals a) imms evm "key" a.key
      (by position_update_get) (by position_update_get)
  refine ExecBlock.consNormal (solm' := positionUpdateSnapshotFrame imms a evm)
    (ExecStmt.letDecl (evalPositionStruct (positionUpdateAliasFrame imms a).locals imms evm
      "self" a.key (by position_update_get))) ?_
  exact ExecBlock.consNormal (ExecStmt.letDecl (by simp only [evalExpr?, pure])) ExecBlock.nil

theorem evalPositionSnapshotLiquidity (locals imms : Store) (evm original : EVM.State)
    (a : PositionUpdateArgs)
    (hget : locals.get? "_self" = some (positionStructValue a.key original.accountMap original.executionEnv)) :
    evalExpr? config {contract := contract, locals := locals, immutables := imms} evm
      (.field (.var "_self") "liquidity") = .ok (.int (positionUpdateLiquidityBefore a original)) := by
  have he := evalExpr_var_get (cfg := config) (evm := evm)
    (frame := {contract := contract, locals := locals, immutables := imms}) hget
  simp only [evalExpr?, he, bind, EvalResult.bind]
  rfl

theorem evalPositionUpdateLiquidityChecks (imms : Store) (evm : EVM.State) (a : PositionUpdateArgs) :
    evalExpr? config (positionUpdateZeroFrame imms a evm) evm
      (.binary .eq (.var "liquidityDelta") (.intLit 0)) = .ok (.bool (decide (a.delta = 0))) ∧
    evalExpr? config (positionUpdateZeroFrame imms a evm) evm
      (.binary .gt (.field (.var "_self") "liquidity") (.intLit 0)) =
      .ok (.bool (decide (0 < positionUpdateLiquidityBefore a evm))) := by
  have hd := evalExpr_var_get (cfg := config) (evm := evm)
    (frame := positionUpdateZeroFrame imms a evm) (name := "liquidityDelta")
    (value := .int a.delta) (by position_update_get)
  have hl : evalExpr? config (positionUpdateZeroFrame imms a evm) evm
      (.field (.var "_self") "liquidity") = .ok (.int (positionUpdateLiquidityBefore a evm)) :=
    evalPositionSnapshotLiquidity (positionUpdateZeroFrame imms a evm).locals
      imms evm evm a (by position_update_get)
  constructor
  · simp [evalExpr?, hd, evalBinaryOp?, bind, EvalResult.bind, pure]
    apply Bool.eq_iff_iff.mpr
    simp only [beq_iff_eq, Value.int.injEq, decide_eq_true_eq]
  · simp only [evalExpr?, hl, evalBinaryOp?, bind, EvalResult.bind, pure]

def positionUpdateLiquidityArgs : List Expr :=
  [.field (.var "_self") "liquidity", .var "liquidityDelta"]

theorem evalPositionUpdateLiquidityArgs (imms : Store) (evm : EVM.State) (a : PositionUpdateArgs) :
    evalExprs? config (positionUpdateZeroFrame imms a evm) evm positionUpdateLiquidityArgs =
      .ok [.int (positionUpdateLiquidityBefore a evm), .int a.delta] := by
  have hl : evalExpr? config (positionUpdateZeroFrame imms a evm) evm
      (.field (.var "_self") "liquidity") = .ok (.int (positionUpdateLiquidityBefore a evm)) :=
    evalPositionSnapshotLiquidity (positionUpdateZeroFrame imms a evm).locals
      imms evm evm a (by position_update_get)
  have hd := evalExpr_var_get (cfg := config) (evm := evm)
    (frame := positionUpdateZeroFrame imms a evm) (name := "liquidityDelta")
    (value := .int a.delta) (by position_update_get)
  simp only [positionUpdateLiquidityArgs, evalExprs?, hl, hd, bind, EvalResult.bind, pure]

theorem positionUpdateLiquidityCall (imms : Store) (evm : EVM.State) (a : PositionUpdateArgs)
    (hv : liquidityDeltaValid (positionUpdateLiquidityBefore a evm) a.delta) :
    ExecStmt config (positionUpdateZeroFrame imms a evm) evm
      (.internalCall "LiquidityMath_addDelta" positionUpdateLiquidityArgs "__c0")
      (.ok (positionUpdateAddFrame imms a evm) evm) :=
  internalCallFunctionReturn (callee := liquidityDeltaFunction)
    (locals := liquidityDeltaLocals (positionUpdateLiquidityBefore a evm) a.delta)
    (calleeSolm := liquidityDeltaReadyFrame imms (positionUpdateLiquidityBefore a evm) a.delta)
    (value := some [.int (liquidityDeltaResult (positionUpdateLiquidityBefore a evm) a.delta)])
    (evalPositionUpdateLiquidityArgs imms evm a) liquidityDeltaLookup
    (liquidityDeltaBind (positionUpdateLiquidityBefore a evm) a.delta)
    (liquidityDeltaReturns imms evm _ _ hv)

end Benchmarks.UniswapV3.Pool
