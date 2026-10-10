import Benchmarks.UniswapV3.Pool.PositionUpdatePrefix

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.UniswapV3.Pool
set_option maxRecDepth 1000

theorem positionUpdateLiquidityChoiceSource (imms : Store) (evm : EVM.State)
    (a : PositionUpdateArgs) (hv : positionUpdateLiquidityValid a evm) :
    ExecStmt config (positionUpdateZeroFrame imms a evm) evm (positionUpdateFunction.body[3]!)
      (.ok (positionUpdateLiquidityFrame imms a evm) evm) := by
  have hc := evalPositionUpdateLiquidityChecks imms evm a
  by_cases hz : a.delta = 0
  · simp only [positionUpdateLiquidityValid, if_pos hz] at hv
    simp only [positionUpdateLiquidityFrame, positionUpdateLiquidityNext, if_pos hz]
    apply ExecStmt.iteTrue (by simpa only [hz, decide_true] using hc.1)
    refine ExecBlock.consNormal (ExecStmt.requireTrue
      (by simpa only [hv, decide_true] using hc.2)) ?_
    exact ExecBlock.consNormal (ExecStmt.assign
      (evalPositionSnapshotLiquidity (positionUpdateZeroFrame imms a evm).locals imms evm evm a
        (by position_update_get))
      (assignLocalVarBase_frame (old := .int 0) (by position_update_get))) ExecBlock.nil
  · simp only [positionUpdateLiquidityValid, if_neg hz] at hv
    simp only [positionUpdateLiquidityFrame, positionUpdateLiquidityNext, if_neg hz]
    apply ExecStmt.iteFalse (by simpa only [hz, decide_false] using hc.1)
    refine ExecBlock.consNormal (positionUpdateLiquidityCall imms evm a hv) ?_
    exact ExecBlock.consNormal (ExecStmt.assign
      (evalExpr_var_get Std.HashMap.getElem?_insert_self)
      (assignLocalVarBase_frame (old := .int 0) (by position_update_get))) ExecBlock.nil

theorem positionUpdateLiquiditySource (imms : Store) (evm : EVM.State)
    (a : PositionUpdateArgs) (hv : positionUpdateLiquidityValid a evm) :
    ExecBlock config (positionUpdateFrame imms a) evm (positionUpdateFunction.body.take 4)
      (.ok (positionUpdateLiquidityFrame imms a evm) evm) := by
  change ExecBlock config (positionUpdateFrame imms a) evm
    (positionUpdateFunction.body.take 3 ++ [positionUpdateFunction.body[3]!]) _
  exact execBlock_append_ok (positionUpdateSnapshotSource imms evm a)
    (ExecBlock.consNormal (positionUpdateLiquidityChoiceSource imms evm a hv) ExecBlock.nil)

theorem positionUpdateLiquidityReverts (imms : Store) (evm : EVM.State)
    (a : PositionUpdateArgs) (hv : ¬ positionUpdateLiquidityValid a evm) :
    ExecFuncBody config (positionUpdateFrame imms a) evm positionUpdateFunction.body .reverted := by
  apply ExecFuncBody.execBlockRevert
  rw [← List.take_append_drop 3 positionUpdateFunction.body]
  apply execBlock_append_ok (positionUpdateSnapshotSource imms evm a)
  apply ExecBlock.consRevert
  have hc := evalPositionUpdateLiquidityChecks imms evm a
  by_cases hz : a.delta = 0
  · simp only [positionUpdateLiquidityValid, if_pos hz] at hv
    apply ExecStmt.iteTrue (by simpa only [hz, decide_true] using hc.1)
    exact ExecBlock.consRevert (ExecStmt.requireFalse
      (by simpa only [hv, decide_false] using hc.2))
  · simp only [positionUpdateLiquidityValid, if_neg hz] at hv
    apply ExecStmt.iteFalse (by simpa only [hz, decide_false] using hc.1)
    apply ExecBlock.consRevert
    exact internalCallFunctionRevert (callee := liquidityDeltaFunction)
      (locals := liquidityDeltaLocals (positionUpdateLiquidityBefore a evm) a.delta)
      (evalPositionUpdateLiquidityArgs imms evm a) liquidityDeltaLookup
      (liquidityDeltaBind (positionUpdateLiquidityBefore a evm) a.delta)
      (liquidityDeltaReverts imms evm _ _ hv)

end Benchmarks.UniswapV3.Pool
