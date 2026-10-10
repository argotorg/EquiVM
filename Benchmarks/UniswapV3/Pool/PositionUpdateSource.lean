import Benchmarks.UniswapV3.Pool.PositionUpdateStoresSource

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.UniswapV3.Pool
set_option maxRecDepth 1000

theorem positionUpdateReturns (imms : Store) (evm : EVM.State)
    (a : PositionUpdateArgs) (hv : positionUpdateLiquidityValid a evm) :
    ExecFuncBody config (positionUpdateFrame imms a) evm positionUpdateFunction.body
      (.returned (positionUpdateReadyFrame imms a evm) (positionUpdateFinalState a evm) none) := by
  apply ExecFuncBody.execBlockOK
  rw [← List.take_append_drop 11 positionUpdateFunction.body]
  exact execBlock_append_ok (positionUpdateStoresSource imms evm a hv)
    (ExecBlock.consNormal (positionUpdateOwedChoice imms evm a) ExecBlock.nil)

theorem positionUpdateStatic (imms : Store) (evm : EVM.State)
    (a : PositionUpdateArgs) (hv : positionUpdateLiquidityValid a evm)
    (hp : evm.executionEnv.perm = false) :
    ExecFuncBody config (positionUpdateFrame imms a) evm positionUpdateFunction.body
      .staticViolation := by
  apply ExecFuncBody.execBlockStatic
  rw [← List.take_append_drop 8 positionUpdateFunction.body]
  apply execBlock_append_ok (positionUpdateFeesSource imms evm a hv)
  by_cases hz : a.delta = 0
  · have hskip := positionUpdateLiquidityStoreChoice imms evm a
    simp only [positionUpdateLiquidityState, if_pos hz] at hskip
    refine ExecBlock.consNormal hskip (ExecBlock.consStatic ?_)
    exact execStmt_assign_static (positionUpdateGrowthStore imms evm evm a false) hp
  · apply ExecBlock.consStatic
    apply ExecStmt.iteTrue
      (by simpa only [decide_eq_true hz] using evalPositionUpdateNonzero imms evm evm a)
    exact ExecBlock.consStatic (execStmt_assign_static (positionUpdateLiquidityStore imms evm a) hp)

end Benchmarks.UniswapV3.Pool
