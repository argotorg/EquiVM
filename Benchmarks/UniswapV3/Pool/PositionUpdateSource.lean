import Benchmarks.UniswapV3.Pool.PositionUpdateStoresSource

variable {fork : Ethereum.Fork}

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.UniswapV3.Pool
set_option maxRecDepth 1000

theorem positionUpdateReturns (imms : Store) (evm : EVM.State)
    (a : PositionUpdateArgs) (hv : positionUpdateLiquidityValid a evm)
    (hperm : evm.executionEnv.perm = true) :
    ExecFuncBody fork config (positionUpdateFrame imms a) evm positionUpdateFunction.body
      (.returned (positionUpdateReadyFrame imms a evm) (positionUpdateFinalState a evm) none) := by
  apply ExecFuncBody.execBlockOK
  rw [← List.take_append_drop 11 positionUpdateFunction.body]
  exact execBlock_append_ok (positionUpdateStoresSource (fork := fork) (hperm := by assumption) imms evm a hv)
    (ExecBlock.consNormal (positionUpdateOwedChoice (fork := fork) (hperm := by assumption) imms evm a) ExecBlock.nil)

theorem positionUpdateStatic (imms : Store) (evm : EVM.State)
    (a : PositionUpdateArgs) (hv : positionUpdateLiquidityValid a evm)
    (hp : evm.executionEnv.perm = false) :
    ExecFuncBody fork config (positionUpdateFrame imms a) evm positionUpdateFunction.body
      .staticViolation := by
  apply ExecFuncBody.execBlockStatic
  rw [← List.take_append_drop 8 positionUpdateFunction.body]
  apply execBlock_append_ok (positionUpdateFeesSource imms evm a hv)
  by_cases hz : a.delta = 0
  · have hskip : ExecStmt fork config (positionUpdateReadyFrame imms a evm) evm
        (positionUpdateFunction.body[8]!) (.ok (positionUpdateReadyFrame imms a evm) evm) :=
      ExecStmt.iteFalse (by simpa only [hz, ne_eq, not_true_eq_false, decide_false] using
        evalPositionUpdateNonzero imms evm evm a) ExecBlock.nil
    refine ExecBlock.consNormal hskip (ExecBlock.consStatic ?_)
    exact execStmt_assign_static (positionUpdateGrowthStore imms evm evm a false) hp
  · apply ExecBlock.consStatic
    apply ExecStmt.iteTrue
      (by simpa only [decide_eq_true hz] using evalPositionUpdateNonzero imms evm evm a)
    exact ExecBlock.consStatic (execStmt_assign_static (positionUpdateLiquidityStore imms evm a) hp)

end Benchmarks.UniswapV3.Pool
