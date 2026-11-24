import Benchmarks.UniswapV3.Pool.TickCrossHistorySource

variable {fork : Ethereum.Fork}

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.UniswapV3.Pool

theorem tickCrossReturns (imms : Store) (evm : EVM.State) (a : TickCrossArgs)
    (hperm : evm.executionEnv.perm = true) :
    ExecFuncBody fork config (tickCrossFrame imms a) evm tickCrossFunction.body
      (.returned (tickCrossResultFrame imms a evm) (tickCrossState evm a)
        (some [.int (tickCrossResult evm a)])) := by
  apply ExecFuncBody.execBlockRet
  rw [← List.take_append_drop 7 tickCrossFunction.body]
  apply execBlock_append_ok (tickCrossStoresSource (fork := fork) (hperm := by assumption) imms evm a)
  refine ExecBlock.consNormal (stele' := tickCrossResultFrame imms a evm)
    (ExecStmt.assign (fork := fork) (hperm := Or.inl rfl) ?_ (assignLocalVarBase_frame (old := .int 0) (by tick_cross_get))) ?_
  · exact evalTickAliasNet (tickCrossAliasFrame imms a).locals imms (tickCrossState evm a)
      "info" a.tick (by tick_cross_get)
  · apply ExecBlock.consReturn
    apply ExecStmt.return
    have hg := evalExpr_var_get (cfg := config) (frame := tickCrossResultFrame imms a evm)
      (evm := tickCrossState evm a) (name := "liquidityNet")
      (value := .int (tickCrossResult evm a)) (by tick_cross_get)
    simp only [evalExprs?, hg, bind, EvalResult.bind, pure]

end Benchmarks.UniswapV3.Pool
