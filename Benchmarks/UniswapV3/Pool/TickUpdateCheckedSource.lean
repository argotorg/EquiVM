import Benchmarks.UniswapV3.Pool.TickUpdatePrefix

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.UniswapV3.Pool
set_option maxRecDepth 1000

theorem evalTickUpdateMax (imms : Store) (evm : EVM.State) (a : TickUpdateArgs) :
    evalExpr? config (tickUpdateAfterFrame imms a evm) evm
      (.binary .le (.var "liquidityGrossAfter") (.var "maxLiquidity")) =
      .ok (.bool (decide (tickUpdateGrossAfter a evm ≤ Int.ofNat a.maxLiquidity.toNat))) := by
  have hg := evalExpr_var_get (cfg := config) (evm := evm)
    (frame := tickUpdateAfterFrame imms a evm) (name := "liquidityGrossAfter")
    (value := .int (tickUpdateGrossAfter a evm)) (by tick_update_get)
  have hm := evalExpr_var_get (cfg := config) (evm := evm)
    (frame := tickUpdateAfterFrame imms a evm) (name := "maxLiquidity")
    (value := .int (Int.ofNat a.maxLiquidity.toNat)) (by tick_update_get)
  simp only [evalExpr?, hg, hm, evalBinaryOp?, bind, EvalResult.bind, pure]

theorem evalTickUpdateFlipped (imms : Store) (evm : EVM.State) (a : TickUpdateArgs) :
    evalExpr? config (tickUpdateAfterFrame imms a evm) evm
      (.binary .ne (.binary .eq (.var "liquidityGrossAfter") (.intLit 0))
        (.binary .eq (.var "liquidityGrossBefore") (.intLit 0))) =
      .ok (.bool (tickUpdateFlipped a evm)) := by
  have ha := evalExpr_var_get (cfg := config) (evm := evm)
    (frame := tickUpdateAfterFrame imms a evm) (name := "liquidityGrossAfter")
    (value := .int (tickUpdateGrossAfter a evm)) (by tick_update_get)
  have hb := evalExpr_var_get (cfg := config) (evm := evm)
    (frame := tickUpdateAfterFrame imms a evm) (name := "liquidityGrossBefore")
    (value := .int (tickUpdateGrossBefore a evm)) (by tick_update_get)
  by_cases haz : tickUpdateGrossAfter a evm = 0 <;>
    by_cases hbz : tickUpdateGrossBefore a evm = 0
  all_goals simp [evalExpr?, ha, hb, evalBinaryOp?, bind, EvalResult.bind, pure,
    tickUpdateFlipped, haz, hbz]

theorem tickUpdateMaxReverts (imms : Store) (evm : EVM.State) (a : TickUpdateArgs)
    (hv : liquidityDeltaValid (tickUpdateGrossBefore a evm) a.delta)
    (hm : ¬ tickUpdateGrossAfter a evm ≤ Int.ofNat a.maxLiquidity.toNat) :
    ExecFuncBody config (tickUpdateFrame imms a) evm tickUpdateFunction.body .reverted := by
  apply ExecFuncBody.execBlockRevert
  rw [← List.take_append_drop 4 tickUpdateFunction.body]
  apply execBlock_append_ok (tickUpdateAfterSource imms evm a hv)
  exact ExecBlock.consRevert (ExecStmt.requireFalse
    (by simpa only [hm, decide_false] using evalTickUpdateMax imms evm a))

theorem tickUpdateCheckedSource (imms : Store) (evm : EVM.State) (a : TickUpdateArgs)
    (hv : liquidityDeltaValid (tickUpdateGrossBefore a evm) a.delta)
    (hm : tickUpdateGrossAfter a evm ≤ Int.ofNat a.maxLiquidity.toNat) :
    ExecBlock config (tickUpdateFrame imms a) evm (tickUpdateFunction.body.take 6)
      (.ok (tickUpdateFlippedFrame imms a evm) evm) := by
  change ExecBlock config (tickUpdateFrame imms a) evm
    (tickUpdateFunction.body.take 4 ++ [tickUpdateFunction.body[4]!, tickUpdateFunction.body[5]!]) _
  apply execBlock_append_ok (tickUpdateAfterSource imms evm a hv)
  refine ExecBlock.consNormal (ExecStmt.requireTrue
    (by simpa only [hm, decide_true] using evalTickUpdateMax imms evm a)) ?_
  exact ExecBlock.consNormal (ExecStmt.assign (evalTickUpdateFlipped imms evm a)
    (assignLocalVarBase_frame (old := .bool false) (by tick_update_get))) ExecBlock.nil

end Benchmarks.UniswapV3.Pool
