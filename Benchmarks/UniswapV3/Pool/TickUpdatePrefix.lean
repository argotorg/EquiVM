import Benchmarks.UniswapV3.Pool.TickUpdateModel

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.UniswapV3.Pool
set_option maxRecDepth 1000

macro "tick_update_get" : tactic => `(tactic| (
  simp only [tickUpdateFlippedFrame, tickUpdateAfterFrame, tickUpdateBeforeFrame,
    tickUpdateAliasFrame, tickUpdateFalseFrame, tickUpdateFrame, tickUpdateLocals,
    Std.HashMap.get?_eq_getElem?, Std.HashMap.getElem?_insert]
  rfl))

theorem tickUpdateBeforeSource (imms : Store) (evm : EVM.State) (a : TickUpdateArgs) :
    ExecBlock config (tickUpdateFrame imms a) evm (tickUpdateFunction.body.take 3)
      (.ok (tickUpdateBeforeFrame imms a evm) evm) := by
  refine ExecBlock.consNormal (solm' := tickUpdateFalseFrame imms a)
    (ExecStmt.letDecl (by simp only [evalExpr?, pure])) ?_
  refine ExecBlock.consNormal (solm' := tickUpdateAliasFrame imms a) (evm' := evm)
    (ExecStmt.letStorage ?_) ?_
  · apply resolveTickReference _ imms evm "tick" a.tick
    · simp [tickUpdateFalseFrame, tickUpdateFrame, tickUpdateLocals]
    · tick_update_get
  · refine ExecBlock.consNormal (solm' := tickUpdateBeforeFrame imms a evm)
      (ExecStmt.letDecl ?_) ExecBlock.nil
    exact evalTickAliasGross (tickUpdateAliasFrame imms a).locals imms evm "info" a.tick
      (by tick_update_get)

theorem tickUpdateLiquidityArgs (imms : Store) (evm : EVM.State) (a : TickUpdateArgs) :
    evalExprs? config (tickUpdateBeforeFrame imms a evm) evm
      [.var "liquidityGrossBefore", .var "liquidityDelta"] =
      .ok [.int (tickUpdateGrossBefore a evm), .int a.delta] := by
  have hg := evalExpr_var_get (cfg := config) (evm := evm)
    (frame := tickUpdateBeforeFrame imms a evm) (name := "liquidityGrossBefore")
    (value := .int (tickUpdateGrossBefore a evm)) (by tick_update_get)
  have hd := evalExpr_var_get (cfg := config) (evm := evm)
    (frame := tickUpdateBeforeFrame imms a evm) (name := "liquidityDelta")
    (value := .int a.delta) (by tick_update_get)
  simp only [evalExprs?, hg, hd, bind, EvalResult.bind, pure]

theorem tickUpdateLiquidityCall (imms : Store) (evm : EVM.State) (a : TickUpdateArgs)
    (hv : liquidityDeltaValid (tickUpdateGrossBefore a evm) a.delta) :
    ExecStmt config (tickUpdateBeforeFrame imms a evm) evm (tickUpdateFunction.body[3]!)
      (.ok (tickUpdateAfterFrame imms a evm) evm) := by
  exact internalCallFunctionReturn (callee := liquidityDeltaFunction)
    (locals := liquidityDeltaLocals (tickUpdateGrossBefore a evm) a.delta)
    (calleeSolm := liquidityDeltaReadyFrame imms (tickUpdateGrossBefore a evm) a.delta)
    (value := some [.int (tickUpdateGrossAfter a evm)])
    (tickUpdateLiquidityArgs imms evm a) liquidityDeltaLookup
    (liquidityDeltaBind (tickUpdateGrossBefore a evm) a.delta)
    (liquidityDeltaReturns imms evm (tickUpdateGrossBefore a evm) a.delta hv)

theorem tickUpdateAfterSource (imms : Store) (evm : EVM.State) (a : TickUpdateArgs)
    (hv : liquidityDeltaValid (tickUpdateGrossBefore a evm) a.delta) :
    ExecBlock config (tickUpdateFrame imms a) evm (tickUpdateFunction.body.take 4)
      (.ok (tickUpdateAfterFrame imms a evm) evm) := by
  change ExecBlock config (tickUpdateFrame imms a) evm
    (tickUpdateFunction.body.take 3 ++ [tickUpdateFunction.body[3]!]) _
  exact execBlock_append_ok (tickUpdateBeforeSource imms evm a)
    (ExecBlock.consNormal (tickUpdateLiquidityCall imms evm a hv) ExecBlock.nil)

theorem tickUpdateLiquidityReverts (imms : Store) (evm : EVM.State) (a : TickUpdateArgs)
    (hv : ¬ liquidityDeltaValid (tickUpdateGrossBefore a evm) a.delta) :
    ExecFuncBody config (tickUpdateFrame imms a) evm tickUpdateFunction.body .reverted := by
  apply ExecFuncBody.execBlockRevert
  rw [← List.take_append_drop 3 tickUpdateFunction.body]
  apply execBlock_append_ok (tickUpdateBeforeSource imms evm a)
  apply ExecBlock.consRevert
  exact internalCallFunctionRevert (callee := liquidityDeltaFunction)
    (locals := liquidityDeltaLocals (tickUpdateGrossBefore a evm) a.delta)
    (tickUpdateLiquidityArgs imms evm a) liquidityDeltaLookup
    (liquidityDeltaBind (tickUpdateGrossBefore a evm) a.delta)
    (liquidityDeltaReverts imms evm (tickUpdateGrossBefore a evm) a.delta hv)

end Benchmarks.UniswapV3.Pool
