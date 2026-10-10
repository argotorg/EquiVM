import Benchmarks.UniswapV3.Pool.TickUpdateNetCalls
import Benchmarks.UniswapV3.Pool.TickUpdateStaticSource

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.UniswapV3.Pool
set_option maxRecDepth 1000

theorem tickUpdateNetStartSource (imms : Store) (evm : EVM.State) (a : TickUpdateArgs)
    (hv : liquidityDeltaValid (tickUpdateGrossBefore a evm) a.delta)
    (hm : tickUpdateGrossAfter a evm ≤ Int.ofNat a.maxLiquidity.toNat) :
    ExecBlock config (tickUpdateFrame imms a) evm (tickUpdateFunction.body.take 9)
      (.ok (tickUpdateNetStartFrame imms a evm) (tickUpdateGrossState a evm)) := by
  change ExecBlock config (tickUpdateFrame imms a) evm
    (tickUpdateFunction.body.take 8 ++ [tickUpdateFunction.body[8]!]) _
  exact execBlock_append_ok (tickUpdateStoresSource imms evm a hv hm)
    (ExecBlock.consNormal (ExecStmt.letDecl (by simp only [evalExpr?, pure])) ExecBlock.nil)

theorem evalTickUpdateUpper (imms : Store) (evm : EVM.State) (a : TickUpdateArgs) :
    evalExpr? config (tickUpdateNetStartFrame imms a evm) (tickUpdateGrossState a evm)
      (.var "upper") = .ok (.bool a.upper) := by
  apply evalExpr_var_get
  simp only [tickUpdateNetStartFrame, Std.HashMap.get?_eq_getElem?, Std.HashMap.getElem?_insert]
  tick_update_get

theorem tickUpdateNetChoiceSource (imms : Store) (evm : EVM.State) (a : TickUpdateArgs)
    (hdlo : -(2 ^ 127 : Int) ≤ a.delta) (hdhi : a.delta < 2 ^ 127)
    (hv : safeCast128Valid (tickUpdateNetResult a evm a.upper)) :
    ExecStmt config (tickUpdateNetStartFrame imms a evm) (tickUpdateGrossState a evm)
      (tickUpdateFunction.body[9]!)
      (.ok (tickUpdateNetReadyFrame imms a evm a.upper) (tickUpdateGrossState a evm)) := by
  cases hu : a.upper
  · exact ExecStmt.iteFalse (by simpa only [hu] using evalTickUpdateUpper imms evm a)
      (tickUpdateNetBranchSource imms evm a false hdlo hdhi (by simpa only [hu] using hv))
  · exact ExecStmt.iteTrue (by simpa only [hu] using evalTickUpdateUpper imms evm a)
      (tickUpdateNetBranchSource imms evm a true hdlo hdhi (by simpa only [hu] using hv))

theorem tickUpdateNetChoiceReverts (imms : Store) (evm : EVM.State) (a : TickUpdateArgs)
    (hdlo : -(2 ^ 127 : Int) ≤ a.delta) (hdhi : a.delta < 2 ^ 127)
    (hv : ¬ safeCast128Valid (tickUpdateNetResult a evm a.upper)) :
    ExecStmt config (tickUpdateNetStartFrame imms a evm) (tickUpdateGrossState a evm)
      (tickUpdateFunction.body[9]!) .reverted := by
  cases hu : a.upper
  · exact ExecStmt.iteFalse (by simpa only [hu] using evalTickUpdateUpper imms evm a)
      (tickUpdateNetBranchReverts imms evm a false hdlo hdhi (by simpa only [hu] using hv))
  · exact ExecStmt.iteTrue (by simpa only [hu] using evalTickUpdateUpper imms evm a)
      (tickUpdateNetBranchReverts imms evm a true hdlo hdhi (by simpa only [hu] using hv))

theorem tickUpdateNetReverts (imms : Store) (evm : EVM.State) (a : TickUpdateArgs)
    (hdlo : -(2 ^ 127 : Int) ≤ a.delta) (hdhi : a.delta < 2 ^ 127)
    (hv : liquidityDeltaValid (tickUpdateGrossBefore a evm) a.delta)
    (hm : tickUpdateGrossAfter a evm ≤ Int.ofNat a.maxLiquidity.toNat)
    (hn : ¬ safeCast128Valid (tickUpdateNetResult a evm a.upper)) :
    ExecFuncBody config (tickUpdateFrame imms a) evm tickUpdateFunction.body .reverted := by
  apply ExecFuncBody.execBlockRevert
  rw [← List.take_append_drop 9 tickUpdateFunction.body]
  apply execBlock_append_ok (tickUpdateNetStartSource imms evm a hv hm)
  exact ExecBlock.consRevert (tickUpdateNetChoiceReverts imms evm a hdlo hdhi hn)

theorem tickUpdateNetReadyGet (imms : Store) (evm : EVM.State) (a : TickUpdateArgs)
    (subtract : Bool) :
    (tickUpdateNetReadyFrame imms a evm subtract).locals.get? "info" = some (tickAlias a.tick) ∧
    (tickUpdateNetReadyFrame imms a evm subtract).locals.get? "flipped" =
      some (.bool (tickUpdateFlipped a evm)) ∧
    (tickUpdateNetReadyFrame imms a evm subtract).locals.get? "__cond5" =
      some (.int (tickUpdateNetResult a evm subtract)) := by
  cases subtract <;> refine ⟨?_, ?_, ?_⟩
  all_goals simp only [tickUpdateNetReadyFrame, tickUpdateCastFrame, tickUpdateMathFrame,
    tickUpdateNetStartFrame, tickUpdateCastRet, tickUpdateMathRet,
    Bool.false_eq_true, if_false, if_true, Std.HashMap.get?_eq_getElem?, Std.HashMap.getElem?_insert]
  all_goals tick_update_get

theorem tickUpdateReturns (imms : Store) (evm : EVM.State) (a : TickUpdateArgs)
    (hdlo : -(2 ^ 127 : Int) ≤ a.delta) (hdhi : a.delta < 2 ^ 127)
    (hv : liquidityDeltaValid (tickUpdateGrossBefore a evm) a.delta)
    (hm : tickUpdateGrossAfter a evm ≤ Int.ofNat a.maxLiquidity.toNat)
    (hn : safeCast128Valid (tickUpdateNetResult a evm a.upper)) :
    ExecFuncBody config (tickUpdateFrame imms a) evm tickUpdateFunction.body
      (.returned (tickUpdateNetReadyFrame imms a evm a.upper) (tickUpdateFinalState a evm)
        (some [.bool (tickUpdateFlipped a evm)])) := by
  apply ExecFuncBody.execBlockRet
  rw [← List.take_append_drop 9 tickUpdateFunction.body]
  apply execBlock_append_ok (tickUpdateNetStartSource imms evm a hv hm)
  refine ExecBlock.consNormal (tickUpdateNetChoiceSource imms evm a hdlo hdhi hn) ?_
  have hg := tickUpdateNetReadyGet imms evm a a.upper
  refine ExecBlock.consNormal (solm' := tickUpdateNetReadyFrame imms a evm a.upper)
    (evm' := tickUpdateFinalState a evm)
    (ExecStmt.assign (evalExpr_var_get hg.2.2)
      (assignTickLiquidity (tickUpdateNetReadyFrame imms a evm a.upper).locals imms _ "info"
        a.tick true (.int (tickUpdateNetResult a evm a.upper))
        (EVM.wordOfInt (tickUpdateNetResult a evm a.upper)) hg.1 rfl)) ?_
  refine ExecBlock.consReturn (ExecStmt.return ?_)
  have he := evalExpr_var_get (cfg := config) (evm := tickUpdateFinalState a evm) hg.2.1
  simp only [evalExprs?, he, bind, EvalResult.bind, pure]

end Benchmarks.UniswapV3.Pool
