import Benchmarks.UniswapV3.Pool.TickUpdateNetModel

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.UniswapV3.Pool
set_option maxRecDepth 1000

theorem evalTickUpdateNetArgs (imms : Store) (evm : EVM.State) (a : TickUpdateArgs) :
    evalExprs? config (tickUpdateNetStartFrame imms a evm) (tickUpdateGrossState a evm)
      tickUpdateNetArgs = .ok [.int (tickUpdateNetBefore a evm), .int a.delta] := by
  have he : evalExpr? config (tickUpdateNetStartFrame imms a evm) (tickUpdateGrossState a evm)
      (.storage ⟨"info", [.field "liquidityNet"]⟩) = .ok (.int (tickUpdateNetBefore a evm)) :=
    evalTickAliasNet (tickUpdateNetStartFrame imms a evm).locals imms _ "info" a.tick
      (by simp only [tickUpdateNetStartFrame, Std.HashMap.get?_eq_getElem?,
        Std.HashMap.getElem?_insert]; tick_update_get)
  have hd := evalExpr_var_get (cfg := config) (evm := tickUpdateGrossState a evm)
    (frame := tickUpdateNetStartFrame imms a evm) (name := "liquidityDelta") (value := .int a.delta)
    (by simp only [tickUpdateNetStartFrame, Std.HashMap.get?_eq_getElem?,
      Std.HashMap.getElem?_insert]; tick_update_get)
  have hb := tickUpdateNetBefore_bounds a evm
  have hn : normalizeInt (.sint ⟨256, by decide⟩) (tickUpdateNetBefore a evm) =
      tickUpdateNetBefore a evm := normalizeSint_eq_self ⟨256, by decide⟩ _
        (by norm_num [EVM.twoPow]; omega) (by norm_num [EVM.twoPow]; omega)
  simp only [tickUpdateNetArgs, evalExprs?, evalExpr?, he, hd, castValue?, hn,
    EvalResult.ofOption, bind, EvalResult.bind, pure]

theorem tickUpdateMathCall (imms : Store) (evm : EVM.State) (a : TickUpdateArgs)
    (subtract : Bool) (hdlo : -(2 ^ 127 : Int) ≤ a.delta) (hdhi : a.delta < 2 ^ 127) :
    ExecStmt config (tickUpdateNetStartFrame imms a evm) (tickUpdateGrossState a evm)
      ((tickUpdateNetBody subtract)[0]!)
      (.ok (tickUpdateMathFrame imms a evm subtract) (tickUpdateGrossState a evm)) := by
  exact internalCallFunctionReturn (callee := safeSignedMathFunction subtract)
    (locals := safeSignedMathLocals (tickUpdateNetBefore a evm) a.delta)
    (calleeSolm := safeSignedMathReadyFrame subtract imms (tickUpdateNetBefore a evm) a.delta)
    (value := some [.int (tickUpdateNetResult a evm subtract)])
    (evalTickUpdateNetArgs imms evm a) (safeSignedMathLookup subtract)
    (safeSignedMathBind subtract (tickUpdateNetBefore a evm) a.delta)
    (safeSignedMathReturns subtract imms _ _ _ (tickUpdateNetMathValid a evm subtract hdlo hdhi))

theorem evalTickUpdateCastArgs (imms : Store) (evm : EVM.State) (a : TickUpdateArgs)
    (subtract : Bool) :
    evalExprs? config (tickUpdateMathFrame imms a evm subtract) (tickUpdateGrossState a evm)
      [.var (tickUpdateMathRet subtract)] = .ok [.int (tickUpdateNetResult a evm subtract)] := by
  have he : evalExpr? config (tickUpdateMathFrame imms a evm subtract) (tickUpdateGrossState a evm)
      (.var (tickUpdateMathRet subtract)) = .ok (.int (tickUpdateNetResult a evm subtract)) :=
    evalExpr_var_get Std.HashMap.getElem?_insert_self
  simp only [evalExprs?, he, bind, EvalResult.bind, pure]

theorem tickUpdateCastCall (imms : Store) (evm : EVM.State) (a : TickUpdateArgs)
    (subtract : Bool) (hv : safeCast128Valid (tickUpdateNetResult a evm subtract)) :
    ExecStmt config (tickUpdateMathFrame imms a evm subtract) (tickUpdateGrossState a evm)
      ((tickUpdateNetBody subtract)[1]!)
      (.ok (tickUpdateCastFrame imms a evm subtract) (tickUpdateGrossState a evm)) := by
  exact internalCallFunctionReturn (callee := safeCast128Function)
    (locals := safeCast128Locals (tickUpdateNetResult a evm subtract))
    (calleeSolm := safeCast128ReadyFrame imms (tickUpdateNetResult a evm subtract))
    (value := some [.int (tickUpdateNetResult a evm subtract)])
    (evalTickUpdateCastArgs imms evm a subtract) safeCast128Lookup
    (safeCast128Bind (tickUpdateNetResult a evm subtract))
    (safeCast128Returns imms _ _ hv)

theorem tickUpdateNetBranchSource (imms : Store) (evm : EVM.State) (a : TickUpdateArgs)
    (subtract : Bool) (hdlo : -(2 ^ 127 : Int) ≤ a.delta) (hdhi : a.delta < 2 ^ 127)
    (hv : safeCast128Valid (tickUpdateNetResult a evm subtract)) :
    ExecBlock config (tickUpdateNetStartFrame imms a evm) (tickUpdateGrossState a evm)
      (tickUpdateNetBody subtract)
      (.ok (tickUpdateNetReadyFrame imms a evm subtract) (tickUpdateGrossState a evm)) := by
  refine ExecBlock.consNormal (tickUpdateMathCall imms evm a subtract hdlo hdhi) ?_
  refine ExecBlock.consNormal (tickUpdateCastCall imms evm a subtract hv) ?_
  refine ExecBlock.consNormal (ExecStmt.assign
    (evalExpr_var_get Std.HashMap.getElem?_insert_self) ?_) ExecBlock.nil
  apply assignLocalVarBase_frame (old := .int 0)
  cases subtract <;> simp only [tickUpdateCastFrame, tickUpdateMathFrame, tickUpdateNetStartFrame,
    tickUpdateCastRet, tickUpdateMathRet, Bool.false_eq_true, if_false, if_true,
    Std.HashMap.get?_eq_getElem?, Std.HashMap.getElem?_insert] <;> rfl

theorem tickUpdateNetBranchReverts (imms : Store) (evm : EVM.State) (a : TickUpdateArgs)
    (subtract : Bool) (hdlo : -(2 ^ 127 : Int) ≤ a.delta) (hdhi : a.delta < 2 ^ 127)
    (hv : ¬ safeCast128Valid (tickUpdateNetResult a evm subtract)) :
    ExecBlock config (tickUpdateNetStartFrame imms a evm) (tickUpdateGrossState a evm)
      (tickUpdateNetBody subtract) .reverted := by
  refine ExecBlock.consNormal (tickUpdateMathCall imms evm a subtract hdlo hdhi) ?_
  apply ExecBlock.consRevert
  exact internalCallFunctionRevert (callee := safeCast128Function)
    (locals := safeCast128Locals (tickUpdateNetResult a evm subtract))
    (evalTickUpdateCastArgs imms evm a subtract) safeCast128Lookup
    (safeCast128Bind (tickUpdateNetResult a evm subtract))
    (safeCast128Reverts imms _ _ hv)

end Benchmarks.UniswapV3.Pool
