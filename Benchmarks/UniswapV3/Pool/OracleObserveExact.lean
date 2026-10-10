import Benchmarks.UniswapV3.Pool.OracleObservePair

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.UniswapV3.Pool
set_option maxRecDepth 10000

theorem evalOracleCumulatives {cfg : Config} {frame : Frame} {evm : EVM.State} {name : Ident}
    (last : OracleObservation) (hget : frame.locals.get? name = some last.value) :
    evalExprs? cfg frame evm [.field (.var name) "tickCumulative",
      .field (.var name) "secondsPerLiquidityCumulativeX128"] = .ok last.cumulatives := by
  have he := evalExpr_var_get (cfg := cfg) (evm := evm) hget
  simp only [evalExprs?, evalExpr?, he, OracleObservation.value, OracleObservation.cumulatives,
    lookupField?, lookupAssoc, EvalResult.ofOption, bind, EvalResult.bind, pure, ↓reduceIte]
  rfl

theorem oracleObserveBeforeBranch {frame : Frame} {evm : EVM.State}
    (target : UInt256) (before : OracleObservation)
    (ht : frame.locals.get? "target" = some (.int (Int.ofNat target.toNat)))
    (hb : frame.locals.get? "beforeOrAt" = some before.value) (he : target = before.timestamp) :
    ExecStmt config frame evm oracleObserveSingleFunction.body[7]!
      (.returned frame evm (some before.cumulatives)) := by
  refine ExecStmt.iteTrue ?_ (ExecBlock.consReturn (ExecStmt.return (evalOracleCumulatives before hb)))
  have h := evalExpr_word_eq (evalExpr_var_get (cfg := config) (evm := evm) ht)
    (evalOracleTimestamp before hb)
  simpa only [he, decide_true] using h

theorem oracleObserveAfterBranch {frame : Frame} {evm : EVM.State}
    (target : UInt256) (before after : OracleObservation)
    (ht : frame.locals.get? "target" = some (.int (Int.ofNat target.toNat)))
    (hb : frame.locals.get? "beforeOrAt" = some before.value)
    (ha : frame.locals.get? "atOrAfter" = some after.value)
    (hne : target ≠ before.timestamp) (he : target = after.timestamp) :
    ExecStmt config frame evm oracleObserveSingleFunction.body[7]!
      (.returned frame evm (some after.cumulatives)) := by
  refine ExecStmt.iteFalse ?_ (ExecBlock.consReturn (ExecStmt.iteTrue ?_
    (ExecBlock.consReturn (ExecStmt.return (evalOracleCumulatives after ha)))))
  · have h := evalExpr_word_eq (evalExpr_var_get (cfg := config) (evm := evm) ht)
      (evalOracleTimestamp before hb)
    simpa only [hne, decide_false] using h
  · have h := evalExpr_word_eq (evalExpr_var_get (cfg := config) (evm := evm) ht)
      (evalOracleTimestamp after ha)
    simpa only [he, decide_true] using h

theorem oracleObserveNonzeroExactReturns (imms : Store) (evm : EVM.State)
    (time secondsAgo : UInt256) (tick : Int) (index liquidity cardinality : UInt256)
    (before after : OracleObservation) (hn : secondsAgo ≠ ⟨0⟩) (hin : index.toNat < 65535)
    (hc : cardinality.toNat < 2 ^ 16) (htick : -(2 ^ 23 : Int) ≤ tick ∧ tick < 2 ^ 23)
    (hrun : OracleSurroundingRun time (oracleDelta time secondsAgo) tick index liquidity cardinality
      evm.accountMap evm.executionEnv before after)
    (hexact : oracleDelta time secondsAgo = before.timestamp ∨
      oracleDelta time secondsAgo = after.timestamp) :
    ∃ frame, ExecFuncBody config
      (oracleObserveSingleFrame imms time secondsAgo tick index liquidity cardinality)
      evm oracleObserveSingleFunction.body (.returned frame evm
        (some (if oracleDelta time secondsAgo = before.timestamp then before else after).cumulatives)) := by
  let f := oracleObservePairFrame imms time secondsAgo tick index liquidity cardinality before after
  obtain ⟨ht, hb, ha⟩ := oracleObservePairGets imms time secondsAgo tick index liquidity cardinality
    before after
  have hstmt : ExecStmt config f evm oracleObserveSingleFunction.body[7]!
      (.returned f evm
        (some (if oracleDelta time secondsAgo = before.timestamp then before else after).cumulatives)) := by
    by_cases he : oracleDelta time secondsAgo = before.timestamp
    · rw [if_pos he]
      exact oracleObserveBeforeBranch _ before ht hb he
    · rw [if_neg he]
      exact oracleObserveAfterBranch _ before after ht hb ha he (hexact.resolve_left he)
  refine ⟨f, ExecFuncBody.execBlockRet ?_⟩
  rw [← List.take_append_drop 7 oracleObserveSingleFunction.body]
  apply execBlock_append_ok
    (oracleObservePairPrefix imms evm time secondsAgo tick index liquidity cardinality
      before after hn hin hc htick hrun)
  exact ExecBlock.consReturn hstmt

end Benchmarks.UniswapV3.Pool
