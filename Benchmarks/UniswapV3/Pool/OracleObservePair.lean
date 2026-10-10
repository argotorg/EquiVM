import Benchmarks.UniswapV3.Pool.OracleObserveNonzeroModel

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.UniswapV3.Pool
set_option maxRecDepth 10000

def oracleObservePairFrame (imms : Store) (time secondsAgo : UInt256) (tick : Int)
    (index liquidity cardinality : UInt256) (before after : OracleObservation) : Frame :=
  { contract := contract
    immutables := imms
    locals := (((oracleObserveTargetFrame imms time secondsAgo tick index liquidity cardinality).locals
      |>.insert "__c1" (.tuple [before.value, after.value])).insert "beforeOrAt" before.value).insert
      "atOrAfter" after.value }

theorem oracleObservePairPrefix (imms : Store) (evm : EVM.State)
    (time secondsAgo : UInt256) (tick : Int) (index liquidity cardinality : UInt256)
    (before after : OracleObservation) (hn : secondsAgo ≠ ⟨0⟩) (hin : index.toNat < 65535)
    (hc : cardinality.toNat < 2 ^ 16) (htick : -(2 ^ 23 : Int) ≤ tick ∧ tick < 2 ^ 23)
    (hrun : OracleSurroundingRun time (oracleDelta time secondsAgo) tick index liquidity cardinality
      evm.accountMap evm.executionEnv before after) :
    ExecBlock config (oracleObserveSingleFrame imms time secondsAgo tick index liquidity cardinality)
      evm (oracleObserveSingleFunction.body.take 7)
      (.ok (oracleObservePairFrame imms time secondsAgo tick index liquidity cardinality before after)
        evm) := by
  let f := oracleObserveTargetFrame imms time secondsAgo tick index liquidity cardinality
  obtain ⟨calleeFrame, hbody⟩ := oracleSurroundingReturns imms evm time (oracleDelta time secondsAgo)
    tick index liquidity cardinality before after hin (oracleDelta_lt _ _) hc htick hrun
  have hcall := internalCallFunctionReturn (cfg := config) (caller := f) (evm := evm)
    (callee := oracleSurroundingFunction) (calleeSolm := calleeFrame)
    (retVar := "__c1") (value := some [before.value, after.value])
    (oracleObserveSurroundingArgs imms evm time secondsAgo tick index liquidity cardinality)
    oracleSurroundingLookup (oracleSurroundingBind time (oracleDelta time secondsAgo)
      tick index liquidity cardinality) hbody
  have htail : ExecBlock config f evm (oracleObserveSingleFunction.body.drop 4 |>.take 3)
      (.ok (oracleObservePairFrame imms time secondsAgo tick index liquidity cardinality before after)
        evm) := by
    refine ExecBlock.consNormal hcall ?_
    refine ExecBlock.consNormal (ExecStmt.letDecl (value := before.value) ?_) ?_
    · simp [evalExpr?, resumeAfterInternalCall, collapseReturns, EvalResult.ofOption,
        tupleGetValue?, bind, EvalResult.bind]
    refine ExecBlock.consNormal (ExecStmt.letDecl (value := after.value) ?_) ExecBlock.nil
    simp [evalExpr?, resumeAfterInternalCall, collapseReturns, EvalResult.ofOption,
      tupleGetValue?, bind, EvalResult.bind, Std.HashMap.getElem_insert]
  exact execBlock_append_ok
    (oracleObserveNonzeroPrefix imms evm time secondsAgo tick index liquidity cardinality hn) htail

theorem oracleObservePairGets (imms : Store) (time secondsAgo : UInt256) (tick : Int)
    (index liquidity cardinality : UInt256) (before after : OracleObservation) :
    let f := oracleObservePairFrame imms time secondsAgo tick index liquidity cardinality before after
    f.locals.get? "target" = some (.int (Int.ofNat (oracleDelta time secondsAgo).toNat)) ∧
      f.locals.get? "beforeOrAt" = some before.value ∧
      f.locals.get? "atOrAfter" = some after.value := by
  simp [oracleObservePairFrame, oracleObserveTargetFrame, Std.HashMap.getElem_insert]

end Benchmarks.UniswapV3.Pool
