import Benchmarks.UniswapV3.Pool.OracleObserveSource
import Benchmarks.UniswapV3.Pool.OracleSurroundingFailure

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.UniswapV3.Pool
set_option maxRecDepth 10000

-- A shared expression rule for the oracle's wrapping timestamp differences.
theorem evalOracleDelta {cfg : Config} {frame : Frame} {evm : EVM.State}
    {lhs rhs : Expr} {time previous : UInt256}
    (ht : evalExpr? cfg frame evm lhs = .ok (.int (Int.ofNat time.toNat)))
    (hp : evalExpr? cfg frame evm rhs = .ok (.int (Int.ofNat previous.toNat))) :
    evalExpr? cfg frame evm (.cast (.binary .sub lhs rhs) (.elem (.int (.uint ⟨32, by decide⟩)))) =
      .ok (.int (Int.ofNat (oracleDelta time previous).toNat)) := by
  simp only [evalExpr?, ht, hp, bind, EvalResult.bind, evalBinaryOp?, castValue?, oracleDelta_source]
  rfl

def oracleObserveReadyFrame (imms : Store) (time secondsAgo : UInt256) (tick : Int)
    (index liquidity cardinality : UInt256) : Frame :=
  { contract := contract
    immutables := imms
    locals := ((oracleObserveSingleLocals time secondsAgo tick index liquidity cardinality).insert
      "tickCumulative" (.int 0)).insert "secondsPerLiquidityCumulativeX128" (.int 0) }

def oracleObserveTargetFrame (imms : Store) (time secondsAgo : UInt256) (tick : Int)
    (index liquidity cardinality : UInt256) : Frame :=
  { contract := contract
    immutables := imms
    locals := (oracleObserveReadyFrame imms time secondsAgo tick index liquidity cardinality).locals
      |>.insert "target" (.int (Int.ofNat (oracleDelta time secondsAgo).toNat)) }

theorem oracleObserveNonzeroPrefix (imms : Store) (evm : EVM.State)
    (time secondsAgo : UInt256) (tick : Int) (index liquidity cardinality : UInt256)
    (hn : secondsAgo ≠ ⟨0⟩) :
    ExecBlock config (oracleObserveSingleFrame imms time secondsAgo tick index liquidity cardinality)
      evm (oracleObserveSingleFunction.body.take 4)
      (.ok (oracleObserveTargetFrame imms time secondsAgo tick index liquidity cardinality) evm) := by
  refine ExecBlock.consNormal (ExecStmt.letDecl (value := .int 0) (by simp only [evalExpr?, pure])) ?_
  refine ExecBlock.consNormal (ExecStmt.letDecl (value := .int 0) (by simp only [evalExpr?, pure])) ?_
  change ExecBlock config
    (oracleObserveReadyFrame imms time secondsAgo tick index liquidity cardinality) evm
    (oracleObserveSingleFunction.body.drop 2 |>.take 2) _
  refine ExecBlock.consNormal (ExecStmt.iteFalse ?_ ExecBlock.nil) ?_
  · have ha : evalExpr? config
        (oracleObserveReadyFrame imms time secondsAgo tick index liquidity cardinality) evm
        (.var "secondsAgo") = .ok (.int (Int.ofNat secondsAgo.toNat)) :=
      evalExpr_var_get (by simp [oracleObserveReadyFrame, oracleObserveSingleLocals,
        Std.HashMap.getElem_insert])
    have hz : evalExpr? config
        (oracleObserveReadyFrame imms time secondsAgo tick index liquidity cardinality) evm
        (.intLit 0) = .ok (.int (Int.ofNat (⟨0⟩ : UInt256).toNat)) := by
      simp only [evalExpr?, pure]
      rfl
    simpa only [hn, decide_false] using evalExpr_word_eq ha hz
  refine ExecBlock.consNormal (ExecStmt.letDecl ?_) ExecBlock.nil
  apply evalOracleDelta
  · exact evalExpr_var_get (by simp [oracleObserveReadyFrame, oracleObserveSingleLocals,
      Std.HashMap.getElem_insert])
  · exact evalExpr_var_get (by simp [oracleObserveReadyFrame, oracleObserveSingleLocals,
      Std.HashMap.getElem_insert])

theorem oracleObserveSurroundingArgs (imms : Store) (evm : EVM.State)
    (time secondsAgo : UInt256) (tick : Int) (index liquidity cardinality : UInt256) :
    evalExprs? config (oracleObserveTargetFrame imms time secondsAgo tick index liquidity cardinality)
      evm [.var "time", .var "target", .var "tick", .var "index", .var "liquidity", .var "cardinality"] =
      .ok [.int (Int.ofNat time.toNat), .int (Int.ofNat (oracleDelta time secondsAgo).toNat),
        .int tick, .int (Int.ofNat index.toNat), .int (Int.ofNat liquidity.toNat),
        .int (Int.ofNat cardinality.toNat)] := by
  simp [evalExprs?, evalExpr?, oracleObserveTargetFrame, oracleObserveReadyFrame,
    oracleObserveSingleLocals, Std.HashMap.getElem_insert, EvalResult.ofOption,
    bind, EvalResult.bind, pure]

theorem oracleObserveNonzeroSurroundingReverts (imms : Store) (evm : EVM.State)
    (time secondsAgo : UInt256) (tick : Int) (index liquidity cardinality : UInt256)
    (hn : secondsAgo ≠ ⟨0⟩) (hc : cardinality.toNat < 2 ^ 16)
    (hfail : OracleSurroundingFailure time (oracleDelta time secondsAgo)
      index cardinality evm.accountMap evm.executionEnv) :
    ExecFuncBody config
      (oracleObserveSingleFrame imms time secondsAgo tick index liquidity cardinality)
      evm oracleObserveSingleFunction.body .reverted := by
  apply ExecFuncBody.execBlockRevert
  rw [← List.take_append_drop 4 oracleObserveSingleFunction.body]
  apply execBlock_append_ok
    (oracleObserveNonzeroPrefix imms evm time secondsAgo tick index liquidity cardinality hn)
  apply ExecBlock.consRevert
  exact internalCallFunctionRevert
    (oracleObserveSurroundingArgs imms evm time secondsAgo tick index liquidity cardinality)
    oracleSurroundingLookup (oracleSurroundingBind time (oracleDelta time secondsAgo)
      tick index liquidity cardinality)
    (oracleSurroundingReverts imms evm time (oracleDelta time secondsAgo) tick index liquidity
      cardinality (oracleDelta_lt _ _) hc hfail)

end Benchmarks.UniswapV3.Pool
