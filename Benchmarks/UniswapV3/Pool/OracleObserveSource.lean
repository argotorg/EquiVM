import Benchmarks.UniswapV3.Pool.OracleObservationStorage

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.UniswapV3.Pool
set_option maxRecDepth 10000

def oracleObserveSingleFunction : FunctionDecl := contract.functions[4]!
theorem oracleObserveSingleLookup :
    lookupCallable? contract "Oracle_observeSingle" = some oracleObserveSingleFunction.toCallable := rfl

def oracleObserveSingleLocals (time secondsAgo : UInt256) (tick : Int) (index liquidity cardinality : UInt256) : Store :=
  ((((((∅ : Store).insert "cardinality" (.int (Int.ofNat cardinality.toNat))).insert
    "liquidity" (.int (Int.ofNat liquidity.toNat))).insert "index" (.int (Int.ofNat index.toNat))).insert
    "tick" (.int tick)).insert "secondsAgo" (.int (Int.ofNat secondsAgo.toNat))).insert
    "time" (.int (Int.ofNat time.toNat))

def oracleObserveSingleFrame (imms : Store) (time secondsAgo : UInt256) (tick : Int)
    (index liquidity cardinality : UInt256) : Frame :=
  {contract := contract, immutables := imms, locals := oracleObserveSingleLocals time secondsAgo tick index liquidity cardinality}

theorem oracleObserveSingleBind (time secondsAgo : UInt256) (tick : Int) (index liquidity cardinality : UInt256) :
    bindParams? oracleObserveSingleFunction.params
      [.int (Int.ofNat time.toNat), .int (Int.ofNat secondsAgo.toNat), .int tick,
       .int (Int.ofNat index.toNat), .int (Int.ofNat liquidity.toNat), .int (Int.ofNat cardinality.toNat)] =
      some (oracleObserveSingleLocals time secondsAgo tick index liquidity cardinality) := rfl

def oracleObserveZeroReadyFrame (imms : Store) (time : UInt256) (tick : Int)
    (index liquidity cardinality : UInt256) : Frame :=
  {oracleObserveSingleFrame imms time ⟨0⟩ tick index liquidity cardinality with
    locals := ((oracleObserveSingleLocals time ⟨0⟩ tick index liquidity cardinality).insert
      "tickCumulative" (.int 0)).insert "secondsPerLiquidityCumulativeX128" (.int 0)}

def oracleObserveZeroLastFrame (imms : Store) (time : UInt256) (tick : Int)
    (index liquidity cardinality : UInt256) (last : OracleObservation) : Frame :=
  {oracleObserveZeroReadyFrame imms time tick index liquidity cardinality with
    locals := (oracleObserveZeroReadyFrame imms time tick index liquidity cardinality).locals.insert
      "last" last.value}

def oracleObserveZeroResult (last : OracleObservation) (time : UInt256) (tick : Int) (liquidity : UInt256) : OracleObservation :=
  if last.timestamp = time then last else oracleTransformed last time tick liquidity

def OracleObservation.cumulatives (last : OracleObservation) : List Value :=
  [.int last.tickCumulative, .int (Int.ofNat last.secondsPerLiquidity.toNat)]

def oracleObserveZeroTail : List Stmt :=
  [.ite (.binary .ne (.field (.var "last") "blockTimestamp") (.var "time"))
    [.internalCall "Oracle_transform" [.var "last", .var "time", .var "tick", .var "liquidity"] "__c0",
     .assign .localVar ⟨"last", []⟩ (.var "__c0")] [],
   .return [.field (.var "last") "tickCumulative",
     .field (.var "last") "secondsPerLiquidityCumulativeX128"]]

theorem evalOracleObserveTime (imms : Store) (evm : EVM.State) (time : UInt256) (tick : Int)
    (index liquidity cardinality : UInt256) (last : OracleObservation) :
    evalExpr? config (oracleObserveZeroLastFrame imms time tick index liquidity cardinality last) evm
      (.binary .ne (.field (.var "last") "blockTimestamp") (.var "time")) =
      .ok (.bool (decide (last.timestamp ≠ time))) := by
  simp [evalExpr?, oracleObserveZeroLastFrame, oracleObserveZeroReadyFrame, oracleObserveSingleFrame,
    oracleObserveSingleLocals, OracleObservation.value, Std.HashMap.getElem_insert,
    lookupField?, lookupAssoc, EvalResult.ofOption, bind, EvalResult.bind, evalBinaryOp?]
  apply Bool.eq_iff_iff.mpr
  simp only [beq_iff_eq, Value.int.injEq, Int.natCast_inj, decide_eq_true_eq]
  exact ⟨u256_inj, fun h => congrArg UInt256.toNat h⟩

theorem oracleObserveZeroTailReturns (imms : Store) (evm : EVM.State) (time : UInt256) (tick : Int)
    (index liquidity cardinality : UInt256) (last : OracleObservation)
    (htick : -(2 ^ 23 : Int) ≤ tick ∧ tick < 2 ^ 23) :
    ∃ frame, ExecBlock config (oracleObserveZeroLastFrame imms time tick index liquidity cardinality last) evm
      oracleObserveZeroTail (.returned frame evm (some (oracleObserveZeroResult last time tick liquidity).cumulatives)) := by
  let frame := oracleObserveZeroLastFrame imms time tick index liquidity cardinality last
  let result := oracleTransformed last time tick liquidity
  have hget : frame.locals.get? "last" = some last.value := by simp [frame, oracleObserveZeroLastFrame]
  rw [Std.HashMap.get?_eq_getElem?] at hget
  have hargs : evalExprs? config frame evm [.var "last", .var "time", .var "tick", .var "liquidity"] =
      .ok [last.value, .int (Int.ofNat time.toNat), .int tick, .int (Int.ofNat liquidity.toNat)] := by
    simp [evalExprs?, evalExpr?, frame, oracleObserveZeroLastFrame, oracleObserveZeroReadyFrame,
      oracleObserveSingleFrame, oracleObserveSingleLocals, Std.HashMap.getElem_insert,
      EvalResult.ofOption, bind, EvalResult.bind, pure]
  have hcall := internalCallFunctionReturn (cfg := config) (caller := frame) (evm := evm)
    (retVar := "__c0") (callee := oracleTransformFunction)
    hargs oracleTransformLookup (oracleTransformBind last time tick liquidity)
    (oracleTransformReturns imms evm last time tick liquidity htick)
  by_cases heq : last.timestamp = time
  · refine ⟨frame, ?_⟩
    simp only [oracleObserveZeroResult, if_pos heq]
    refine ExecBlock.consNormal (ExecStmt.iteFalse ?_ ExecBlock.nil) ?_
    · simpa only [heq, ne_self_iff_false, decide_false] using evalOracleObserveTime imms evm time tick index liquidity cardinality last
    · apply ExecBlock.consReturn
      apply ExecStmt.return
      simp [evalExprs?, evalExpr?, oracleObserveZeroLastFrame, OracleObservation.value,
        OracleObservation.cumulatives, lookupField?, lookupAssoc,
        EvalResult.ofOption, bind, EvalResult.bind, pure]
  · let called := {frame with locals := frame.locals.insert "__c0" result.value}
    let final := {called with locals := called.locals.insert "last" result.value}
    refine ⟨final, ?_⟩
    simp only [oracleObserveZeroResult, if_neg heq]
    refine ExecBlock.consNormal (solm' := final) (evm' := evm) (ExecStmt.iteTrue ?_ ?_) ?_
    · simpa only [ne_eq, heq, not_false_eq_true, decide_true] using evalOracleObserveTime imms evm time tick index liquidity cardinality last
    · refine ExecBlock.consNormal hcall ?_
      refine ExecBlock.consNormal (ExecStmt.assign (value := result.value) ?_ ?_) ExecBlock.nil
      · exact evalExpr_var_get (by simp [resumeAfterInternalCall, collapseReturns, result])
      · apply assignLocalVarBase_frame (old := last.value)
        simp [resumeAfterInternalCall, collapseReturns, hget, Std.HashMap.getElem?_insert]
    · apply ExecBlock.consReturn
      apply ExecStmt.return
      simp [evalExprs?, evalExpr?, final, OracleObservation.value,
        OracleObservation.cumulatives, lookupField?, lookupAssoc,
        EvalResult.ofOption, bind, EvalResult.bind, pure, result]


theorem evalOracleObserveZeroCondition (imms : Store) (evm : EVM.State) (time : UInt256) (tick : Int)
    (index liquidity cardinality : UInt256) :
    evalExpr? config (oracleObserveZeroReadyFrame imms time tick index liquidity cardinality) evm
      (.binary .eq (.var "secondsAgo") (.intLit 0)) = .ok (.bool true) := by
  simp [evalExpr?, oracleObserveZeroReadyFrame, oracleObserveSingleFrame, oracleObserveSingleLocals,
    Std.HashMap.getElem_insert, EvalResult.ofOption, bind, EvalResult.bind, evalBinaryOp?]

theorem oracleObserveSingleZeroReturns (imms : Store) (evm : EVM.State) (time : UInt256) (tick : Int)
    (index liquidity cardinality : UInt256) (hin : index.toNat < 65535)
    (htick : -(2 ^ 23 : Int) ≤ tick ∧ tick < 2 ^ 23) :
    ∃ frame, ExecFuncBody config (oracleObserveSingleFrame imms time ⟨0⟩ tick index liquidity cardinality) evm
      oracleObserveSingleFunction.body (.returned frame evm
        (some (oracleObserveZeroResult (oracleStoredObservation index evm.accountMap evm.executionEnv)
          time tick liquidity).cumulatives)) := by
  obtain ⟨frame, htail⟩ := oracleObserveZeroTailReturns imms evm time tick index liquidity cardinality
    (oracleStoredObservation index evm.accountMap evm.executionEnv) htick
  refine ⟨frame, ExecFuncBody.execBlockRet ?_⟩
  refine ExecBlock.consNormal (ExecStmt.letDecl (value := .int 0) (by simp only [evalExpr?, pure])) ?_
  refine ExecBlock.consNormal (ExecStmt.letDecl (value := .int 0) (by simp only [evalExpr?, pure])) ?_
  refine ExecBlock.consReturn (ExecStmt.iteTrue
    (evalOracleObserveZeroCondition imms evm time tick index liquidity cardinality) ?_)
  refine ExecBlock.consNormal (ExecStmt.letDecl ?_) htail
  exact evalOracleObservation _ imms evm "index" index
    (by simp [oracleObserveSingleFrame, oracleObserveSingleLocals])
    (by simp [oracleObserveSingleFrame, oracleObserveSingleLocals, Std.HashMap.getElem_insert]) hin

theorem oracleObserveSingleZeroReverts (imms : Store) (evm : EVM.State) (time : UInt256) (tick : Int)
    (index liquidity cardinality : UInt256) (hin : ¬ index.toNat < 65535) :
    ExecFuncBody config (oracleObserveSingleFrame imms time ⟨0⟩ tick index liquidity cardinality) evm
      oracleObserveSingleFunction.body .reverted := by
  apply ExecFuncBody.execBlockRevert
  refine ExecBlock.consNormal (ExecStmt.letDecl (value := .int 0) (by simp only [evalExpr?, pure])) ?_
  refine ExecBlock.consNormal (ExecStmt.letDecl (value := .int 0) (by simp only [evalExpr?, pure])) ?_
  refine ExecBlock.consRevert (ExecStmt.iteTrue
    (evalOracleObserveZeroCondition imms evm time tick index liquidity cardinality) ?_)
  apply ExecBlock.consRevert
  apply ExecStmt.letDeclRevert
  exact evalOracleObservationRevert _ imms evm "index" index
    (by simp [oracleObserveSingleFrame, oracleObserveSingleLocals])
    (by simp [oracleObserveSingleFrame, oracleObserveSingleLocals, Std.HashMap.getElem_insert]) hin

end Benchmarks.UniswapV3.Pool

