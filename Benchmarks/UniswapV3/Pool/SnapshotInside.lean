import Benchmarks.UniswapV3.Pool.SnapshotBranches

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables Benchmarks.UniswapV3.Pool.Immutables
namespace Benchmarks.UniswapV3.Pool
set_option maxRecDepth 10000

def snapshotTimeFrame (v : UniswapV3PoolImmutables) (lower upper : Int)
    (σ : AccountMap) (I : ExecutionEnv) : Frame :=
  { (snapshotReadyFrame v lower upper σ I) with
    locals := (snapshotReadyFrame v lower upper σ I).locals.insert "time"
      (.int (Int.ofNat (blockTimestampWord I).toNat)) }
def snapshotObservedFrame (v : UniswapV3PoolImmutables) (lower upper : Int)
    (σ : AccountMap) (I : ExecutionEnv) : Frame :=
  { (snapshotTimeFrame v lower upper σ I) with
    locals := (snapshotTimeFrame v lower upper σ I).locals.insert "__c11"
      (.tuple (snapshotCurrent σ I).cumulatives) }
def snapshotInsideFrame (v : UniswapV3PoolImmutables) (lower upper : Int)
    (σ : AccountMap) (I : ExecutionEnv) : Frame :=
  { (snapshotObservedFrame v lower upper σ I) with
    locals := ((snapshotObservedFrame v lower upper σ I).locals.insert "tickCumulative"
      (.int (snapshotCurrent σ I).tickCumulative)).insert "secondsPerLiquidityCumulativeX128"
      (.int (Int.ofNat (snapshotCurrent σ I).secondsPerLiquidity.toNat)) }

def snapshotObserveArgs : List Expr :=
  [.var "time", .intLit 0, .field (.var "_slot0") "tick",
   .field (.var "_slot0") "observationIndex", .storage ⟨"liquidity", []⟩,
   .field (.var "_slot0") "observationCardinality"]
def snapshotInsideBody : List Stmt :=
  [.internalCall "_blockTimestamp" [] "time",
   .internalCall "Oracle_observeSingle" snapshotObserveArgs "__c11",
   .letDecl "tickCumulative" (some (.elem (.int (.sint ⟨56, by decide⟩))))
     (.tupleGet (.var "__c11") 0),
   .letDecl "secondsPerLiquidityCumulativeX128" (some (.elem (.int (.uint ⟨160, by decide⟩))))
     (.tupleGet (.var "__c11") 1),
   .return [
     .cast (.binary .sub
       (.cast (.binary .sub (.var "tickCumulative") (.var "tickCumulativeLower"))
         (.elem (.int (.sint ⟨56, by decide⟩)))) (.var "tickCumulativeUpper"))
       (.elem (.int (.sint ⟨56, by decide⟩))),
     .cast (.binary .sub
       (.cast (.binary .sub (.var "secondsPerLiquidityCumulativeX128")
         (.var "secondsPerLiquidityOutsideLowerX128")) (.elem (.int (.uint ⟨160, by decide⟩))))
       (.var "secondsPerLiquidityOutsideUpperX128")) (.elem (.int (.uint ⟨160, by decide⟩))),
     .cast (.binary .sub
       (.cast (.binary .sub (.var "time") (.var "secondsOutsideLower"))
         (.elem (.int (.uint ⟨32, by decide⟩)))) (.var "secondsOutsideUpper"))
       (.elem (.int (.uint ⟨32, by decide⟩)))]]

theorem snapshotTimestampCall (v : UniswapV3PoolImmutables) (evm : EVM.State) (lower upper : Int) :
    ExecStmt config (snapshotReadyFrame v lower upper evm.accountMap evm.executionEnv) evm
      (.internalCall "_blockTimestamp" [] "time")
      (.ok (snapshotTimeFrame v lower upper evm.accountMap evm.executionEnv) evm) := by
  exact internalCallFunctionReturn (callee := blockTimestampFunction) (argVals := []) (locals := ∅)
    (calleeSolm := {contract := contract, locals := ∅, immutables := immStore v})
    (value := some [.int (Int.ofNat (blockTimestampWord evm.executionEnv).toNat)])
    (by simp only [evalExprs?, pure]) blockTimestampLookup rfl (blockTimestampReturns (immStore v) evm)

theorem evalSnapshotObserveArgs (v : UniswapV3PoolImmutables) (evm : EVM.State) (lower upper : Int) :
    evalExprs? config (snapshotTimeFrame v lower upper evm.accountMap evm.executionEnv) evm
      snapshotObserveArgs = .ok [
        .int (Int.ofNat (blockTimestampWord evm.executionEnv).toNat), .int 0,
        .int (slot0TickValue evm.accountMap evm.executionEnv),
        .int (Int.ofNat (slot0FieldWord 23 2 evm.accountMap evm.executionEnv).toNat),
        .int (Int.ofNat (poolLiquidityWord evm.accountMap evm.executionEnv).toNat),
        .int (Int.ofNat (slot0FieldWord 25 2 evm.accountMap evm.executionEnv).toNat)] := by
  have hl := evalLiquidity (snapshotTimeFrame v lower upper evm.accountMap evm.executionEnv).locals
    (immStore v) evm (by
      simp [snapshotTimeFrame, snapshotReadyFrame, snapshotBothFrame, snapshotUpperReadFrame,
        snapshotLowerFrame, snapshotLowerReadFrame, snapshotAliasesFrame, snapshotLowerAliasFrame,
        snapshotZerosFrame, snapshotCheckedFrame, snapshotDelegateFrame, snapshotInitialFrame,
        snapshotLocals, checkTicksLocals])
  have hl' : evalExpr? config (snapshotTimeFrame v lower upper evm.accountMap evm.executionEnv) evm
      (.storage ⟨"liquidity", []⟩) =
      .ok (.int (Int.ofNat (poolLiquidityWord evm.accountMap evm.executionEnv).toNat)) := hl
  simp only [snapshotObserveArgs, evalExprs?, hl', bind, EvalResult.bind, pure]
  simp [evalExpr?, snapshotTimeFrame, snapshotReadyFrame, Std.HashMap.getElem_insert, slot0StructValue,
    lookupField?, lookupAssoc, EvalResult.ofOption, bind, EvalResult.bind, pure, poolLiquidityWord]

theorem slot0TickValue_bounds (σ : AccountMap) (I : ExecutionEnv) :
    -(2 ^ 23 : Int) ≤ slot0TickValue σ I ∧ slot0TickValue σ I < 2 ^ 23 :=
  normalizeSint_bounds ⟨24, by decide⟩ _

theorem snapshotObserveCall (v : UniswapV3PoolImmutables) (evm : EVM.State) (lower upper : Int)
    (hin : (slot0FieldWord 23 2 evm.accountMap evm.executionEnv).toNat < 65535) :
    ExecStmt config (snapshotTimeFrame v lower upper evm.accountMap evm.executionEnv) evm
      (.internalCall "Oracle_observeSingle" snapshotObserveArgs "__c11")
      (.ok (snapshotObservedFrame v lower upper evm.accountMap evm.executionEnv) evm) := by
  obtain ⟨frame, hbody⟩ := oracleObserveSingleZeroReturns (immStore v) evm
    (blockTimestampWord evm.executionEnv) (slot0TickValue evm.accountMap evm.executionEnv)
    (slot0FieldWord 23 2 evm.accountMap evm.executionEnv) (poolLiquidityWord evm.accountMap evm.executionEnv)
    (slot0FieldWord 25 2 evm.accountMap evm.executionEnv) hin (slot0TickValue_bounds _ _)
  exact internalCallFunctionReturn (callee := oracleObserveSingleFunction)
    (locals := oracleObserveSingleLocals (blockTimestampWord evm.executionEnv) ⟨0⟩
      (slot0TickValue evm.accountMap evm.executionEnv) (slot0FieldWord 23 2 evm.accountMap evm.executionEnv)
      (poolLiquidityWord evm.accountMap evm.executionEnv) (slot0FieldWord 25 2 evm.accountMap evm.executionEnv))
    (calleeSolm := frame) (value := some (snapshotCurrent evm.accountMap evm.executionEnv).cumulatives)
    (evalSnapshotObserveArgs v evm lower upper) oracleObserveSingleLookup
    (oracleObserveSingleBind _ ⟨0⟩ _ _ _ _) hbody

theorem snapshotInsideReturns (v : UniswapV3PoolImmutables) (evm : EVM.State) (lower upper : Int)
    (hin : (slot0FieldWord 23 2 evm.accountMap evm.executionEnv).toNat < 65535) :
    ExecBlock config (snapshotReadyFrame v lower upper evm.accountMap evm.executionEnv) evm
      snapshotInsideBody (.returned (snapshotInsideFrame v lower upper evm.accountMap evm.executionEnv) evm
        (some (snapshotInside (snapshotCurrent evm.accountMap evm.executionEnv)
          (blockTimestampWord evm.executionEnv) (tickOutside lower evm.accountMap evm.executionEnv)
          (tickOutside upper evm.accountMap evm.executionEnv)).values)) := by
  refine ExecBlock.consNormal (snapshotTimestampCall v evm lower upper) ?_
  refine ExecBlock.consNormal (snapshotObserveCall v evm lower upper hin) ?_
  refine ExecBlock.consNormal (ExecStmt.letDecl (value := .int (snapshotCurrent evm.accountMap evm.executionEnv).tickCumulative) ?_) ?_
  · simp [evalExpr?, snapshotObservedFrame, OracleObservation.cumulatives,
      EvalResult.ofOption, bind, EvalResult.bind, tupleGetValue?]
  refine ExecBlock.consNormal (solm' := snapshotInsideFrame v lower upper evm.accountMap evm.executionEnv)
    (evm' := evm) (ExecStmt.letDecl ?_) ?_
  · simp [evalExpr?, snapshotObservedFrame, OracleObservation.cumulatives, Std.HashMap.getElem_insert,
      EvalResult.ofOption, bind, EvalResult.bind, tupleGetValue?]
  apply ExecBlock.consReturn (ExecStmt.return ?_)
  simp [evalExprs?, evalExpr?, snapshotInsideFrame, snapshotObservedFrame, snapshotTimeFrame,
    snapshotReadyFrame, snapshotBothFrame, snapshotUpperReadFrame, snapshotLowerFrame,
    snapshotLowerReadFrame, Std.HashMap.getElem_insert, EvalResult.ofOption, bind, EvalResult.bind,
    pure, castValue?, evalBinaryOp?, snapshotInside, SnapshotCumulatives.values]

theorem snapshotInsideReverts (v : UniswapV3PoolImmutables) (evm : EVM.State) (lower upper : Int)
    (hin : ¬ (slot0FieldWord 23 2 evm.accountMap evm.executionEnv).toNat < 65535) :
    ExecBlock config (snapshotReadyFrame v lower upper evm.accountMap evm.executionEnv) evm
      snapshotInsideBody .reverted := by
  refine ExecBlock.consNormal (snapshotTimestampCall v evm lower upper) ?_
  apply ExecBlock.consRevert
  exact internalCallFunctionRevert (callee := oracleObserveSingleFunction)
    (locals := oracleObserveSingleLocals (blockTimestampWord evm.executionEnv) ⟨0⟩
      (slot0TickValue evm.accountMap evm.executionEnv) (slot0FieldWord 23 2 evm.accountMap evm.executionEnv)
      (poolLiquidityWord evm.accountMap evm.executionEnv) (slot0FieldWord 25 2 evm.accountMap evm.executionEnv))
    (evalSnapshotObserveArgs v evm lower upper) oracleObserveSingleLookup
    (oracleObserveSingleBind _ ⟨0⟩ _ _ _ _)
    (oracleObserveSingleZeroReverts (immStore v) evm _ _ _ _ _ hin)

end Benchmarks.UniswapV3.Pool
