import Benchmarks.UniswapV3.Pool.UpdatePositionPrefix
import Benchmarks.UniswapV3.Pool.SnapshotInside
import Benchmarks.UniswapV3.Pool.OracleObservationTypes

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.UniswapV3.Pool
set_option maxRecDepth 1000

def updatePositionTimeFrame (imms : Store) (a : UpdatePositionArgs) (evm : EVM.State) : Frame :=
  let locals := (updatePositionReadyFrame imms a evm).locals.insert "time"
    (.int (Int.ofNat (blockTimestampWord evm.executionEnv).toNat))
  {updatePositionReadyFrame imms a evm with locals := locals}

def updatePositionObservedFrame (imms : Store) (a : UpdatePositionArgs) (evm : EVM.State) : Frame :=
  let locals := (updatePositionTimeFrame imms a evm).locals.insert "__c2"
    (.tuple (snapshotCurrent evm.accountMap evm.executionEnv).cumulatives)
  {updatePositionTimeFrame imms a evm with locals := locals}

def updatePositionCumulativeFrame (imms : Store) (a : UpdatePositionArgs) (evm : EVM.State) : Frame :=
  let locals := (updatePositionObservedFrame imms a evm).locals.insert "tickCumulative"
    (.int (snapshotCurrent evm.accountMap evm.executionEnv).tickCumulative)
  {updatePositionObservedFrame imms a evm with locals := locals}

def updatePositionOracleFrame (imms : Store) (a : UpdatePositionArgs) (evm : EVM.State) : Frame :=
  let locals := (updatePositionCumulativeFrame imms a evm).locals.insert "secondsPerLiquidityCumulativeX128"
    (.int (Int.ofNat (snapshotCurrent evm.accountMap evm.executionEnv).secondsPerLiquidity.toNat))
  {updatePositionCumulativeFrame imms a evm with locals := locals}

def updatePositionObserveArgs : List Expr :=
  [.var "time", .intLit 0, .storage ⟨"slot0", [.field "tick"]⟩,
    .storage ⟨"slot0", [.field "observationIndex"]⟩, .storage ⟨"liquidity", []⟩,
    .storage ⟨"slot0", [.field "observationCardinality"]⟩]

def updatePositionObserveBody : List Stmt :=
  [.internalCall "_blockTimestamp" [] "time",
    .internalCall "Oracle_observeSingle" updatePositionObserveArgs "__c2",
    .letDecl "tickCumulative" (some (.elem (.int (.sint ⟨56, by decide⟩))))
      (.tupleGet (.var "__c2") 0),
    .letDecl "secondsPerLiquidityCumulativeX128" (some (.elem (.int (.uint ⟨160, by decide⟩))))
      (.tupleGet (.var "__c2") 1)]

theorem updatePositionTimestampSource (imms : Store) (evm : EVM.State) (a : UpdatePositionArgs) :
    ExecStmt config (updatePositionReadyFrame imms a evm) evm
      (.internalCall "_blockTimestamp" [] "time") (.ok (updatePositionTimeFrame imms a evm) evm) := by
  exact internalCallFunctionReturn (callee := blockTimestampFunction) (argVals := []) (locals := ∅)
    (calleeSolm := {contract := contract, locals := ∅, immutables := imms})
    (value := some [.int (Int.ofNat (blockTimestampWord evm.executionEnv).toNat)])
    (by simp only [evalExprs?, pure]) blockTimestampLookup rfl (blockTimestampReturns imms evm)

theorem evalUpdatePositionObserveArgs (imms : Store) (evm : EVM.State) (a : UpdatePositionArgs) :
    evalExprs? config (updatePositionTimeFrame imms a evm) evm updatePositionObserveArgs = .ok
      [.int (Int.ofNat (blockTimestampWord evm.executionEnv).toNat), .int 0,
        .int (slot0TickValue evm.accountMap evm.executionEnv),
        .int (Int.ofNat (slot0FieldWord 23 2 evm.accountMap evm.executionEnv).toNat),
        .int (Int.ofNat (poolLiquidityWord evm.accountMap evm.executionEnv).toNat),
        .int (Int.ofNat (slot0FieldWord 25 2 evm.accountMap evm.executionEnv).toNat)] := by
  have hslot : (updatePositionTimeFrame imms a evm).locals.get? "slot0" = none := by
    dsimp only [updatePositionTimeFrame]
    update_position_prefix_get
  have hliq : (updatePositionTimeFrame imms a evm).locals.get? "liquidity" = none := by
    dsimp only [updatePositionTimeFrame]
    update_position_prefix_get
  have ht : evalExpr? config (updatePositionTimeFrame imms a evm) evm (.var "time") =
      .ok (.int (Int.ofNat (blockTimestampWord evm.executionEnv).toNat)) :=
    evalExpr_var_get Std.HashMap.getElem?_insert_self
  have hk := evalSlot0Tick (updatePositionTimeFrame imms a evm).locals imms evm hslot
  have hi := evalSlot0ObservationIndex (updatePositionTimeFrame imms a evm).locals imms evm hslot
  have hc := evalSlot0ObservationCardinality (updatePositionTimeFrame imms a evm).locals imms evm hslot
  have hl := evalLiquidity (updatePositionTimeFrame imms a evm).locals imms evm hliq
  have hf : updatePositionTimeFrame imms a evm =
      {contract := contract, locals := (updatePositionTimeFrame imms a evm).locals,
        immutables := imms} := rfl
  rw [hf] at ht ⊢
  simp only [updatePositionObserveArgs, evalExprs?, ht, hk, hi, hc, hl,
    evalExpr?, bind, EvalResult.bind, pure]
  rfl

theorem updatePositionObserveCall (imms : Store) (evm : EVM.State) (a : UpdatePositionArgs)
    (hin : (slot0FieldWord 23 2 evm.accountMap evm.executionEnv).toNat < 65535) :
    ExecStmt config (updatePositionTimeFrame imms a evm) evm
      (.internalCall "Oracle_observeSingle" updatePositionObserveArgs "__c2")
      (.ok (updatePositionObservedFrame imms a evm) evm) := by
  obtain ⟨frame, hb⟩ := oracleObserveSingleZeroReturns imms evm
    (blockTimestampWord evm.executionEnv) (slot0TickValue evm.accountMap evm.executionEnv)
    (slot0FieldWord 23 2 evm.accountMap evm.executionEnv) (poolLiquidityWord evm.accountMap evm.executionEnv)
    (slot0FieldWord 25 2 evm.accountMap evm.executionEnv) hin (slot0TickValue_bounds _ _)
  exact internalCallFunctionReturn (callee := oracleObserveSingleFunction) (calleeSolm := frame)
    (locals := oracleObserveSingleLocals (blockTimestampWord evm.executionEnv) ⟨0⟩
      (slot0TickValue evm.accountMap evm.executionEnv) (slot0FieldWord 23 2 evm.accountMap evm.executionEnv)
      (poolLiquidityWord evm.accountMap evm.executionEnv) (slot0FieldWord 25 2 evm.accountMap evm.executionEnv))
    (value := some (snapshotCurrent evm.accountMap evm.executionEnv).cumulatives)
    (evalUpdatePositionObserveArgs imms evm a) oracleObserveSingleLookup
    (oracleObserveSingleBind _ ⟨0⟩ _ _ _ _) hb

theorem updatePositionObserveSource (imms : Store) (evm : EVM.State) (a : UpdatePositionArgs)
    (hin : (slot0FieldWord 23 2 evm.accountMap evm.executionEnv).toNat < 65535) :
    ExecBlock config (updatePositionReadyFrame imms a evm) evm updatePositionObserveBody
      (.ok (updatePositionOracleFrame imms a evm) evm) := by
  refine ExecBlock.consNormal (updatePositionTimestampSource imms evm a) ?_
  refine ExecBlock.consNormal (updatePositionObserveCall imms evm a hin) ?_
  refine ExecBlock.consNormal (solm' := updatePositionCumulativeFrame imms a evm) (evm' := evm)
    (ExecStmt.letDecl ?_) ?_
  · simp only [evalExpr?, updatePositionObservedFrame, Std.HashMap.get?_eq_getElem?,
      Std.HashMap.getElem?_insert_self, EvalResult.ofOption, bind, EvalResult.bind,
      OracleObservation.cumulatives, tupleGetValue?]
    rfl
  exact ExecBlock.consNormal (ExecStmt.letDecl (by
    simp only [evalExpr?, updatePositionCumulativeFrame, updatePositionObservedFrame,
      Std.HashMap.get?_eq_getElem?, Std.HashMap.getElem?_insert, EvalResult.ofOption, bind,
      EvalResult.bind, OracleObservation.cumulatives, tupleGetValue?]; rfl)) ExecBlock.nil

theorem updatePositionObserveReverts (imms : Store) (evm : EVM.State) (a : UpdatePositionArgs)
    (hin : ¬(slot0FieldWord 23 2 evm.accountMap evm.executionEnv).toNat < 65535) :
    ExecBlock config (updatePositionReadyFrame imms a evm) evm updatePositionObserveBody .reverted := by
  refine ExecBlock.consNormal (updatePositionTimestampSource imms evm a) (ExecBlock.consRevert ?_)
  exact internalCallFunctionRevert (callee := oracleObserveSingleFunction)
    (locals := oracleObserveSingleLocals (blockTimestampWord evm.executionEnv) ⟨0⟩
      (slot0TickValue evm.accountMap evm.executionEnv) (slot0FieldWord 23 2 evm.accountMap evm.executionEnv)
      (poolLiquidityWord evm.accountMap evm.executionEnv) (slot0FieldWord 25 2 evm.accountMap evm.executionEnv))
    (evalUpdatePositionObserveArgs imms evm a) oracleObserveSingleLookup
    (oracleObserveSingleBind _ ⟨0⟩ _ _ _ _)
    (oracleObserveSingleZeroReverts imms evm _ _ _ _ _ hin)

theorem snapshotCurrent_valid (σ : AccountMap) (ee : ExecutionEnv) : (snapshotCurrent σ ee).Valid := by
  unfold snapshotCurrent oracleObserveZeroResult
  split_ifs
  · exact oracleStoredValid _ _ _
  · exact oracleTransformedValid _ _ _ _ (blockTimestampWord_lt _)

end Benchmarks.UniswapV3.Pool
