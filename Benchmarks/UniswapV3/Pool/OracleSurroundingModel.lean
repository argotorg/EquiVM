import Benchmarks.UniswapV3.Pool.OracleSearchSource

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.UniswapV3.Pool
set_option maxRecDepth 10000

def oracleSurroundingFunction : FunctionDecl := contract.functions[29]!
theorem oracleSurroundingLookup : lookupCallable? contract "Oracle_getSurroundingObservations" =
    some oracleSurroundingFunction.toCallable := rfl

def oracleSurroundingLocals (time target : UInt256) (tick : Int)
    (index liquidity cardinality : UInt256) : Store :=
  ((((((∅ : Store).insert "cardinality" (.int (Int.ofNat cardinality.toNat))).insert
    "liquidity" (.int (Int.ofNat liquidity.toNat))).insert "index"
    (.int (Int.ofNat index.toNat))).insert "tick" (.int tick)).insert
    "target" (.int (Int.ofNat target.toNat))).insert "time" (.int (Int.ofNat time.toNat))

def oracleSurroundingFrame (imms : Store) (time target : UInt256) (tick : Int)
    (index liquidity cardinality : UInt256) : Frame :=
  { contract := contract
    immutables := imms
    locals := oracleSurroundingLocals time target tick index liquidity cardinality }

theorem oracleSurroundingBind (time target : UInt256) (tick : Int)
    (index liquidity cardinality : UInt256) :
    bindParams? oracleSurroundingFunction.params [.int (Int.ofNat time.toNat),
      .int (Int.ofNat target.toNat), .int tick, .int (Int.ofNat index.toNat),
      .int (Int.ofNat liquidity.toNat), .int (Int.ofNat cardinality.toNat)] =
      some (oracleSurroundingLocals time target tick index liquidity cardinality) := rfl

def oracleSurroundingZeroFrame (imms : Store) (time target : UInt256) (tick : Int)
    (index liquidity cardinality : UInt256) : Frame :=
  { contract := contract
    immutables := imms
    locals := ((oracleSurroundingLocals time target tick index liquidity cardinality).insert
      "beforeOrAt" oracleZeroObservation.value).insert "atOrAfter" oracleZeroObservation.value }

def oracleSurroundingReadFrame (imms : Store) (evm : EVM.State) (time target : UInt256)
    (tick : Int) (index liquidity cardinality : UInt256) : Frame :=
  { contract := contract
    immutables := imms
    locals := (oracleSurroundingZeroFrame imms time target tick index
      liquidity cardinality).locals.insert "beforeOrAt"
      (oracleStoredObservation index evm.accountMap evm.executionEnv).value }

def oracleSurroundingFirst (time target index : UInt256) (σ : AccountMap)
    (I : ExecutionEnv) : Bool :=
  oracleLte time (oracleStoredObservation index σ I).timestamp target

def oracleSurroundingFirstFrame (imms : Store) (evm : EVM.State) (time target : UInt256)
    (tick : Int) (index liquidity cardinality : UInt256) : Frame :=
  { contract := contract
    immutables := imms
    locals := (oracleSurroundingReadFrame imms evm time target tick index
      liquidity cardinality).locals.insert "__c0"
      (.bool (oracleSurroundingFirst time target index evm.accountMap evm.executionEnv)) }

theorem oracleSurroundingZeroPrefix (imms : Store) (evm : EVM.State) (time target : UInt256)
    (tick : Int) (index liquidity cardinality : UInt256) :
    ExecBlock config (oracleSurroundingFrame imms time target tick index liquidity cardinality) evm
      (oracleSurroundingFunction.body.take 2)
      (.ok (oracleSurroundingZeroFrame imms time target tick index liquidity cardinality) evm) :=
  oracleObservationZeroPrefix (oracleSurroundingLocals time target tick index liquidity cardinality)
    imms evm

theorem oracleSurroundingReadPrefix (imms : Store) (evm : EVM.State) (time target : UInt256)
    (tick : Int) (index liquidity cardinality : UInt256) (hin : index.toNat < 65535) :
    ExecBlock config (oracleSurroundingFrame imms time target tick index liquidity cardinality) evm
      (oracleSurroundingFunction.body.take 3)
      (.ok (oracleSurroundingReadFrame imms evm time target tick index liquidity cardinality)
        evm) := by
  have hz := oracleSurroundingZeroPrefix imms evm time target tick index liquidity cardinality
  have he : evalExpr? config
      (oracleSurroundingZeroFrame imms time target tick index liquidity cardinality) evm
      (.storage ⟨"observations", [.aindex (.var "index")]⟩) =
      .ok (oracleStoredObservation index evm.accountMap evm.executionEnv).value := by
    apply evalOracleObservation
    · simp [oracleSurroundingLocals]
    · simp [oracleSurroundingLocals, Std.HashMap.getElem_insert]
    · exact hin
  have hs : ExecStmt config
      (oracleSurroundingZeroFrame imms time target tick index liquidity cardinality) evm
      oracleSurroundingFunction.body[2]!
      (.ok (oracleSurroundingReadFrame imms evm time target tick index liquidity cardinality)
        evm) := by
    apply ExecStmt.assign he
    exact assignLocalVarBase_frame (old := oracleZeroObservation.value)
      (by simp [oracleSurroundingZeroFrame, Std.HashMap.getElem_insert])
  exact execBlock_append_ok hz (ExecBlock.consNormal hs ExecBlock.nil)

theorem oracleSurroundingFirstPrefix (imms : Store) (evm : EVM.State) (time target : UInt256)
    (tick : Int) (index liquidity cardinality : UInt256) (hin : index.toNat < 65535)
    (ht : target.toNat < 2 ^ 32) :
    ExecBlock config (oracleSurroundingFrame imms time target tick index liquidity cardinality) evm
      (oracleSurroundingFunction.body.take 4)
      (.ok (oracleSurroundingFirstFrame imms evm time target tick index liquidity cardinality)
        evm) := by
  let frame := oracleSurroundingReadFrame imms evm time target tick index liquidity cardinality
  have hs : ExecStmt config frame evm oracleSurroundingFunction.body[3]!
      (.ok (oracleSurroundingFirstFrame imms evm time target tick index liquidity cardinality)
        evm) := by
    apply oracleLteCall
    · change evalExprs? config frame evm
        [.var "time", .field (.var "beforeOrAt") "blockTimestamp", .var "target"] = _
      have eb := evalOracleTimestamp (frame := frame) (evm := evm) (name := "beforeOrAt")
        (oracleStoredObservation index evm.accountMap evm.executionEnv)
        (by simp [frame, oracleSurroundingReadFrame])
      have et : evalExpr? config frame evm (.var "time") =
          .ok (.int (Int.ofNat time.toNat)) := evalExpr_var_get (by
        simp [frame, oracleSurroundingReadFrame, oracleSurroundingZeroFrame,
          oracleSurroundingLocals, Std.HashMap.getElem_insert])
      have eg : evalExpr? config frame evm (.var "target") =
          .ok (.int (Int.ofNat target.toNat)) := evalExpr_var_get (by
        simp [frame, oracleSurroundingReadFrame, oracleSurroundingZeroFrame,
          oracleSurroundingLocals, Std.HashMap.getElem_insert])
      simp only [evalExprs?, et, eb, eg, bind, EvalResult.bind, pure]
    · exact oracleStoredTimestamp_lt index evm.accountMap evm.executionEnv
    · exact ht
  exact execBlock_append_ok (oracleSurroundingReadPrefix imms evm time target tick index
    liquidity cardinality hin) (ExecBlock.consNormal hs ExecBlock.nil)

end Benchmarks.UniswapV3.Pool
