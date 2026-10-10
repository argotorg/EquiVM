import Benchmarks.UniswapV3.Pool.OracleSurroundingModel

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.UniswapV3.Pool
set_option maxRecDepth 10000

def oracleSurroundingCandidate (index cardinality : UInt256) (σ : AccountMap) (I : ExecutionEnv) :
    OracleObservation := oracleStoredObservation (oracleSearchLeft index cardinality) σ I

def oracleSurroundingOldest (index cardinality : UInt256) (σ : AccountMap) (I : ExecutionEnv) :
    OracleObservation :=
  let candidate := oracleSurroundingCandidate index cardinality σ I
  if candidate.initialized then candidate else oracleStoredObservation ⟨0⟩ σ I

def oracleSurroundingCandidateFrame (imms : Store) (evm : EVM.State) (time target : UInt256)
    (tick : Int) (index liquidity cardinality : UInt256) : Frame :=
  { contract := contract
    immutables := imms
    locals := (oracleSurroundingFirstFrame imms evm time target tick index
      liquidity cardinality).locals.insert "beforeOrAt"
      (oracleSurroundingCandidate index cardinality evm.accountMap evm.executionEnv).value }

def oracleSurroundingOldestFrame (imms : Store) (evm : EVM.State) (time target : UInt256)
    (tick : Int) (index liquidity cardinality : UInt256) : Frame :=
  { contract := contract
    immutables := imms
    locals := if (oracleSurroundingCandidate index cardinality evm.accountMap
        evm.executionEnv).initialized then
      (oracleSurroundingCandidateFrame imms evm time target tick index liquidity cardinality).locals
    else
      (oracleSurroundingCandidateFrame imms evm time target tick index
        liquidity cardinality).locals.insert "beforeOrAt"
      (oracleStoredObservation ⟨0⟩ evm.accountMap evm.executionEnv).value }

theorem oracleSurroundingCandidatePrefix (imms : Store) (evm : EVM.State) (time target : UInt256)
    (tick : Int) (index liquidity cardinality : UInt256) (hin : index.toNat < 65535)
    (ht : target.toNat < 2 ^ 32) (hn : cardinality.toNat ≠ 0)
    (hc : cardinality.toNat < 2 ^ 16)
    (hf : oracleSurroundingFirst time target index evm.accountMap evm.executionEnv = false) :
    ExecBlock config (oracleSurroundingFrame imms time target tick index liquidity cardinality) evm
      (oracleSurroundingFunction.body.take 6)
      (.ok (oracleSurroundingCandidateFrame imms evm time target tick index liquidity cardinality)
        evm) := by
  let f := oracleSurroundingFirstFrame imms evm time target tick index liquidity cardinality
  have hi : f.locals.get? "index" = some (.int (Int.ofNat index.toNat)) := by
    simp [f, oracleSurroundingFirstFrame, oracleSurroundingReadFrame, oracleSurroundingZeroFrame,
      oracleSurroundingLocals, Std.HashMap.getElem_insert]
  have hcard : f.locals.get? "cardinality" = some (.int (Int.ofNat cardinality.toNat)) := by
    simp [f, oracleSurroundingFirstFrame, oracleSurroundingReadFrame, oracleSurroundingZeroFrame,
      oracleSurroundingLocals, Std.HashMap.getElem_insert]
  have hbase : f.locals.get? "observations" = none := by
    simp [f, oracleSurroundingFirstFrame, oracleSurroundingReadFrame, oracleSurroundingZeroFrame,
      oracleSurroundingLocals]
  have hindex := evalOracleSearchLeft (frame := f) (evm := evm) index cardinality hi hcard hn
  have hbound : (oracleSearchLeft index cardinality).toNat < 65535 :=
    oracleSearchRemainder_lt _ cardinality hn hc
  have hread := evalOracleObservationExpr f.locals imms evm _ _ hbase hindex hbound
  have htail : ExecBlock config f evm (oracleSurroundingFunction.body.drop 4 |>.take 2)
      (.ok (oracleSurroundingCandidateFrame imms evm time target tick index liquidity cardinality)
        evm) := by
    refine ExecBlock.consNormal (ExecStmt.iteFalse ?_ ExecBlock.nil) ?_
    · exact evalExpr_var_get (by simp [f, oracleSurroundingFirstFrame, hf])
    · refine ExecBlock.consNormal (ExecStmt.assign hread ?_) ExecBlock.nil
      exact assignLocalVarBase_frame
        (old := (oracleStoredObservation index evm.accountMap evm.executionEnv).value)
        (by simp [f, oracleSurroundingFirstFrame, oracleSurroundingReadFrame,
          Std.HashMap.getElem_insert])
  exact execBlock_append_ok (oracleSurroundingFirstPrefix imms evm time target tick index
    liquidity cardinality hin ht) htail

theorem oracleSurroundingOldestFallback (imms : Store) (evm : EVM.State) (time target : UInt256)
    (tick : Int) (index liquidity cardinality : UInt256) :
    ExecStmt config
      (oracleSurroundingCandidateFrame imms evm time target tick index liquidity cardinality) evm
      oracleSurroundingFunction.body[6]!
      (.ok (oracleSurroundingOldestFrame imms evm time target tick index liquidity cardinality)
        evm) := by
  let candidate := oracleSurroundingCandidate index cardinality evm.accountMap evm.executionEnv
  let f := oracleSurroundingCandidateFrame imms evm time target tick index liquidity cardinality
  have he : evalExpr? config f evm (.unary .not (.field (.var "beforeOrAt") "initialized")) =
      .ok (.bool (!candidate.initialized)) := by
    simp [evalExpr?, f, oracleSurroundingCandidateFrame, OracleObservation.value,
      EvalResult.ofOption, lookupField?, lookupAssoc, bind, EvalResult.bind, evalUnaryOp?]
    rfl
  by_cases hi : (oracleSurroundingCandidate index cardinality
      evm.accountMap evm.executionEnv).initialized = true
  · have hh : oracleSurroundingOldestFrame imms evm time target tick index liquidity cardinality =
        f := by simp only [oracleSurroundingOldestFrame, hi, ↓reduceIte]; rfl
    rw [hh]
    exact ExecStmt.iteFalse
      (by simpa only [candidate, hi, Bool.not_true] using he) ExecBlock.nil
  · have hz : (oracleSurroundingCandidate index cardinality
        evm.accountMap evm.executionEnv).initialized = false := Bool.eq_false_of_not_eq_true hi
    have hh : oracleSurroundingOldestFrame imms evm time target tick index liquidity cardinality =
        { f with
          locals := f.locals.insert "beforeOrAt"
            (oracleStoredObservation ⟨0⟩ evm.accountMap evm.executionEnv).value } := by
      simp only [oracleSurroundingOldestFrame, hz, Bool.false_eq_true, ↓reduceIte]
      rfl
    rw [hh]
    refine ExecStmt.iteTrue (by simpa only [candidate, hz, Bool.not_false] using he) ?_
    refine ExecBlock.consNormal
      (ExecStmt.assign
        (value := (oracleStoredObservation ⟨0⟩ evm.accountMap evm.executionEnv).value)
        ?_ ?_) ExecBlock.nil
    · exact evalOracleObservationExpr f.locals imms evm (.intLit 0) ⟨0⟩
        (by simp [f, oracleSurroundingCandidateFrame, oracleSurroundingFirstFrame,
          oracleSurroundingReadFrame, oracleSurroundingZeroFrame, oracleSurroundingLocals])
        (by simp only [evalExpr?, pure]; rfl) (by decide)
    · exact assignLocalVarBase_frame (old := candidate.value)
        (by simp [oracleSurroundingCandidateFrame, candidate])

end Benchmarks.UniswapV3.Pool
