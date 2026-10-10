import Benchmarks.UniswapV3.Pool.OracleSurroundingOldest

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.UniswapV3.Pool
set_option maxRecDepth 10000

theorem oracleSurroundingOldestGets (imms : Store) (evm : EVM.State) (time target : UInt256)
    (tick : Int) (index liquidity cardinality : UInt256) :
    let locals := (oracleSurroundingOldestFrame imms evm time target tick index
      liquidity cardinality).locals
    locals.get? "beforeOrAt" =
        some (oracleSurroundingOldest index cardinality evm.accountMap evm.executionEnv).value ∧
      locals.get? "time" = some (.int (Int.ofNat time.toNat)) ∧
      locals.get? "target" = some (.int (Int.ofNat target.toNat)) ∧
      locals.get? "index" = some (.int (Int.ofNat index.toNat)) ∧
      locals.get? "cardinality" = some (.int (Int.ofNat cardinality.toNat)) := by
  cases hi : (oracleSurroundingCandidate index cardinality
      evm.accountMap evm.executionEnv).initialized <;>
    simp [oracleSurroundingOldestFrame, oracleSurroundingOldest, hi,
      oracleSurroundingCandidateFrame, oracleSurroundingFirstFrame, oracleSurroundingReadFrame,
      oracleSurroundingZeroFrame, oracleSurroundingLocals, Std.HashMap.getElem_insert]

theorem oracleSurroundingOldestTimestamp_lt (index cardinality : UInt256)
    (σ : AccountMap) (I : ExecutionEnv) :
    (oracleSurroundingOldest index cardinality σ I).timestamp.toNat < 2 ^ 32 := by
  dsimp only [oracleSurroundingOldest]
  split <;> exact oracleStoredTimestamp_lt _ σ I

def oracleSurroundingOldEnough (time target index cardinality : UInt256)
    (σ : AccountMap) (I : ExecutionEnv) : Bool :=
  oracleLte time (oracleSurroundingOldest index cardinality σ I).timestamp target

def oracleSurroundingCompareFrame (imms : Store) (evm : EVM.State) (time target : UInt256)
    (tick : Int) (index liquidity cardinality : UInt256) : Frame :=
  { contract := contract
    immutables := imms
    locals := (oracleSurroundingOldestFrame imms evm time target tick index
      liquidity cardinality).locals.insert "__c2"
      (.bool (oracleSurroundingOldEnough time target index cardinality
        evm.accountMap evm.executionEnv)) }

theorem oracleSurroundingCompareGets (imms : Store) (evm : EVM.State) (time target : UInt256)
    (tick : Int) (index liquidity cardinality : UInt256) :
    let locals := (oracleSurroundingCompareFrame imms evm time target tick index
      liquidity cardinality).locals
    locals.get? "time" = some (.int (Int.ofNat time.toNat)) ∧
      locals.get? "target" = some (.int (Int.ofNat target.toNat)) ∧
      locals.get? "index" = some (.int (Int.ofNat index.toNat)) ∧
      locals.get? "cardinality" = some (.int (Int.ofNat cardinality.toNat)) := by
  have hg := oracleSurroundingOldestGets imms evm time target tick index liquidity cardinality
  simpa [oracleSurroundingCompareFrame, Std.HashMap.get?_eq_getElem?,
    Std.HashMap.getElem?_insert] using hg.2

theorem oracleSurroundingComparePrefix (imms : Store) (evm : EVM.State) (time target : UInt256)
    (tick : Int) (index liquidity cardinality : UInt256) (hin : index.toNat < 65535)
    (ht : target.toNat < 2 ^ 32) (hn : cardinality.toNat ≠ 0)
    (hc : cardinality.toNat < 2 ^ 16)
    (hf : oracleSurroundingFirst time target index evm.accountMap evm.executionEnv = false) :
    ExecBlock config (oracleSurroundingFrame imms time target tick index liquidity cardinality) evm
      (oracleSurroundingFunction.body.take 8)
      (.ok (oracleSurroundingCompareFrame imms evm time target tick index liquidity cardinality)
        evm) := by
  let f := oracleSurroundingOldestFrame imms evm time target tick index liquidity cardinality
  have hg := oracleSurroundingOldestGets imms evm time target tick index liquidity cardinality
  have hs : ExecStmt config f evm oracleSurroundingFunction.body[7]!
      (.ok (oracleSurroundingCompareFrame imms evm time target tick index liquidity cardinality)
        evm) := by
    apply oracleLteCall
    · change evalExprs? config f evm
        [.var "time", .field (.var "beforeOrAt") "blockTimestamp", .var "target"] = _
      have eb := evalOracleTimestamp (frame := f) (evm := evm)
        (oracleSurroundingOldest index cardinality evm.accountMap evm.executionEnv) hg.1
      have et := evalExpr_var_get (cfg := config) (evm := evm) (frame := f) hg.2.1
      have eg := evalExpr_var_get (cfg := config) (evm := evm) (frame := f) hg.2.2.1
      simp only [evalExprs?, eb, et, eg, bind, EvalResult.bind, pure]
    · exact oracleSurroundingOldestTimestamp_lt index cardinality evm.accountMap evm.executionEnv
    · exact ht
  have htail : ExecBlock config
      (oracleSurroundingCandidateFrame imms evm time target tick index liquidity cardinality) evm
      (oracleSurroundingFunction.body.drop 6 |>.take 2)
      (.ok (oracleSurroundingCompareFrame imms evm time target tick index liquidity cardinality)
        evm) :=
    ExecBlock.consNormal
      (oracleSurroundingOldestFallback imms evm time target tick index liquidity cardinality)
      (ExecBlock.consNormal hs ExecBlock.nil)
  exact execBlock_append_ok (oracleSurroundingCandidatePrefix imms evm time target tick index
    liquidity cardinality hin ht hn hc hf) htail

end Benchmarks.UniswapV3.Pool
