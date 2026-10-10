import Benchmarks.UniswapV3.Pool.OracleSurroundingLatest
import Benchmarks.UniswapV3.Pool.OracleSurroundingSearch
import Benchmarks.UniswapV3.Pool.OracleSurroundingReverts

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.UniswapV3.Pool

inductive OracleSurroundingRun (time target : UInt256) (tick : Int)
    (index liquidity cardinality : UInt256) (σ : AccountMap) (I : ExecutionEnv) :
    OracleObservation → OracleObservation → Prop where
  | latest : oracleSurroundingFirst time target index σ I = true →
      OracleSurroundingRun time target tick index liquidity cardinality σ I
        (oracleStoredObservation index σ I)
        (oracleSurroundingLatestAfter (oracleStoredObservation index σ I) target tick liquidity)
  | search {before after} :
      oracleSurroundingFirst time target index σ I = false →
      oracleSurroundingOldEnough time target index cardinality σ I = true →
      cardinality.toNat ≠ 0 →
      OracleSearchRun time target cardinality σ I (oracleSearchLeft index cardinality)
        (oracleSearchRight index cardinality) before after →
      OracleSurroundingRun time target tick index liquidity cardinality σ I before after

theorem oracleSurroundingReturns (imms : Store) (evm : EVM.State) (time target : UInt256)
    (tick : Int) (index liquidity cardinality : UInt256) (before after : OracleObservation)
    (hin : index.toNat < 65535) (ht : target.toNat < 2 ^ 32)
    (hc : cardinality.toNat < 2 ^ 16) (htick : -(2 ^ 23 : Int) ≤ tick ∧ tick < 2 ^ 23)
    (hrun : OracleSurroundingRun time target tick index liquidity cardinality
      evm.accountMap evm.executionEnv before after) :
    ∃ frame, ExecFuncBody config
      (oracleSurroundingFrame imms time target tick index liquidity cardinality)
      evm oracleSurroundingFunction.body
        (.returned frame evm (some [before.value, after.value])) := by
  cases hrun with
  | latest hf =>
      exact oracleSurroundingLatestReturns imms evm time target tick index liquidity cardinality
        hin ht htick hf
  | search hf ho hn hs =>
      exact oracleSurroundingSearchReturns imms evm time target tick index liquidity cardinality
        before after hin ht hn hc hf ho hs

end Benchmarks.UniswapV3.Pool
