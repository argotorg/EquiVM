import Benchmarks.UniswapV3.Pool.OracleInterpolationSource

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.UniswapV3.Pool
set_option maxRecDepth 10000

theorem oracleObserveNonzeroInterpolationReturns (imms : Store) (evm : EVM.State)
    (time secondsAgo : UInt256) (tick : Int) (index liquidity cardinality : UInt256)
    (before after : OracleObservation) (hn : secondsAgo ≠ ⟨0⟩) (hin : index.toNat < 65535)
    (hc : cardinality.toNat < 2 ^ 16) (htick : -(2 ^ 23 : Int) ≤ tick ∧ tick < 2 ^ 23)
    (hrun : OracleSurroundingRun time (oracleDelta time secondsAgo) tick index liquidity cardinality
      evm.accountMap evm.executionEnv before after)
    (hnb : oracleDelta time secondsAgo ≠ before.timestamp)
    (hna : oracleDelta time secondsAgo ≠ after.timestamp)
    (hd : (oracleDelta after.timestamp before.timestamp).toNat ≠ 0) :
    ∃ frame, ExecFuncBody config
      (oracleObserveSingleFrame imms time secondsAgo tick index liquidity cardinality)
      evm oracleObserveSingleFunction.body (.returned frame evm
        (some (oracleInterpolatedValues before after (oracleDelta time secondsAgo)))) := by
  let f := oracleObservePairFrame imms time secondsAgo tick index liquidity cardinality before after
  obtain ⟨ht, hb, ha⟩ := oracleObservePairGets imms time secondsAgo tick index liquidity cardinality
    before after
  have hstmt := oracleObserveInterpolationBranchStep (evm := evm) (oracleDelta time secondsAgo) before after
    ht hb ha hnb hna (oracleInterpolationReturns before after (oracleDelta time secondsAgo) ht hb ha hd)
  refine ⟨oracleInterpolationFrame f before after (oracleDelta time secondsAgo),
    ExecFuncBody.execBlockRet ?_⟩
  rw [← List.take_append_drop 7 oracleObserveSingleFunction.body]
  apply execBlock_append_ok
    (oracleObservePairPrefix imms evm time secondsAgo tick index liquidity cardinality
      before after hn hin hc htick hrun)
  exact ExecBlock.consReturn hstmt

theorem oracleObserveNonzeroInterpolationReverts (imms : Store) (evm : EVM.State)
    (time secondsAgo : UInt256) (tick : Int) (index liquidity cardinality : UInt256)
    (before after : OracleObservation) (hn : secondsAgo ≠ ⟨0⟩) (hin : index.toNat < 65535)
    (hc : cardinality.toNat < 2 ^ 16) (htick : -(2 ^ 23 : Int) ≤ tick ∧ tick < 2 ^ 23)
    (hrun : OracleSurroundingRun time (oracleDelta time secondsAgo) tick index liquidity cardinality
      evm.accountMap evm.executionEnv before after)
    (hnb : oracleDelta time secondsAgo ≠ before.timestamp)
    (hna : oracleDelta time secondsAgo ≠ after.timestamp)
    (hd : (oracleDelta after.timestamp before.timestamp).toNat = 0) :
    ExecFuncBody config
      (oracleObserveSingleFrame imms time secondsAgo tick index liquidity cardinality)
      evm oracleObserveSingleFunction.body .reverted := by
  obtain ⟨ht, hb, ha⟩ := oracleObservePairGets imms time secondsAgo tick index liquidity cardinality
    before after
  have hstmt := oracleObserveInterpolationBranchStep (evm := evm) (oracleDelta time secondsAgo) before after
    ht hb ha hnb hna (oracleInterpolationReverts before after (oracleDelta time secondsAgo) ht hb ha hd)
  apply ExecFuncBody.execBlockRevert
  rw [← List.take_append_drop 7 oracleObserveSingleFunction.body]
  apply execBlock_append_ok
    (oracleObservePairPrefix imms evm time secondsAgo tick index liquidity cardinality
      before after hn hin hc htick hrun)
  exact ExecBlock.consRevert hstmt

end Benchmarks.UniswapV3.Pool
