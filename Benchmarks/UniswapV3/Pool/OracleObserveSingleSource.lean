import Benchmarks.UniswapV3.Pool.OracleObserveInterpolation

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.UniswapV3.Pool

inductive OracleObserveSingleRun (time secondsAgo : UInt256) (tick : Int)
    (index liquidity card : UInt256) (σ : AccountMap) (I : ExecutionEnv) : List Value → Prop where
  | zero : secondsAgo = ⟨0⟩ → index.toNat < 65535 →
      OracleObserveSingleRun time secondsAgo tick index liquidity card σ I
        (oracleObserveZeroResult (oracleStoredObservation index σ I) time tick liquidity).cumulatives
  | observation {before after} : secondsAgo ≠ ⟨0⟩ → index.toNat < 65535 →
      OracleSurroundingRun time (oracleDelta time secondsAgo) tick index liquidity card σ I before after →
      (oracleDelta time secondsAgo = before.timestamp ∨ oracleDelta time secondsAgo = after.timestamp) →
      OracleObserveSingleRun time secondsAgo tick index liquidity card σ I
        (if oracleDelta time secondsAgo = before.timestamp then before else after).cumulatives
  | interpolated {before after} : secondsAgo ≠ ⟨0⟩ → index.toNat < 65535 →
      OracleSurroundingRun time (oracleDelta time secondsAgo) tick index liquidity card σ I before after →
      oracleDelta time secondsAgo ≠ before.timestamp → oracleDelta time secondsAgo ≠ after.timestamp →
      (oracleDelta after.timestamp before.timestamp).toNat ≠ 0 →
      OracleObserveSingleRun time secondsAgo tick index liquidity card σ I
        (oracleInterpolatedValues before after (oracleDelta time secondsAgo))

inductive OracleObserveSingleFailure (time secondsAgo : UInt256) (tick : Int)
    (index liquidity card : UInt256) (σ : AccountMap) (I : ExecutionEnv) : Prop where
  | zeroIndex : secondsAgo = ⟨0⟩ → ¬ index.toNat < 65535 →
      OracleObserveSingleFailure time secondsAgo tick index liquidity card σ I
  | surrounding : secondsAgo ≠ ⟨0⟩ →
      OracleSurroundingFailure time (oracleDelta time secondsAgo) index card σ I →
      OracleObserveSingleFailure time secondsAgo tick index liquidity card σ I
  | interpolation {before after} : secondsAgo ≠ ⟨0⟩ → index.toNat < 65535 →
      OracleSurroundingRun time (oracleDelta time secondsAgo) tick index liquidity card σ I before after →
      oracleDelta time secondsAgo ≠ before.timestamp → oracleDelta time secondsAgo ≠ after.timestamp →
      (oracleDelta after.timestamp before.timestamp).toNat = 0 →
      OracleObserveSingleFailure time secondsAgo tick index liquidity card σ I

theorem oracleObserveSingleReturns (imms : Store) (evm : EVM.State)
    (time secondsAgo : UInt256) (tick : Int) (index liquidity card : UInt256) (values : List Value)
    (hc : card.toNat < 2 ^ 16) (htick : -(2 ^ 23 : Int) ≤ tick ∧ tick < 2 ^ 23)
    (hrun : OracleObserveSingleRun time secondsAgo tick index liquidity card
      evm.accountMap evm.executionEnv values) :
    ∃ frame, ExecFuncBody config (oracleObserveSingleFrame imms time secondsAgo tick index liquidity card)
      evm oracleObserveSingleFunction.body (.returned frame evm (some values)) := by
  cases hrun with
  | zero hz hi =>
      subst secondsAgo
      exact oracleObserveSingleZeroReturns imms evm time tick index liquidity card hi htick
  | observation hn hi hs he =>
      exact oracleObserveNonzeroExactReturns imms evm time secondsAgo tick index liquidity card
        _ _ hn hi hc htick hs he
  | interpolated hn hi hs hnb hna hd =>
      exact oracleObserveNonzeroInterpolationReturns imms evm time secondsAgo tick index liquidity card
        _ _ hn hi hc htick hs hnb hna hd

theorem oracleObserveSingleReverts (imms : Store) (evm : EVM.State)
    (time secondsAgo : UInt256) (tick : Int) (index liquidity card : UInt256)
    (hc : card.toNat < 2 ^ 16) (htick : -(2 ^ 23 : Int) ≤ tick ∧ tick < 2 ^ 23)
    (hfail : OracleObserveSingleFailure time secondsAgo tick index liquidity card
      evm.accountMap evm.executionEnv) :
    ExecFuncBody config (oracleObserveSingleFrame imms time secondsAgo tick index liquidity card)
      evm oracleObserveSingleFunction.body .reverted := by
  cases hfail with
  | zeroIndex hz hi =>
      subst secondsAgo
      exact oracleObserveSingleZeroReverts imms evm time tick index liquidity card hi
  | surrounding hn hf =>
      exact oracleObserveNonzeroSurroundingReverts imms evm time secondsAgo tick index liquidity card hn hc hf
  | interpolation hn hi hs hnb hna hd =>
      exact oracleObserveNonzeroInterpolationReverts imms evm time secondsAgo tick index liquidity card
        _ _ hn hi hc htick hs hnb hna hd

end Benchmarks.UniswapV3.Pool
