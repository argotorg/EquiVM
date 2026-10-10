import Benchmarks.UniswapV3.Pool.OracleObserveModel

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.UniswapV3.Pool

inductive OracleObserveLoopRun (time : UInt256) (secondsAgos : List UInt256) (tick : Int)
    (index liquidity card : UInt256) (σ : AccountMap) (I : ExecutionEnv) :
    Nat → List Value → List Value → List Value → List Value → Prop where
  | done {i ticks seconds} : secondsAgos.length ≤ i →
      OracleObserveLoopRun time secondsAgos tick index liquidity card σ I i ticks seconds ticks seconds
  | step {i ticks seconds finalTicks finalSeconds tickValue secondsValue}
      (hi : i < secondsAgos.length) :
      OracleObserveSingleRun time secondsAgos[i] tick index liquidity card σ I
        [.int tickValue, .int secondsValue] →
      OracleObserveLoopRun time secondsAgos tick index liquidity card σ I (i + 1)
        (ticks.set i (.int tickValue)) (seconds.set i (.int secondsValue)) finalTicks finalSeconds →
      OracleObserveLoopRun time secondsAgos tick index liquidity card σ I
        i ticks seconds finalTicks finalSeconds

inductive OracleObserveLoopFailure (time : UInt256) (secondsAgos : List UInt256) (tick : Int)
    (index liquidity card : UInt256) (σ : AccountMap) (I : ExecutionEnv) :
    Nat → List Value → List Value → Prop where
  | failure {i ticks seconds} (hi : i < secondsAgos.length) :
      OracleObserveSingleFailure time secondsAgos[i] tick index liquidity card σ I →
      OracleObserveLoopFailure time secondsAgos tick index liquidity card σ I i ticks seconds
  | step {i ticks seconds tickValue secondsValue} (hi : i < secondsAgos.length) :
      OracleObserveSingleRun time secondsAgos[i] tick index liquidity card σ I
        [.int tickValue, .int secondsValue] →
      OracleObserveLoopFailure time secondsAgos tick index liquidity card σ I (i + 1)
        (ticks.set i (.int tickValue)) (seconds.set i (.int secondsValue)) →
      OracleObserveLoopFailure time secondsAgos tick index liquidity card σ I i ticks seconds

theorem OracleObserveLoopRun.lengths {time : UInt256} {secondsAgos : List UInt256} {tick : Int}
    {index liquidity card : UInt256} {σ : AccountMap} {I : ExecutionEnv}
    {i : Nat} {ticks seconds finalTicks finalSeconds : List Value}
    (h : OracleObserveLoopRun time secondsAgos tick index liquidity card σ I
      i ticks seconds finalTicks finalSeconds) :
    finalTicks.length = ticks.length ∧ finalSeconds.length = seconds.length := by
  induction h with
  | done => exact ⟨rfl, rfl⟩
  | step _ _ _ ih => simpa only [List.length_set] using ih

end Benchmarks.UniswapV3.Pool
