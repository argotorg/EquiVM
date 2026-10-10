import Benchmarks.UniswapV3.Pool.OracleObserveLoopResult
import Benchmarks.UniswapV3.Pool.OracleObserveBodySource

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables Benchmarks.UniswapV3.Pool.Immutables
namespace Benchmarks.UniswapV3.Pool

inductive OracleObserveFailure (time : UInt256) (secondsAgos : List UInt256) (tick : Int)
    (index liquidity card : UInt256) (σ : AccountMap) (I : ExecutionEnv) : Prop where
  | cardinality : card.toNat = 0 → OracleObserveFailure time secondsAgos tick index liquidity card σ I
  | loop : OracleObserveLoopFailure time secondsAgos tick index liquidity card σ I 0
      (List.replicate secondsAgos.length (.int 0)) (List.replicate secondsAgos.length (.int 0)) →
      OracleObserveFailure time secondsAgos tick index liquidity card σ I

theorem oracleObserveFailureReverts (imms : Store) (evm : EVM.State) (time : UInt256)
    (secondsAgos : List UInt256) (tick : Int) (index liquidity card : UInt256)
    (hc : card.toNat < 2 ^ 16) (ht : -(2 ^ 23 : Int) ≤ tick ∧ tick < 2 ^ 23)
    (hn : secondsAgos.length ≤ 2 ^ 64 - 1)
    (hf : OracleObserveFailure time secondsAgos tick index liquidity card evm.accountMap evm.executionEnv) :
    ExecFuncBody config (oracleObserveFrame imms time secondsAgos tick index liquidity card)
      evm oracleObserveFunction.body .reverted := by
  by_cases hz : card.toNat = 0
  · have hzword : card = (⟨0⟩ : UInt256) := u256_inj hz
    simpa only [hzword] using oracleObserveRevertsZero imms evm time secondsAgos tick index liquidity
  · cases hf with
    | cardinality h => exact False.elim (hz h)
    | loop h => exact oracleObserveLoopReverts imms evm time secondsAgos tick index liquidity card hz hc ht hn h

abbrev OracleObserveOutcome (v : UniswapV3PoolImmutables) (ee : ExecutionEnv) (g : Sat256)
    (s0 : EVM.State) (σ : AccountMap) (rdata : ByteArray) (ret : UInt256) (R : List UInt256)
    (time : UInt256) (rawAgos : List UInt256) (tick : Int) (index liquidity card agoPtr : UInt256)
    (initMem : ByteArray) (initAw initFree : UInt256) (initCost : Nat) : Prop :=
  X (g.toNat + 1) (D_J (deployedRuntime v) 0) s0 = .error .OutOfGass ∨
  (OracleObserveFailure time (oracleObserveCleanAgos rawAgos) tick index liquidity card σ ee ∧
    (RDrev (deployedRuntime v) g s0 ∨ RDinvalid (deployedRuntime v) g s0)) ∨
  (card.toNat ≠ 0 ∧ Nonempty (OracleObserveLoopExit v ee g s0 σ rdata ret R time rawAgos tick index liquidity card
    agoPtr initFree (wordArrayElement initFree rawAgos.length) 0
    (List.replicate rawAgos.length 0) (List.replicate rawAgos.length 0) initMem initAw initFree initCost))

end Benchmarks.UniswapV3.Pool
