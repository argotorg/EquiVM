import Benchmarks.UniswapV3.Pool.OracleObserveRun
import Benchmarks.UniswapV3.Pool.OracleObserveStepSource

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.UniswapV3.Pool
set_option maxRecDepth 10000

theorem oracleObserveLoopOfRun (imms : Store) (evm : EVM.State) (time : UInt256)
    (secondsAgos : List UInt256) (tick : Int) (index liquidity card : UInt256)
    (i : Nat) (ticks seconds finalTicks finalSeconds : List Value)
    (hc : card.toNat < 2 ^ 16) (htick : -(2 ^ 23 : Int) ≤ tick ∧ tick < 2 ^ 23)
    (hb : secondsAgos.length < 2 ^ 256)
    (hrun : OracleObserveLoopRun time secondsAgos tick index liquidity card
      evm.accountMap evm.executionEnv i ticks seconds finalTicks finalSeconds) :
    ∀ locals, OracleObserveBindings locals time secondsAgos tick index liquidity card →
      locals.get? "i" = some (.int (Int.ofNat i)) →
      locals.get? "tickCumulatives" = some (.array ticks) →
      locals.get? "secondsPerLiquidityCumulativeX128s" = some (.array seconds) →
      ticks.length = secondsAgos.length → seconds.length = secondsAgos.length →
      ∃ locals', ExecForLoop config {contract := contract, locals := locals, immutables := imms} evm
        oracleObserveCondition oracleObservePost oracleObserveLoopBody
        (.ok {contract := contract, locals := locals', immutables := imms} evm) ∧
        locals'.get? "tickCumulatives" = some (.array finalTicks) ∧
        locals'.get? "secondsPerLiquidityCumulativeX128s" = some (.array finalSeconds) := by
  induction hrun with
  | done hdone =>
      intro locals h hi ht hs _ _
      refine ⟨locals, ExecForLoop.falseDone ?_, ht, hs⟩
      simpa only [decide_eq_false (Nat.not_lt_of_ge hdone)] using
        evalOracleObserveCondition (evm := evm) h hi
  | @step i ticks seconds finalTicks finalSeconds tv sv hib hsingle hrun ih =>
      intro locals h hi ht hs htl hsl
      obtain ⟨l1, l2, hsbody, hpost, hb2, hi2, ht2, hs2⟩ := oracleObserveIteration
        imms evm locals time secondsAgos tick index liquidity card i ticks seconds tv sv
        h hi hib ht hs (by omega) (by omega) (by omega) hc htick hsingle
      obtain ⟨locals', hloop, htf, hsf⟩ := ih l2 hb2 hi2 ht2 hs2
        (by simpa only [List.length_set] using htl) (by simpa only [List.length_set] using hsl)
      refine ⟨locals', ExecForLoop.iterate ?_ hsbody hpost hloop, htf, hsf⟩
      simpa only [decide_eq_true hib] using evalOracleObserveCondition (evm := evm) h hi

theorem oracleObserveLoopOfFailure (imms : Store) (evm : EVM.State) (time : UInt256)
    (secondsAgos : List UInt256) (tick : Int) (index liquidity card : UInt256)
    (i : Nat) (ticks seconds : List Value)
    (hc : card.toNat < 2 ^ 16) (htick : -(2 ^ 23 : Int) ≤ tick ∧ tick < 2 ^ 23)
    (hb : secondsAgos.length < 2 ^ 256)
    (hfail : OracleObserveLoopFailure time secondsAgos tick index liquidity card
      evm.accountMap evm.executionEnv i ticks seconds) :
    ∀ locals, OracleObserveBindings locals time secondsAgos tick index liquidity card →
      locals.get? "i" = some (.int (Int.ofNat i)) →
      locals.get? "tickCumulatives" = some (.array ticks) →
      locals.get? "secondsPerLiquidityCumulativeX128s" = some (.array seconds) →
      ticks.length = secondsAgos.length → seconds.length = secondsAgos.length →
      ExecForLoop config {contract := contract, locals := locals, immutables := imms} evm
        oracleObserveCondition oracleObservePost oracleObserveLoopBody .reverted := by
  induction hfail with
  | @failure i ticks seconds hib hsingle =>
      intro locals h hi _ _ _ _
      apply ExecForLoop.bodyRevert
      · simpa only [decide_eq_true hib] using evalOracleObserveCondition (evm := evm) h hi
      · exact oracleObserveStepReverts imms evm locals time secondsAgos tick index liquidity card
          i h hi hib hc htick hsingle
  | @step i ticks seconds tv sv hib hsingle hfail ih =>
      intro locals h hi ht hs htl hsl
      obtain ⟨l1, l2, hsbody, hpost, hb2, hi2, ht2, hs2⟩ := oracleObserveIteration
        imms evm locals time secondsAgos tick index liquidity card i ticks seconds tv sv
        h hi hib ht hs (by omega) (by omega) (by omega) hc htick hsingle
      have hloop := ih l2 hb2 hi2 ht2 hs2
        (by simpa only [List.length_set] using htl) (by simpa only [List.length_set] using hsl)
      apply ExecForLoop.iterate _ hsbody hpost hloop
      simpa only [decide_eq_true hib] using evalOracleObserveCondition (evm := evm) h hi

end Benchmarks.UniswapV3.Pool
