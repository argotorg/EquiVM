import Benchmarks.CompoundIII.Comet.SupplyBaseReadySource
import Benchmarks.CompoundIII.Comet.SupplyBaseTotalsResult

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Benchmarks.CompoundIII.Comet.Immutables

namespace Benchmarks.CompoundIII.Comet

set_option maxRecDepth 2000
attribute [local irreducible] signed104

theorem supplyBaseAfterAccrue_source {v sender dst amount evm result} (requested : UInt256)
    (ht : SupplyBaseAfterAccrue v sender dst amount evm result) :
    internalBlockResult config (supplyBaseAccruedFrame v sender dst requested amount)
      evm supplyBaseAfterAccrueBlock result := by
  let frame := supplyBaseAccruedFrame v sender dst requested amount
  let ready := supplyBaseReadyFrame v sender dst requested amount evm
  have hmath := supplyBaseInitial_source v sender dst requested amount evm
  have htot := supplyBaseReady_totals v sender dst requested amount evm
  have hprefix (hf : SupplyBaseMathFits evm (withdrawBaseBasic evm dst).principal amount) :
      ExecBlock config frame evm (supplyBaseReadBlock ++ supplyBaseMathBlock) (.ok ready evm) := by
    simpa only [if_pos hf] using hmath
  change internalBlockResult config frame evm
    ((supplyBaseReadBlock ++ supplyBaseMathBlock) ++
      (supplyBaseTotalsBlock ++ (supplyBaseUpdateStmt :: supplyBaseEvents))) result
  cases ht with
  | mathFailed hf =>
    rw [if_neg hf] at hmath
    exact execBlock_append_term hmath (by intro _ _ he; cases he)
  | totalsReverted hf he =>
    have htot := supplyBaseTotals_result htot he
    exact (show internalBlockResult config ready evm
      (supplyBaseTotalsBlock ++ (supplyBaseUpdateStmt :: supplyBaseEvents)) .reverted from
        execBlock_append_term htot (by intro _ _ he; cases he)).prependBlock (hprefix hf)
  | totalsStatic hf he =>
    have htot := supplyBaseTotals_result htot he
    exact (show internalBlockResult config ready evm
      (supplyBaseTotalsBlock ++ (supplyBaseUpdateStmt :: supplyBaseEvents)) .staticViolation from
        execBlock_append_term htot (by intro _ _ he; cases he)).prependBlock (hprefix hf)
  | @updateReverted evm' hf he hu =>
    have htot := supplyBaseTotals_result htot he
    have hc := supplyBaseReady_update (v := v) (sender := sender) (requested := requested) evm' hf
    have hc := internalStmtResult.cast hc hu
    exact (show internalBlockResult config ready _
      (supplyBaseUpdateStmt :: supplyBaseEvents) .reverted from
        ExecBlock.consRevert hc).prependBlock htot |>.prependBlock (hprefix hf)
  | @updateStatic evm' hf he hu =>
    have htot := supplyBaseTotals_result htot he
    have hc := supplyBaseReady_update (v := v) (sender := sender) (requested := requested) evm' hf
    have hc := internalStmtResult.cast hc hu
    exact (show internalBlockResult config ready _
      (supplyBaseUpdateStmt :: supplyBaseEvents) .staticViolation from
        ExecBlock.consStatic hc).prependBlock htot |>.prependBlock (hprefix hf)
  | done hf he hu =>
    have htot := supplyBaseTotals_result htot he
    exact ((supplyBaseReady_finish hf hu).prependBlock htot).prependBlock (hprefix hf)

end Benchmarks.CompoundIII.Comet
