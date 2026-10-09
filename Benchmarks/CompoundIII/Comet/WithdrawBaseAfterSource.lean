import Benchmarks.CompoundIII.Comet.WithdrawBaseReadySource
import Benchmarks.CompoundIII.Comet.WithdrawBaseTotalsResult

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Benchmarks.CompoundIII.Comet.Immutables

namespace Benchmarks.CompoundIII.Comet

set_option maxRecDepth 2000
attribute [local irreducible] signed104

theorem withdrawBaseAfterAccrue_source {v src recipient amount evm result}
    (ht : WithdrawBaseAfterAccrue v src recipient amount evm result) :
    internalBlockResult config (withdrawBaseAccruedFrame v src recipient amount)
      evm withdrawBaseAfterAccrueBlock result := by
  let frame := withdrawBaseAccruedFrame v src recipient amount
  let ready := withdrawBaseReadyFrame v src recipient amount evm
  have hmath := withdrawBaseInitial_source v src recipient amount evm
  have htot := withdrawBaseReady_totals v src recipient amount evm
  have hprefix (hf : WithdrawBaseMathFits evm (withdrawBaseBasic evm src).principal amount) :
      ExecBlock config frame evm (withdrawBaseReadBlock ++ withdrawBaseMathBlock) (.ok ready evm) := by
    simpa only [if_pos hf] using hmath
  change internalBlockResult config frame evm
    ((withdrawBaseReadBlock ++ withdrawBaseMathBlock) ++
      (withdrawBaseTotalsBlock ++ (withdrawBaseUpdateStmt :: withdrawBaseTail))) result
  cases ht with
  | mathFailed hf =>
    rw [if_neg hf] at hmath
    exact execBlock_append_term hmath (by intro _ _ he; cases he)
  | totalsReverted hf he =>
    have htot := withdrawBaseTotals_result htot he
    exact (show internalBlockResult config ready evm
      (withdrawBaseTotalsBlock ++ (withdrawBaseUpdateStmt :: withdrawBaseTail)) .reverted from
        execBlock_append_term htot (by intro _ _ he; cases he)).prependBlock (hprefix hf)
  | totalsStatic hf he =>
    have htot := withdrawBaseTotals_result htot he
    exact (show internalBlockResult config ready evm
      (withdrawBaseTotalsBlock ++ (withdrawBaseUpdateStmt :: withdrawBaseTail)) .staticViolation from
        execBlock_append_term htot (by intro _ _ he; cases he)).prependBlock (hprefix hf)
  | @updateReverted evm' hf he hu =>
    have htot := withdrawBaseTotals_result htot he
    have hc := withdrawBaseReady_update (v := v) (recipient := recipient) evm' hf
    have hc := internalStmtResult.cast hc hu
    exact (show internalBlockResult config ready _
      (withdrawBaseUpdateStmt :: withdrawBaseTail) .reverted from
        ExecBlock.consRevert hc).prependBlock htot |>.prependBlock (hprefix hf)
  | @updateStatic evm' hf he hu =>
    have htot := withdrawBaseTotals_result htot he
    have hc := withdrawBaseReady_update (v := v) (recipient := recipient) evm' hf
    have hc := internalStmtResult.cast hc hu
    exact (show internalBlockResult config ready _
      (withdrawBaseUpdateStmt :: withdrawBaseTail) .staticViolation from
        ExecBlock.consStatic hc).prependBlock htot |>.prependBlock (hprefix hf)
  | done hf he hu tail =>
    have htot := withdrawBaseTotals_result htot he
    exact ((withdrawBaseReady_finish hf hu tail).prependBlock htot).prependBlock (hprefix hf)

end Benchmarks.CompoundIII.Comet
