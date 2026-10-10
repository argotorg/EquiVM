import Benchmarks.CompoundIII.Comet.TransferBaseReadySource

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Benchmarks.CompoundIII.Comet.Immutables

namespace Benchmarks.CompoundIII.Comet

set_option maxRecDepth 2000
attribute [local irreducible] signed104

theorem transferBaseTotals_result {frame evm supplied withdrawn borrowed repaid result}
    (hb : ExecBlock config frame evm transferBaseTotalsBlock
      (transferBaseTotalsResult frame evm supplied withdrawn borrowed repaid))
    (he : transferBaseTotalsOutcome evm supplied withdrawn borrowed repaid = result) :
    ExecBlock config frame evm transferBaseTotalsBlock
      (match result with
       | .ok evm' => .ok frame evm'
       | .reverted => .reverted
       | .staticViolation => .staticViolation) := by
  cases result <;> simpa only [transferBaseTotalsResult, he] using hb

theorem transferBaseUpdate_result {frame v evm src dst srcBasic dstBasic srcNext dstNext result}
    (hb : ExecBlock config frame evm transferBaseUpdateBlock
      (transferBaseUpdateResult frame v evm src dst srcBasic dstBasic srcNext dstNext))
    (he : transferBaseUpdateOutcome v evm src dst srcBasic dstBasic srcNext dstNext = result) :
    ExecBlock config frame evm transferBaseUpdateBlock
      (match result with
       | .ok evm' => .ok (transferBaseUpdatedFrame frame) evm'
       | .reverted => .reverted
       | .staticViolation => .staticViolation) := by
  cases result <;> simpa only [transferBaseUpdateResult, he] using hb

theorem transferBaseAfterAccrue_source {v src dst amount evm result}
    (ht : TransferBaseAfterAccrue v src dst amount evm result) :
    internalBlockResult config (transferBaseAccruedFrame v src dst amount)
      evm transferBaseAfterAccrueBlock result := by
  let frame := transferBaseAccruedFrame v src dst amount
  let ready := transferBaseReadyFrame v src dst amount evm
  have hmath := transferBaseInitial_source v src dst amount evm
  have hprefix (hf : TransferBaseMathFits evm (withdrawBaseBasic evm src).principal
      (withdrawBaseBasic evm dst).principal amount) :
      ExecBlock config frame evm (transferBaseReadBlock ++ transferBaseMathBlock) (.ok ready evm) := by
    simpa only [if_pos hf] using hmath
  change internalBlockResult config frame evm
    ((transferBaseReadBlock ++ transferBaseMathBlock) ++
      (transferBaseTotalsBlock ++ (transferBaseUpdateBlock ++ transferBaseTail))) result
  cases ht with
  | mathFailed hf =>
    rw [if_neg hf] at hmath
    exact execBlock_append_term hmath (by intro _ _ he; cases he)
  | totalsReverted hf he =>
    have htot := transferBaseTotals_result (transferBaseReady_totals (v := v) hf) he
    exact (show internalBlockResult config ready evm
      (transferBaseTotalsBlock ++ (transferBaseUpdateBlock ++ transferBaseTail)) .reverted from
        execBlock_append_term htot (by intro _ _ he; cases he)).prependBlock (hprefix hf)
  | totalsStatic hf he =>
    have htot := transferBaseTotals_result (transferBaseReady_totals (v := v) hf) he
    exact (show internalBlockResult config ready evm
      (transferBaseTotalsBlock ++ (transferBaseUpdateBlock ++ transferBaseTail)) .staticViolation from
        execBlock_append_term htot (by intro _ _ he; cases he)).prependBlock (hprefix hf)
  | @updateReverted evm' hf he hu =>
    have htot := transferBaseTotals_result (transferBaseReady_totals (v := v) hf) he
    have hc := transferBaseUpdate_result (transferBaseReady_update (v := v) evm' hf) hu
    exact (show internalBlockResult config ready evm'
      (transferBaseUpdateBlock ++ transferBaseTail) .reverted from
        execBlock_append_term hc (by intro _ _ he; cases he)).prependBlock htot
      |>.prependBlock (hprefix hf)
  | @updateStatic evm' hf he hu =>
    have htot := transferBaseTotals_result (transferBaseReady_totals (v := v) hf) he
    have hc := transferBaseUpdate_result (transferBaseReady_update (v := v) evm' hf) hu
    exact (show internalBlockResult config ready evm'
      (transferBaseUpdateBlock ++ transferBaseTail) .staticViolation from
        execBlock_append_term hc (by intro _ _ he; cases he)).prependBlock htot
      |>.prependBlock (hprefix hf)
  | done hf he hu tail =>
    have htot := transferBaseTotals_result (transferBaseReady_totals (v := v) hf) he
    exact ((transferBaseReady_finish hf hu tail).prependBlock htot).prependBlock (hprefix hf)

end Benchmarks.CompoundIII.Comet
