import Benchmarks.CompoundIII.Comet.WithdrawBaseFrames
import Benchmarks.CompoundIII.Comet.WithdrawBaseMathSource
import Benchmarks.CompoundIII.Comet.WithdrawBaseTotalsSource
import Benchmarks.CompoundIII.Comet.WithdrawBaseTailSource
import Benchmarks.CompoundIII.Comet.UpdateBaseSource
import Benchmarks.CompoundIII.Comet.InternalBlockComposition

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Benchmarks.CompoundIII.Comet.Immutables

namespace Benchmarks.CompoundIII.Comet

set_option maxRecDepth 2000
attribute [local irreducible] signed104

theorem withdrawBaseInitial_source (v : CometWithExtendedAssetListImmutables)
    (src recipient : AccountAddress) (amount : UInt256) (evm : EVM.State) :
    ExecBlock config (withdrawBaseAccruedFrame v src recipient amount) evm
      (withdrawBaseReadBlock ++ withdrawBaseMathBlock)
      (if WithdrawBaseMathFits evm (withdrawBaseBasic evm src).principal amount then
        .ok (withdrawBaseReadyFrame v src recipient amount evm) evm else .reverted) := by
  let frame := withdrawBaseAccruedFrame v src recipient amount
  let read := withdrawBaseReadFrame frame evm src
  have hread := withdrawBaseRead_source frame evm src rfl (by
    simp only [frame, withdrawBaseAccruedFrame, withdrawBaseEntry,
      Std.HashMap.get?_eq_getElem?, Std.HashMap.getElem?_insert]; rfl) (by
    simp only [frame, withdrawBaseAccruedFrame, withdrawBaseEntry,
      Std.HashMap.get?_eq_getElem?, Std.HashMap.getElem?_insert, Std.HashMap.getElem?_empty]; rfl)
  have hmath := withdrawBaseMath_source read evm (withdrawBaseBasic evm src).principal amount rfl
    (by simp only [read, withdrawBaseReadFrame, Std.HashMap.get?_eq_getElem?,
          Std.HashMap.getElem?_insert]; rfl)
    (by simp only [read, frame, withdrawBaseReadFrame, withdrawBaseAccruedFrame, withdrawBaseEntry,
          Std.HashMap.get?_eq_getElem?, Std.HashMap.getElem?_insert]; rfl)
  exact execBlock_append hread hmath

theorem withdrawBaseReady_totals (v : CometWithExtendedAssetListImmutables)
    (src recipient : AccountAddress) (amount : UInt256) (evm : EVM.State) :
    ExecBlock config (withdrawBaseReadyFrame v src recipient amount evm) evm withdrawBaseTotalsBlock
      (withdrawBaseTotalsResult (withdrawBaseReadyFrame v src recipient amount evm) evm
        (withdrawBaseSupplied evm src amount) (withdrawBaseBorrowed evm src amount)) := by
  have hfargs := withdrawBaseReady_args v src recipient amount evm
  apply withdrawBaseTotals_source _ evm _ _ rfl hfargs.supplied
  · simp only [withdrawBaseReadyFrame, withdrawBaseMathFrame,
      Std.HashMap.get?_eq_getElem?, Std.HashMap.getElem?_insert]; rfl
  · simp only [withdrawBaseReadyFrame, withdrawBaseMathFrame, withdrawBaseReadFrame,
      withdrawBaseAccruedFrame, withdrawBaseEntry, Std.HashMap.get?_eq_getElem?,
      Std.HashMap.getElem?_insert, Std.HashMap.getElem?_empty]; rfl
  · simp only [withdrawBaseReadyFrame, withdrawBaseMathFrame, withdrawBaseReadFrame,
      withdrawBaseAccruedFrame, withdrawBaseEntry, Std.HashMap.get?_eq_getElem?,
      Std.HashMap.getElem?_insert, Std.HashMap.getElem?_empty]; rfl

theorem withdrawBaseReady_update {v src recipient amount evm}
    (evm' : EVM.State)
    (hf : WithdrawBaseMathFits evm (withdrawBaseBasic evm src).principal amount) :
    ExecStmt config (withdrawBaseReadyFrame v src recipient amount evm) evm' withdrawBaseUpdateStmt
      (internalStmtResult (withdrawBaseReadyFrame v src recipient amount evm) "__c5"
        (updateBaseOutcome v evm' src (withdrawBaseBasic evm src) (withdrawBaseNext evm src amount))) := by
  have hfargs := withdrawBaseReady_args v src recipient amount evm
  exact updateBase_call v _ evm' src (withdrawBaseBasic evm src) (withdrawBaseNext evm src amount)
    (.var "src") (.var "srcUser") (.var "srcPrincipalNew") "__c5" rfl rfl
    (by simp only [evalExpr?, hfargs.src, EvalResult.ofOption])
    (by simp only [evalExpr?, withdrawBaseReady_basic, EvalResult.ofOption])
    (by simp only [evalExpr?, withdrawBaseReady_principal hf, EvalResult.ofOption])

theorem withdrawBaseReady_finish {v src recipient amount evm evm' evm'' result}
    (hf : WithdrawBaseMathFits evm (withdrawBaseBasic evm src).principal amount)
    (hu : updateBaseOutcome v evm' src (withdrawBaseBasic evm src)
      (withdrawBaseNext evm src amount) = .ok evm'')
    (tail : WithdrawBaseTailTrace v src recipient amount
      (withdrawBaseBalance evm (withdrawBaseBasic evm src).principal amount) evm'' result) :
    internalBlockResult config (withdrawBaseReadyFrame v src recipient amount evm) evm'
      (withdrawBaseUpdateStmt :: withdrawBaseTail) result := by
  let ready := withdrawBaseReadyFrame v src recipient amount evm
  have hfargs := withdrawBaseReady_args v src recipient amount evm
  have hcall := withdrawBaseReady_update (v := v) (recipient := recipient) evm' hf
  simp only [hu, internalStmtResult] at hcall
  have hb := withdrawBaseTail_source tail
    { ready with locals := ready.locals.insert "__c5" .unit } (withdrawBaseSupplied evm src amount)
    (hfargs.insert "__c5" .unit (by decide)) (withdrawSupplyAmount_lt _ _)
    (by simpa only [Std.HashMap.get?_eq_getElem?, Std.HashMap.getElem?_insert] using
      withdrawBaseReady_balance (v := v) (recipient := recipient) hf) hf.2.1.1
  exact hb.prepend hcall

end Benchmarks.CompoundIII.Comet
