import Benchmarks.CompoundIII.Comet.SupplyBaseFrames
import Benchmarks.CompoundIII.Comet.SupplyBaseMathSource
import Benchmarks.CompoundIII.Comet.SupplyBaseTotalsSource
import Benchmarks.CompoundIII.Comet.SupplyBaseEventsSource
import Benchmarks.CompoundIII.Comet.UpdateBaseSource
import Benchmarks.CompoundIII.Comet.InternalBlockComposition

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Benchmarks.CompoundIII.Comet.Immutables

namespace Benchmarks.CompoundIII.Comet

set_option maxRecDepth 2000
attribute [local irreducible] signed104

theorem supplyBaseInitial_source (v : CometWithExtendedAssetListImmutables)
    (sender dst : AccountAddress) (requested amount : UInt256) (evm : EVM.State) :
    ExecBlock config (supplyBaseAccruedFrame v sender dst requested amount) evm
      (supplyBaseReadBlock ++ supplyBaseMathBlock)
      (if SupplyBaseMathFits evm (withdrawBaseBasic evm dst).principal amount then
        .ok (supplyBaseReadyFrame v sender dst requested amount evm) evm else .reverted) := by
  let frame := supplyBaseAccruedFrame v sender dst requested amount
  let read := supplyBaseReadFrame frame evm dst
  have hread := supplyBaseRead_source frame evm dst rfl (by
    simp only [frame, supplyBaseAccruedFrame, supplyBaseReceivedFrame, supplyBaseEntry,
      Std.HashMap.get?_eq_getElem?, Std.HashMap.getElem?_insert]; rfl) (by
    simp only [frame, supplyBaseAccruedFrame, supplyBaseReceivedFrame, supplyBaseEntry,
      Std.HashMap.get?_eq_getElem?, Std.HashMap.getElem?_insert, Std.HashMap.getElem?_empty]; rfl)
  have hmath := supplyBaseMath_source read evm (withdrawBaseBasic evm dst).principal amount rfl
    (by simp only [read, supplyBaseReadFrame, Std.HashMap.get?_eq_getElem?,
          Std.HashMap.getElem?_insert]; rfl)
    (by simp only [read, frame, supplyBaseReadFrame, supplyBaseAccruedFrame, supplyBaseReceivedFrame, supplyBaseEntry,
          Std.HashMap.get?_eq_getElem?, Std.HashMap.getElem?_insert]; rfl)
  exact execBlock_append hread hmath

theorem supplyBaseReady_totals (v : CometWithExtendedAssetListImmutables)
    (sender dst : AccountAddress) (requested amount : UInt256) (evm : EVM.State) :
    ExecBlock config (supplyBaseReadyFrame v sender dst requested amount evm) evm supplyBaseTotalsBlock
      (supplyBaseTotalsResult (supplyBaseReadyFrame v sender dst requested amount evm) evm
        (supplyBaseSupplied evm dst amount) (supplyBaseRepaid evm dst amount)) := by
  have hfargs := supplyBaseReady_args v sender dst requested amount evm
  apply supplyBaseTotals_source _ evm _ _ rfl hfargs.supplied
  · simp only [supplyBaseReadyFrame, supplyBaseMathFrame,
      Std.HashMap.get?_eq_getElem?, Std.HashMap.getElem?_insert]; rfl
  · simp only [supplyBaseReadyFrame, supplyBaseMathFrame, supplyBaseReadFrame,
      supplyBaseAccruedFrame, supplyBaseReceivedFrame, supplyBaseEntry, Std.HashMap.get?_eq_getElem?,
      Std.HashMap.getElem?_insert, Std.HashMap.getElem?_empty]; rfl
  · simp only [supplyBaseReadyFrame, supplyBaseMathFrame, supplyBaseReadFrame,
      supplyBaseAccruedFrame, supplyBaseReceivedFrame, supplyBaseEntry, Std.HashMap.get?_eq_getElem?,
      Std.HashMap.getElem?_insert, Std.HashMap.getElem?_empty]; rfl

theorem supplyBaseReady_update {v sender dst requested amount evm}
    (evm' : EVM.State)
    (hf : SupplyBaseMathFits evm (withdrawBaseBasic evm dst).principal amount) :
    ExecStmt config (supplyBaseReadyFrame v sender dst requested amount evm) evm' supplyBaseUpdateStmt
      (internalStmtResult (supplyBaseReadyFrame v sender dst requested amount evm) "__c6"
        (updateBaseOutcome v evm' dst (withdrawBaseBasic evm dst) (supplyBaseNext evm dst amount))) := by
  have hfargs := supplyBaseReady_args v sender dst requested amount evm
  exact updateBase_call v _ evm' dst (withdrawBaseBasic evm dst) (supplyBaseNext evm dst amount)
    (.var "dst") (.var "dstUser") (.var "dstPrincipalNew") "__c6" rfl rfl
    (by simp only [evalExpr?, hfargs.dst, EvalResult.ofOption])
    (by simp only [evalExpr?, supplyBaseReady_basic, EvalResult.ofOption])
    (by simp only [evalExpr?, supplyBaseReady_principal hf, EvalResult.ofOption])

theorem supplyBaseReady_finish {v sender dst requested amount evm evm' evm''}
    (hf : SupplyBaseMathFits evm (withdrawBaseBasic evm dst).principal amount)
    (hu : updateBaseOutcome v evm' dst (withdrawBaseBasic evm dst)
      (supplyBaseNext evm dst amount) = .ok evm'') :
    internalBlockResult config (supplyBaseReadyFrame v sender dst requested amount evm) evm'
      (supplyBaseUpdateStmt :: supplyBaseEvents) (.ok evm'') := by
  let ready := supplyBaseReadyFrame v sender dst requested amount evm
  let final := { ready with locals := ready.locals.insert "__c6" .unit }
  have hcall := supplyBaseReady_update (v := v) (sender := sender) (requested := requested) evm' hf
  have hcall := internalStmtResult.cast hcall hu
  have hargs := (supplyBaseReady_args v sender dst requested amount evm).insert
    "__c6" .unit (by decide)
  obtain ⟨frame', he⟩ := supplyBaseEvents_source final evm'' hargs (supplyAmount_lt _ _)
  exact (show internalBlockResult config final evm'' supplyBaseEvents (.ok evm'') from
    ⟨frame', he⟩).prepend hcall

end Benchmarks.CompoundIII.Comet
