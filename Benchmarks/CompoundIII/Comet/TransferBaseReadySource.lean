import Benchmarks.CompoundIII.Comet.TransferBaseFrames
import Benchmarks.CompoundIII.Comet.TransferBaseMathSource
import Benchmarks.CompoundIII.Comet.TransferBaseTotalsSource
import Benchmarks.CompoundIII.Comet.TransferBaseUpdateSource
import Benchmarks.CompoundIII.Comet.TransferBaseTailSource
import Benchmarks.CompoundIII.Comet.InternalBlockComposition

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Benchmarks.CompoundIII.Comet.Immutables

namespace Benchmarks.CompoundIII.Comet

set_option maxRecDepth 2000
attribute [local irreducible] signed104

theorem transferBaseInitial_source (v : CometWithExtendedAssetListImmutables)
    (src dst : AccountAddress) (amount : UInt256) (evm : EVM.State) :
    ExecBlock config (transferBaseAccruedFrame v src dst amount) evm
      (transferBaseReadBlock ++ transferBaseMathBlock)
      (if TransferBaseMathFits evm (withdrawBaseBasic evm src).principal
          (withdrawBaseBasic evm dst).principal amount then
        .ok (transferBaseReadyFrame v src dst amount evm) evm else .reverted) := by
  let frame := transferBaseAccruedFrame v src dst amount
  let read := transferBaseReadFrame frame evm src dst
  have hread := transferBaseRead_source frame evm src dst rfl (by
    simp only [frame, transferBaseAccruedFrame, transferBaseEntry,
      Std.HashMap.get?_eq_getElem?, Std.HashMap.getElem?_insert]; rfl) (by
    simp only [frame, transferBaseAccruedFrame, transferBaseEntry,
      Std.HashMap.get?_eq_getElem?, Std.HashMap.getElem?_insert]; rfl) (by
    simp only [frame, transferBaseAccruedFrame, transferBaseEntry,
      Std.HashMap.get?_eq_getElem?, Std.HashMap.getElem?_insert, Std.HashMap.getElem?_empty]; rfl)
  have hmath := transferBaseMath_source read evm (withdrawBaseBasic evm src).principal
    (withdrawBaseBasic evm dst).principal amount rfl
    (by simp only [read, transferBaseReadFrame, Std.HashMap.get?_eq_getElem?,
          Std.HashMap.getElem?_insert]; rfl)
    (by simp only [read, transferBaseReadFrame, Std.HashMap.get?_eq_getElem?,
          Std.HashMap.getElem?_insert]; rfl)
    (by simp only [read, frame, transferBaseReadFrame, transferBaseAccruedFrame, transferBaseEntry,
          Std.HashMap.get?_eq_getElem?, Std.HashMap.getElem?_insert]; rfl)
  exact execBlock_append hread hmath

theorem transferBaseReady_totals {v src dst amount evm}
    (hf : TransferBaseMathFits evm (withdrawBaseBasic evm src).principal
      (withdrawBaseBasic evm dst).principal amount) :
    ExecBlock config (transferBaseReadyFrame v src dst amount evm) evm transferBaseTotalsBlock
      (transferBaseTotalsResult (transferBaseReadyFrame v src dst amount evm) evm
        (supplyBaseSupplied evm dst amount) (withdrawBaseSupplied evm src amount)
        (withdrawBaseBorrowed evm src amount) (supplyBaseRepaid evm dst amount)) := by
  have hfargs := transferBaseReady_args (v := v) hf
  apply transferBaseTotals_source _ evm _ _ _ _ rfl hfargs.supplied hfargs.withdrawn
  all_goals
    simp only [transferBaseReadyFrame, transferBaseMathFrame, transferBaseAmountsFrame,
      transferBasePrincipalFrame, transferBaseBalanceFrame, transferBaseSrcBalanceFrame,
      transferBaseReadFrame, transferBaseAccruedFrame, transferBaseEntry,
      Std.HashMap.get?_eq_getElem?, Std.HashMap.getElem?_insert, Std.HashMap.getElem?_empty]
    rfl

theorem transferBaseReady_update {v src dst amount evm} (evm' : EVM.State)
    (hf : TransferBaseMathFits evm (withdrawBaseBasic evm src).principal
      (withdrawBaseBasic evm dst).principal amount) :
    ExecBlock config (transferBaseReadyFrame v src dst amount evm) evm' transferBaseUpdateBlock
      (transferBaseUpdateResult (transferBaseReadyFrame v src dst amount evm) v evm' src dst
        (withdrawBaseBasic evm src) (withdrawBaseBasic evm dst)
        (withdrawBaseNext evm src amount) (supplyBaseNext evm dst amount)) := by
  have hfargs := transferBaseReady_args (v := v) hf
  exact transferBaseUpdate_source v _ evm' src dst _ _ _ _ rfl rfl hfargs.src hfargs.dst
    (transferBaseReady_srcBasic v src dst amount evm)
    (transferBaseReady_dstBasic v src dst amount evm)
    (transferBaseReady_srcNext hf) (transferBaseReady_dstNext hf)

theorem transferBaseReady_finish {v src dst amount evm evm' evm'' result}
    (hf : TransferBaseMathFits evm (withdrawBaseBasic evm src).principal
      (withdrawBaseBasic evm dst).principal amount)
    (hu : transferBaseUpdates v evm evm' src dst amount = .ok evm'')
    (tail : TransferBaseTailTrace v src
      (withdrawBaseBalance evm (withdrawBaseBasic evm src).principal amount) evm'' result) :
    internalBlockResult config (transferBaseReadyFrame v src dst amount evm) evm'
      (transferBaseUpdateBlock ++ transferBaseTail) result := by
  let ready := transferBaseReadyFrame v src dst amount evm
  have hfargs := transferBaseReady_args (v := v) hf
  have hcall := transferBaseReady_update (v := v) evm' hf
  change transferBaseUpdateOutcome v evm' src dst _ _ _ _ = .ok evm'' at hu
  simp only [transferBaseUpdateResult, hu] at hcall
  have hb := transferBaseTail_source tail (transferBaseUpdatedFrame ready) dst
    (withdrawBaseSupplied evm src amount) (supplyBaseSupplied evm dst amount)
    ((hfargs.insert "__c9" .unit (by decide)).insert "__c10" .unit (by decide))
    (withdrawSupplyAmount_lt _ _) (supplyAmount_lt _ _) hf.1.2.1.1
  exact hb.prependBlock hcall

end Benchmarks.CompoundIII.Comet
