import Benchmarks.CompoundIII.Comet.AbsorbRepayModel
import Benchmarks.CompoundIII.Comet.InternalFrameResult

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.CompoundIII.Comet

set_option maxRecDepth 10000
attribute [local irreducible] signed104 supplyBaseTotalsOutcome absorbRepayOutcome

theorem supplyBaseTotalsResult_asFrameResult (frame : Frame) (evm : EVM.State)
    (supplied repaid : UInt256) :
    supplyBaseTotalsResult frame evm supplied repaid =
      internalFrameResult frame (supplyBaseTotalsOutcome evm supplied repaid) := rfl

theorem absorbRepayResult_eq (frame : Frame) (evm : EVM.State) (old next : UInt256) :
    absorbRepayResult frame evm old next =
      internalFrameResult (absorbRepayFrame frame old next) (absorbRepayOutcome evm old next) := by
  unfold absorbRepayResult absorbRepayOutcome
  split_ifs
  · exact supplyBaseTotalsResult_asFrameResult _ _ _ _
  · rfl

theorem absorbRepay_result {frame evm old next result}
    (hb : ExecBlock config frame evm absorbRepayBlock (absorbRepayResult frame evm old next))
    (he : absorbRepayOutcome evm old next = result) :
    ExecBlock config frame evm absorbRepayBlock
      (internalFrameResult (absorbRepayFrame frame old next) result) := by
  rw [absorbRepayResult_eq, he] at hb
  exact hb

end Benchmarks.CompoundIII.Comet
