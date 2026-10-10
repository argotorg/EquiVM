import Benchmarks.CompoundIII.Comet.AccrueInternalModel
import Benchmarks.CompoundIII.Comet.TrackingAccrualSource
import Benchmarks.CompoundIII.Comet.TrackingFrame

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Benchmarks.CompoundIII.Comet.Immutables

namespace Benchmarks.CompoundIII.Comet

set_option maxRecDepth 2000

def accrueRewardsFrame (frame : Frame) (evm : EVM.State)
    (v : CometWithExtendedAssetListImmutables) (elapsed : UInt256) : Frame :=
  trackingBranchFrame (trackingBranchFrame frame evm v false elapsed)
    (trackingBranchState evm v false elapsed) v true elapsed

theorem accrueRewards_source (v : CometWithExtendedAssetListImmutables)
    (frame : Frame) (evm : EVM.State) (elapsed time : UInt256)
    (hc : frame.contract = contract) (hi : frame.immutables = immStore v)
    (ht : evalExpr? config frame evm (.var "timeElapsed") = .ok (.int elapsed.toNat))
    (hn : evalExpr? config frame evm (.var "now_") = .ok (.int time.toNat))
    (hp : ∀ b, frame.locals.get? (totalsPrincipalName b) = none)
    (hx : ∀ b, frame.locals.get? (trackingIndexName b) = none)
    (hl : frame.locals.get? "lastAccrualTime" = none) :
    ExecBlock config frame evm accrueRewardsBlock
      (if AccrueRewardsValid v evm elapsed then
        .ok (accrueRewardsFrame frame evm v elapsed) (accrueRewardsState evm v elapsed time)
      else .reverted) := by
  let f1 := trackingBranchFrame frame evm v false elapsed
  let evm1 := trackingBranchState evm v false elapsed
  let f2 := accrueRewardsFrame frame evm v elapsed
  let evm2 := trackingBranchState evm1 v true elapsed
  have hsupply := trackingBranch_source v false frame evm elapsed hc hi ht (hp false) (hx false)
  by_cases hsup : TrackingBranchValid v false evm elapsed
  · rw [if_pos hsup] at hsupply
    apply ExecBlock.consNormal hsupply
    have hfc : f1.contract = contract := (trackingBranchFrame_contract _ _ _ _ _).trans hc
    have hfi : f1.immutables = immStore v := (trackingBranchFrame_immutables _ _ _ _ _).trans hi
    have ht1 : evalExpr? config f1 evm1 (.var "timeElapsed") = .ok (.int elapsed.toNat) := by
      rw [trackingBranchFrame_eval _ _ _ _ _ _ _ (by decide) (by decide)]
      exact ht
    have hp1 : f1.locals.get? (totalsPrincipalName true) = none := by
      rw [trackingBranchFrame_get _ _ _ _ _ _ (by decide) (by decide)]
      exact hp true
    have hx1 : f1.locals.get? (trackingIndexName true) = none := by
      rw [trackingBranchFrame_get _ _ _ _ _ _ (by decide) (by decide)]
      exact hx true
    have hborrow := trackingBranch_source v true f1 evm1 elapsed hfc hfi ht1 hp1 hx1
    by_cases hbor : TrackingBranchValid v true evm1 elapsed
    · rw [if_pos hbor] at hborrow
      apply ExecBlock.consNormal hborrow
      rw [if_pos (show AccrueRewardsValid v evm elapsed from ⟨hsup, hbor⟩)]
      have hn2 : evalExpr? config f2 evm2 (.var "now_") = .ok (.int time.toNat) := by
        unfold f2 accrueRewardsFrame
        rw [trackingBranchFrame_eval _ _ _ _ _ _ _ (by decide) (by decide),
          trackingBranchFrame_eval _ _ _ _ _ _ _ (by decide) (by decide)]
        exact hn
      have hl2 : f2.locals.get? "lastAccrualTime" = none := by
        unfold f2 accrueRewardsFrame
        rw [trackingBranchFrame_get _ _ _ _ _ _ (by decide) (by decide),
          trackingBranchFrame_get _ _ _ _ _ _ (by decide) (by decide)]
        exact hl
      have hfc2 : f2.contract = contract :=
        (trackingBranchFrame_contract _ _ _ _ _).trans hfc
      have ha : assignStorageRef? config f2 evm2 .storage ⟨"lastAccrualTime", []⟩
          (.int time.toNat) = .ok (f2, storeLastAccrual evm2 time) := by
        simpa only [← hfc2] using assignLastAccrual evm2 f2.locals f2.immutables time hl2
      exact ExecBlock.consNormal (ExecStmt.assign hn2 ha) ExecBlock.nil
    · rw [if_neg hbor] at hborrow
      rw [if_neg (show ¬ AccrueRewardsValid v evm elapsed from fun h ↦ hbor h.2)]
      exact ExecBlock.consRevert hborrow
  · rw [if_neg hsup] at hsupply
    rw [if_neg (show ¬ AccrueRewardsValid v evm elapsed from fun h ↦ hsup h.1)]
    exact ExecBlock.consRevert hsupply

end Benchmarks.CompoundIII.Comet
