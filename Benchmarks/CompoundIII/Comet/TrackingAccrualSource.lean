import Benchmarks.CompoundIII.Comet.TrackingAccrualModel

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Benchmarks.CompoundIII.Comet.Immutables

namespace Benchmarks.CompoundIII.Comet

set_option maxRecDepth 2000

theorem trackingAccrual_source (v : CometWithExtendedAssetListImmutables) (borrow : Bool)
    (frame : Frame) (evm : EVM.State) (elapsed : UInt256)
    (hc : frame.contract = contract) (hi : frame.immutables = immStore v)
    (ht : evalExpr? config frame evm (.var "timeElapsed") = .ok (.int elapsed.toNat))
    (hp : frame.locals.get? (totalsPrincipalName borrow) = none)
    (hx : frame.locals.get? (trackingIndexName borrow) = none) :
    let w0 := Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨0⟩
    let w1 := Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨1⟩
    ExecBlock config frame evm (trackingAccrualBlock borrow)
      (if TrackingAccrualValid v borrow w0 w1 elapsed then
        .ok (trackingAccrualFrame frame borrow
          (trackingIncrement v borrow (totalsPrincipalWord w1 borrow) elapsed))
          (trackingAccrualState evm v borrow elapsed) else .reverted) := by
  dsimp only
  let w0 := Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨0⟩
  let w1 := Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨1⟩
  let total := totalsPrincipalWord w1 borrow
  let increment := trackingIncrement v borrow total elapsed
  let product := UInt256.mul (trackingSpeed v borrow) elapsed
  let f1 : Frame :=
    { frame with locals := frame.locals.insert (trackingDivName borrow) (.int increment.toNat) }
  let f2 := trackingAccrualFrame frame borrow increment
  change ExecBlock config frame evm (trackingAccrualBlock borrow)
    (if TrackingAccrualValid v borrow w0 w1 elapsed then
      .ok f2 (trackingAccrualState evm v borrow elapsed) else .reverted)
  have hs := evalTrackingSpeed v borrow frame evm hi
  have htotal : evalExpr? config frame evm (.storage ⟨totalsPrincipalName borrow, []⟩) =
      .ok (.int total.toNat) := by
    simpa only [← hc] using evalTotalsPrincipal evm frame.locals frame.immutables borrow hp
  by_cases hm : (trackingSpeed v borrow).toNat * elapsed.toNat < UInt256.size
  · have hmexpr := checkedMulSourceOk hs ht hm
    have hdiv := divBaseWei_call v frame evm product total _ _ (trackingDivName borrow)
      hc hi hmexpr htotal
    by_cases hd : DivBaseWeiValid v product total
    · rw [if_pos hd] at hdiv
      apply ExecBlock.consNormal hdiv
      have hinc : evalExpr? config f1 evm (.var (trackingDivName borrow)) =
          .ok (.int increment.toNat) := by
        simp only [evalExpr?, f1, Std.HashMap.get?_eq_getElem?,
          Std.HashMap.getElem?_insert, beq_self_eq_true, if_true, EvalResult.ofOption]
      by_cases h64 : increment.toNat < 2^64
      · apply ExecBlock.consNormal (safe64_call_ok f1 evm increment _ (trackingSafeName borrow)
          hc hinc h64)
        have hlocal : f2.locals.get? (trackingIndexName borrow) = none := by
          cases borrow <;>
            simpa only [f2, trackingAccrualFrame, trackingDivName, trackingSafeName,
              trackingIndexName, Bool.false_eq_true, if_false, if_true,
              Std.HashMap.get?_eq_getElem?, Std.HashMap.getElem?_insert] using hx
        have hidx : evalExpr? config f2 evm (.storage ⟨trackingIndexName borrow, []⟩) =
            .ok (.int (trackingIndexWord w0 borrow).toNat) := by
          simpa only [f2, trackingAccrualFrame, hc] using
            evalTrackingIndex evm f2.locals f2.immutables borrow hlocal
        have hsafe : evalExpr? config f2 evm (.var (trackingSafeName borrow)) =
            .ok (.int increment.toNat) := by
          simp only [evalExpr?, f2, trackingAccrualFrame, Std.HashMap.get?_eq_getElem?,
            Std.HashMap.getElem?_insert, beq_self_eq_true, if_true, EvalResult.ofOption]
        by_cases hadd : (trackingIndexWord w0 borrow).toNat + increment.toNat < 2^64
        · rw [if_pos (show TrackingAccrualValid v borrow w0 w1 elapsed from
            ⟨⟨hm, hd, h64⟩, hadd⟩)]
          have ha : assignStorageRef? config f2 evm .storage ⟨trackingIndexName borrow, []⟩
              (.int (trackingIndexWord w0 borrow + increment).toNat) =
              .ok (f2, storeTrackingIndex evm borrow
                (trackingIndexWord w0 borrow + increment)) := by
            simpa only [f2, trackingAccrualFrame, hc] using
              assignTrackingIndex evm f2.locals f2.immutables borrow
                (trackingIndexWord w0 borrow + increment) hlocal
          exact ExecBlock.consNormal (ExecStmt.assign
            (checkedNarrowAddSourceOk ⟨64, by decide⟩ (by decide) hidx hsafe hadd) ha) ExecBlock.nil
        · rw [if_neg (show ¬ TrackingAccrualValid v borrow w0 w1 elapsed from
            fun h ↦ hadd h.2)]
          apply ExecBlock.consRevert (ExecStmt.assignExprRevert ?_)
          exact uintRangeSourceOverflow ⟨64, by decide⟩ (naturalAddSource hidx hsafe)
            (le_of_not_gt hadd)
      · rw [if_neg (show ¬ TrackingAccrualValid v borrow w0 w1 elapsed from
          fun h ↦ h64 h.1.2.2)]
        exact ExecBlock.consRevert
          (safe64_call_revert f1 evm increment _ (trackingSafeName borrow) hc hinc h64)
    · rw [if_neg hd] at hdiv
      rw [if_neg (show ¬ TrackingAccrualValid v borrow w0 w1 elapsed from
        fun h ↦ hd h.1.2.1)]
      exact ExecBlock.consRevert hdiv
  · rw [if_neg (show ¬ TrackingAccrualValid v borrow w0 w1 elapsed from fun h ↦ hm h.1.1)]
    have hmul := checkedMulSourceOverflow hs ht (le_of_not_gt hm)
    apply ExecBlock.consRevert (ExecStmt.internalCallArgsRevert ?_)
    simp only [evalExprs?, hmul, bind, EvalResult.bind]

theorem trackingBranch_source (v : CometWithExtendedAssetListImmutables) (borrow : Bool)
    (frame : Frame) (evm : EVM.State) (elapsed : UInt256)
    (hc : frame.contract = contract) (hi : frame.immutables = immStore v)
    (ht : evalExpr? config frame evm (.var "timeElapsed") = .ok (.int elapsed.toNat))
    (hp : frame.locals.get? (totalsPrincipalName borrow) = none)
    (hx : frame.locals.get? (trackingIndexName borrow) = none) :
    ExecStmt config frame evm (trackingBranch borrow)
      (if TrackingBranchValid v borrow evm elapsed then
        .ok (trackingBranchFrame frame evm v borrow elapsed)
          (trackingBranchState evm v borrow elapsed) else .reverted) := by
  have htotal : evalExpr? config frame evm (.storage ⟨totalsPrincipalName borrow, []⟩) =
      .ok (.int (totalsPrincipalWord
        (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨1⟩) borrow).toNat) := by
    simpa only [← hc] using evalTotalsPrincipal evm frame.locals frame.immutables borrow hp
  have hmin : evalExpr? config frame evm (.immutable "baseMinForRewards") =
      .ok (.int v.baseMinForRewards.toNat) := by
    simp only [evalExpr?, hi, immStore_get_baseMinForRewards, EvalResult.ofOption]
    rfl
  have hcond : evalExpr? config frame evm
      (.binary .ge (.storage ⟨totalsPrincipalName borrow, []⟩) (.immutable "baseMinForRewards")) =
      .ok (.bool (decide (TrackingEnabled v borrow evm))) := by
    exact naturalGeSource htotal hmin
  have hb := trackingAccrual_source v borrow frame evm elapsed hc hi ht hp hx
  dsimp only at hb
  by_cases hen : TrackingEnabled v borrow evm
  · simp only [TrackingBranchValid, trackingBranchFrame, trackingBranchState, if_pos hen]
    rw [decide_eq_true hen] at hcond
    exact ExecStmt.iteTrue hcond hb
  · simp only [TrackingBranchValid, trackingBranchFrame, trackingBranchState, if_neg hen, if_true]
    rw [decide_eq_false hen] at hcond
    exact ExecStmt.iteFalse hcond ExecBlock.nil

end Benchmarks.CompoundIII.Comet
