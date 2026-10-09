import Benchmarks.CompoundIII.Comet.AccountMagnitude

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Benchmarks.CompoundIII.Comet.Immutables

namespace Benchmarks.CompoundIII.Comet

set_option maxRecDepth 2000

theorem accountReward_source (v : CometWithExtendedAssetListImmutables) (borrow : Bool)
    (frame : Frame) (evm : EVM.State) (basic : UserBasicData) (principal : UInt256)
    (hc : frame.contract = contract) (hi : frame.immutables = immStore v)
    (hb : frame.locals.get? "basic" = some (userBasicValue basic))
    (hp : frame.locals.get? "principal" = some (.int (signed104 principal)))
    (hx : frame.locals.get? (trackingIndexName borrow) = none)
    (hsign : if borrow then signed104 principal < 0 else 0 ≤ signed104 principal) :
    ExecBlock config frame evm (accountRewardBlock borrow)
      (if AccountRewardValid v evm basic principal borrow then
        .ok (accountRewardFrame frame v evm basic principal borrow) evm else .reverted) := by
  let delta := accountRewardDelta evm basic borrow
  let reward := accountReward v evm basic principal borrow
  let f1 : Frame := { frame with locals := frame.locals.insert "indexDelta" (.int delta.toNat) }
  let f2 : Frame :=
    { f1 with locals := f1.locals.insert (accountRewardName borrow) (.int reward.toNat) }
  have heb : evalExpr? config frame evm (.var "basic") = .ok (userBasicValue basic) := by
    simp only [evalExpr?, hb, EvalResult.ofOption]
  have hindex : evalExpr? config frame evm (.storage ⟨trackingIndexName borrow, []⟩) =
      .ok (.int (accountRewardIndex evm borrow).toNat) := by
    simpa only [← hc] using evalTrackingIndex evm frame.locals frame.immutables borrow hx
  by_cases hle : basic.index.toNat ≤ (accountRewardIndex evm borrow).toNat
  · have hdelta := checkedNarrowSubSourceOk ⟨64, by decide⟩ hindex (evalBasicIndex heb)
      (accountRewardIndex_lt evm borrow) hle
    have hdt : delta.toNat < 2^64 := accountRewardDelta_lt hle
    have hcast := castUintSourceOk ⟨256, by decide⟩ hdelta (lt_trans hdt (by decide))
    apply ExecBlock.consNormal (ExecStmt.letDecl hcast)
    have heprincipal : evalExpr? config f1 evm (.var "principal") =
        .ok (.int (signed104 principal)) := by
      have hp1 : f1.locals.get? "principal" = some (.int (signed104 principal)) := by
        simpa only [f1, Std.HashMap.get?_eq_getElem?, Std.HashMap.getElem?_insert] using hp
      simp only [evalExpr?, hp1, EvalResult.ofOption]
    have hem := accountMagnitude_source borrow heprincipal hsign
    by_cases hmin : -(2^103 : Int) < signed104 principal
    · rw [if_pos hmin] at hem
      have hedelta : evalExpr? config f1 evm (.var "indexDelta") = .ok (.int delta.toNat) := by
        simp only [evalExpr?, f1, Std.HashMap.get?_eq_getElem?, Std.HashMap.getElem?_insert,
          EvalResult.ofOption]
        rfl
      have hr := baseReward_call v f1 evm (accountMagnitude principal borrow) delta _ _
        (accountRewardName borrow) hc hi hem hedelta (accountMagnitude_lt borrow hmin) hdt
      by_cases hv : BaseRewardValid v (accountMagnitude principal borrow) delta
      · rw [if_pos hv] at hr
        apply ExecBlock.consNormal hr
        have hb2 : f2.locals.get? "basic" = some (userBasicValue basic) := by
          cases borrow <;>
            simpa only [f2, f1, accountRewardName, Bool.false_eq_true, if_false, if_true,
              Std.HashMap.get?_eq_getElem?, Std.HashMap.getElem?_insert] using hb
        have heb2 : evalExpr? config f2 evm (.var "basic") = .ok (userBasicValue basic) := by
          simp only [evalExpr?, hb2, EvalResult.ofOption]
        have her : evalExpr? config f2 evm (.var (accountRewardName borrow)) =
            .ok (.int reward.toNat) := by
          simp only [evalExpr?, f2, Std.HashMap.get?_eq_getElem?, Std.HashMap.getElem?_insert,
            beq_self_eq_true, if_true, EvalResult.ofOption]
        by_cases hadd : basic.accrued.toNat + reward.toNat < 2^64
        · rw [if_pos (show AccountRewardValid v evm basic principal borrow from
            ⟨hle, hmin, hv, hadd⟩)]
          have hsum : (basic.accrued + reward).toNat < 2^64 := by
            change (UInt256.add basic.accrued reward).toNat < 2^64
            rw [addWord_toNat _ _ (lt_trans hadd (by decide))]
            exact hadd
          exact ExecBlock.consNormal (ExecStmt.assign
            (checkedNarrowAddSourceOk ⟨64, by decide⟩ (by decide) (evalBasicAccrued heb2) her hadd)
            (assignBasicAccrued (basic.accrued + reward) hsum hb2)) ExecBlock.nil
        · rw [if_neg (show ¬ AccountRewardValid v evm basic principal borrow from
            fun h ↦ hadd h.2.2.2)]
          exact ExecBlock.consRevert (ExecStmt.assignExprRevert
            (uintRangeSourceOverflow ⟨64, by decide⟩
              (naturalAddSource (evalBasicAccrued heb2) her) (le_of_not_gt hadd)))
      · rw [if_neg hv] at hr
        rw [if_neg (show ¬ AccountRewardValid v evm basic principal borrow from
          fun h ↦ hv h.2.2.1)]
        exact ExecBlock.consRevert hr
    · rw [if_neg hmin] at hem
      rw [if_neg (show ¬ AccountRewardValid v evm basic principal borrow from fun h ↦ hmin h.2.1)]
      apply ExecBlock.consRevert (ExecStmt.internalCallArgsRevert ?_)
      change evalExprs? config f1 evm _ = _
      simp only [evalExprs?, baseRewardExpr, evalExpr?, hem, bind, EvalResult.bind]
  · rw [if_neg (show ¬ AccountRewardValid v evm basic principal borrow from fun h ↦ hle h.1)]
    have hr := checkedNarrowSubSourceUnderflow ⟨64, by decide⟩ hindex (evalBasicIndex heb)
      (Nat.lt_of_not_ge hle)
    apply ExecBlock.consRevert (ExecStmt.letDeclRevert ?_)
    simp only [evalExpr?, hr, bind, EvalResult.bind]

end Benchmarks.CompoundIII.Comet
