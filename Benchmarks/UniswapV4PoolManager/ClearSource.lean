import Benchmarks.UniswapV4PoolManager.SafeCast
import Benchmarks.UniswapV4PoolManager.AccountDeltaSource

/-! Source execution of `clear`, including all guards and static calls. -/
open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.UniswapV4PoolManager
set_option maxRecDepth 5000

def clearFinalFrame (f : Frame) (evm : EVM.State) (currency : AccountAddress) (amount : UInt256) : Frame :=
  let locals := f.locals.insert "__c0" (.bool true)
  let locals := locals.insert "current" (.int (currencyDeltaValue evm evm.executionEnv.source currency))
  let locals := locals.insert "amountDelta" (.int (Int.ofNat amount.toNat))
  {f with locals := locals.insert "__c3" .unit}

def clearBodyResult (f : Frame) (evm : EVM.State) (currency : AccountAddress) (amount : UInt256) : ExecResult :=
  if transientWord evm lockSlot = ⟨0⟩ then .reverted else
  if amount.toNat < 2^127 then
    if Int.ofNat amount.toNat = currencyDeltaValue evm evm.executionEnv.source currency then
      if amount.toNat ≠ 0 ∧ evm.executionEnv.perm = false then .staticViolation else
      .returned (clearFinalFrame f evm currency amount)
        (accountDeltaPost evm evm.executionEnv.source currency (-(Int.ofNat amount.toNat))) none
    else .reverted
  else .reverted

theorem clearBodyExec {evm : EVM.State} {locals imms : Store} {currency : AccountAddress} {amount : UInt256}
    (hwv : evm.executionEnv.weiValue = ⟨0⟩) (hhi : evm.executionEnv.calldata.size < calldataLimit)
    (hc : locals.get? "currency" = some (.address currency))
    (ha : locals.get? "amount" = some (.int (Int.ofNat amount.toNat))) :
    ExecTransitionBody config contract evm locals clearTransition.body
      (clearBodyResult (calldataFrame contract locals imms evm) evm currency amount) imms := by
  let f := calldataFrame contract locals imms evm
  have hlock := lockCall (f := f) (evm := evm) rfl "__c0"
  rw [clearBodyResult]
  by_cases hl : transientWord evm lockSlot = ⟨0⟩
  · rw [if_pos hl]
    rw [decide_eq_false (not_not.mpr hl)] at hlock
    apply ExecFuncBody.execBlockRevert
    apply nonpayableCalldataBlock hwv hhi
    refine ExecBlock.consNormal hlock (ExecBlock.consRevert (ExecStmt.iteTrue ?_ ?_))
    · exact evalNotBool (va := false) (evalLocalValue (f := {f with locals := f.locals.insert "__c0" (.bool false)})
        (store_get_self _ _ _))
    · exact ExecBlock.consRevert (ExecStmt.requireFalse (by simp only [evalExpr?]; rfl))
  · rw [if_neg hl]
    rw [decide_eq_true hl] at hlock
    let f1 := {f with locals := f.locals.insert "__c0" (.bool true)}
    have hlockGuard : ExecStmt config f1 evm clearTransition.body[4]! (.ok f1 evm) :=
      ExecStmt.iteFalse (evalNotBool (va := true) (evalLocalValue (f := f1) (store_get_self _ _ _))) ExecBlock.nil
    have hc1 : f1.locals.get? "currency" = some (.address currency) :=
      (store_get_ne _ _ (by decide : ("__c0" == "currency") = false)).trans
        ((store_get_ne _ _ (by decide : ("__calldata" == "currency") = false)).trans hc)
    have hcaller : evalExpr? config f1 evm (.env .caller) = .ok (.address evm.executionEnv.source) := by
      simp only [evalExpr?, envValue, pure]
    have hget := getDeltaCall rfl (evalLocalValue hc1) hcaller "current"
    let current := currencyDeltaValue evm evm.executionEnv.source currency
    let f2 := {f1 with locals := f1.locals.insert "current" (.int current)}
    have ha2 : f2.locals.get? "amount" = some (.int (Int.ofNat amount.toNat)) :=
      (store_get_ne _ _ (by decide : ("current" == "amount") = false)).trans
        ((store_get_ne _ _ (by decide : ("__c0" == "amount") = false)).trans
          ((store_get_ne _ _ (by decide : ("__calldata" == "amount") = false)).trans ha))
    by_cases hfit : amount.toNat < 2^127
    · rw [if_pos hfit]
      have hcast := uintToInt128Call rfl (evalLocalValue (cfg := config) (evm := evm) ha2) hfit "amountDelta"
      let f3 := {f2 with locals := f2.locals.insert "amountDelta" (.int (Int.ofNat amount.toNat))}
      have hamount3 : f3.locals.get? "amountDelta" = some (.int (Int.ofNat amount.toNat)) := store_get_self _ _ _
      have hcurrent3 : f3.locals.get? "current" = some (.int current) :=
        (store_get_ne _ _ (by decide : ("amountDelta" == "current") = false)).trans (store_get_self _ _ _)
      have hneq : evalExpr? config f3 evm (.binary .ne (.var "amountDelta") (.var "current")) =
          .ok (.bool (decide (Int.ofNat amount.toNat ≠ current))) := by
        rw [evalExpr_binary_nonshort (by decide) (by decide), evalLocalValue hamount3, evalLocalValue hcurrent3]
        simp only [bind, EvalResult.bind, evalBinaryOp?, BEq.beq, Value.int.injEq, ← decide_not]
      by_cases heq : Int.ofNat amount.toNat = current
      · rw [if_pos heq]
        have heqGuard : ExecStmt config f3 evm clearTransition.body[7]! (.ok f3 evm) :=
          ExecStmt.iteFalse (hneq.trans (by rw [decide_eq_false (not_not.mpr heq)])) ExecBlock.nil
        have hc3 : f3.locals.get? "currency" = some (.address currency) :=
          (store_get_ne _ _ (by decide : ("amountDelta" == "currency") = false)).trans
            ((store_get_ne _ _ (by decide : ("current" == "currency") = false)).trans hc1)
        have hdelta : evalExpr? config f3 evm (.cast
            (.binary .sub (.intLit 0) (.var "amountDelta")) (.elem (.int (.sint ⟨128, by decide⟩)))) =
            .ok (.int (-(Int.ofNat amount.toNat))) := by
          have hsub : evalExpr? config f3 evm (.binary .sub (.intLit 0) (.var "amountDelta")) =
              .ok (.int (-(Int.ofNat amount.toNat))) := by
            simp only [evalExpr?, hamount3, bind, EvalResult.bind, EvalResult.ofOption, evalBinaryOp?, pure, zero_sub]
          have h := evalExpr_cast_int (intType := .sint ⟨128, by decide⟩) hsub
          rw [normalizeSignedSelf ⟨128, by decide⟩ _
            (by change -(2^127 : Int) ≤ -(Int.ofNat amount.toNat); simp only [Int.ofNat_eq_natCast]; omega)
            (by change -(Int.ofNat amount.toNat) < (2^127 : Int); simp only [Int.ofNat_eq_natCast]; omega)] at h
          exact h
        have hcall := accountDeltaCall (f := f3) (evm := evm) (et := .env .caller) rfl (evalLocalValue hc3) hdelta
          (by simp only [evalExpr?, envValue, pure]; rfl) "__c3"
        have hsum : current + -(Int.ofNat amount.toNat) = 0 := by rw [← heq]; omega
        have hsumFit : int256Fits (current + -(Int.ofNat amount.toNat)) := by rw [hsum]; constructor <;> decide
        rw [accountDeltaCallResult] at hcall
        by_cases hz : amount.toNat = 0
        · have hzInt : -(Int.ofNat amount.toNat) = 0 := by rw [hz]; rfl
          rw [if_pos hzInt] at hcall
          rw [if_neg (by simp only [hz, ne_eq, not_true_eq_false, false_and, not_false_eq_true])]
          rw [accountDeltaPost, if_pos hzInt]
          apply ExecFuncBody.execBlockOK
          apply nonpayableCalldataBlock hwv hhi
          exact ExecBlock.consNormal hlock (ExecBlock.consNormal hlockGuard (ExecBlock.consNormal hget
            (ExecBlock.consNormal hcast (ExecBlock.consNormal heqGuard (ExecBlock.consNormal hcall ExecBlock.nil)))))
        · have hzInt : -(Int.ofNat amount.toNat) ≠ 0 := by simp only [Int.ofNat_eq_natCast]; omega
          rw [if_neg hzInt, if_pos hsumFit] at hcall
          by_cases hp : evm.executionEnv.perm = false
          · rw [if_pos hp] at hcall
            rw [if_pos ⟨hz, hp⟩]
            apply ExecFuncBody.execBlockStatic
            apply nonpayableCalldataBlock hwv hhi
            exact ExecBlock.consNormal hlock (ExecBlock.consNormal hlockGuard (ExecBlock.consNormal hget
              (ExecBlock.consNormal hcast (ExecBlock.consNormal heqGuard (ExecBlock.consStatic hcall)))))
          · rw [if_neg hp] at hcall
            rw [if_neg (fun he => hp he.2)]
            apply ExecFuncBody.execBlockOK
            apply nonpayableCalldataBlock hwv hhi
            exact ExecBlock.consNormal hlock (ExecBlock.consNormal hlockGuard (ExecBlock.consNormal hget
              (ExecBlock.consNormal hcast (ExecBlock.consNormal heqGuard (ExecBlock.consNormal hcall ExecBlock.nil)))))
      · rw [if_neg heq]
        apply ExecFuncBody.execBlockRevert
        apply nonpayableCalldataBlock hwv hhi
        exact ExecBlock.consNormal hlock (ExecBlock.consNormal hlockGuard (ExecBlock.consNormal hget
          (ExecBlock.consNormal hcast (ExecBlock.consRevert (ExecStmt.iteTrue
            (hneq.trans (by rw [decide_eq_true heq]))
            (ExecBlock.consRevert (ExecStmt.requireFalse (by simp only [evalExpr?]; rfl))))))))
    · rw [if_neg hfit]
      have hcast := uintToInt128CallReverts rfl (evalLocalValue (cfg := config) (evm := evm) ha2) hfit "amountDelta"
      apply ExecFuncBody.execBlockRevert
      apply nonpayableCalldataBlock hwv hhi
      exact ExecBlock.consNormal hlock (ExecBlock.consNormal hlockGuard
        (ExecBlock.consNormal hget (ExecBlock.consRevert hcast)))

end Benchmarks.UniswapV4PoolManager
