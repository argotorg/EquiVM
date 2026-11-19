import Benchmarks.Midnight.LiquidateFeeSource

/-! The remaining-fee branch and final continuous-fee storage write. -/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Midnight

set_option maxRecDepth 2000000

def liquidateFeeValue (evm : State) (id oldLoss : UInt256) : UInt256 :=
  if oldLoss.toNat < 2 ^ 128 - 1 then
    liquidateRemainingFees (marketBalanceWord evm id 2) oldLoss (marketLossWord evm id)
  else ⟨0⟩

def liquidateFeeFrame (frame : Frame) (oldLoss amount : UInt256) : Frame :=
  let f := wordLocal frame "remainingFees" ⟨0⟩
  if oldLoss.toNat < 2 ^ 128 - 1 then liquidateFeeInnerFrame f amount else f

def LiquidateFeeSafe (evm : State) (id oldLoss : UInt256) : Prop :=
  oldLoss.toNat < 2 ^ 128 - 1 →
    (liquidateRemainingFees (marketBalanceWord evm id 2) oldLoss (marketLossWord evm id)).toNat < 2 ^ 128

theorem liquidateFeesSource {frame : Frame} {evm : State} {id oldLoss : UInt256}
    (hc : frame.contract = contract)
    (hm : frame.locals.get? "_marketState" = some (.storageRef (marketStateRef id) marketStateType))
    (hl : frame.locals.get? "_lossFactor" = some (.int oldLoss.toNat))
    (hp : evm.executionEnv.perm = true) :
    (¬ LiquidateFeeSafe evm id oldLoss ∧
      ExecBlock config frame evm (liquidateBadDebtBody.drop 8) .reverted) ∨
    (LiquidateFeeSafe evm id oldLoss ∧ ExecBlock config frame evm (liquidateBadDebtBody.drop 8)
      (.ok (liquidateFeeFrame frame oldLoss (liquidateFeeValue evm id oldLoss))
        (marketBalanceStore evm id 2 (liquidateFeeValue evm id oldLoss)))) := by
  let f0 := wordLocal frame "remainingFees" ⟨0⟩
  have hs0 : ExecStmt config frame evm (liquidateBadDebtBody[8]!) (.ok f0 evm) :=
    ExecStmt.letDecl (by simp [evalExpr?, pure])
  have hm0 : f0.locals.get? "_marketState" =
      some (.storageRef (marketStateRef id) marketStateType) := by
    simpa only [f0, wordLocal_get_ne _ _ _ _ (show "remainingFees" ≠ "_marketState" by decide)] using hm
  have hl0 : f0.locals.get? "_lossFactor" = some (.int oldLoss.toNat) := by
    simpa only [f0, wordLocal_get_ne _ _ _ _ (show "remainingFees" ≠ "_lossFactor" by decide)] using hl
  have hr0 : f0.locals.get? "remainingFees" = some (.int (⟨0⟩ : UInt256).toNat) := wordLocal_get _ _ _
  have hcond : evalExpr? config f0 evm
      (.binary .lt (.var "_lossFactor") (.intLit (2 ^ 128 - 1))) =
      .ok (.bool (decide (oldLoss.toNat < 2 ^ 128 - 1))) := by
    simp only [evalExpr?, hl0, EvalResult.ofOption, bind, pure, EvalResult.bind, evalBinaryOp?]
    norm_num
  by_cases ho : oldLoss.toNat < 2 ^ 128 - 1
  · rcases liquidateFeeInnerSource (frame := f0) hc hm0 hl0 hr0 ho with ⟨hbad, hrev⟩ | ⟨hfit, hinner⟩
    · refine Or.inl ⟨fun h ↦ Nat.not_lt.mpr hbad (h ho), ?_⟩
      exact ExecBlock.consNormal hs0 (ExecBlock.consRevert
        (ExecStmt.iteTrue (hcond.trans (by rw [decide_eq_true ho])) hrev))
    · let amount := liquidateRemainingFees (marketBalanceWord evm id 2) oldLoss (marketLossWord evm id)
      let f1 := liquidateFeeInnerFrame f0 amount
      have hs1 : ExecStmt config f0 evm (liquidateBadDebtBody[9]!) (.ok f1 evm) :=
        ExecStmt.iteTrue (hcond.trans (by rw [decide_eq_true ho])) hinner
      have hm1 : f1.locals.get? "_marketState" =
          some (.storageRef (marketStateRef id) marketStateType) := by
        simpa only [f1, liquidateFeeInnerFrame,
          wordLocal_get_ne _ _ _ _ (show "remainingFees" ≠ "_marketState" by decide),
          wordLocal_get_ne _ _ _ _ (show "checkedAmount" ≠ "_marketState" by decide),
          wordLocal_get_ne _ _ _ _ (show "amount" ≠ "_marketState" by decide)] using hm0
      have hr1 : f1.locals.get? "remainingFees" = some (.int amount.toNat) := wordLocal_get _ _ _
      have hs2 : ExecStmt config f1 evm (liquidateBadDebtBody[10]!)
          (.ok f1 (marketBalanceStore evm id 2 amount)) :=
        ExecStmt.assign (Or.inr hp) (evalWordLocal hr1) (assignMarketBalance 2 _ hm1)
      refine Or.inr ⟨fun _ ↦ hfit, ?_⟩
      simpa only [liquidateFeeFrame, liquidateFeeValue, if_pos ho] using
        (show ExecBlock config frame evm (liquidateBadDebtBody.drop 8)
          (.ok f1 (marketBalanceStore evm id 2 amount)) from ExecBlock.consNormal hs0
            (ExecBlock.consNormal hs1 (ExecBlock.consNormal hs2 ExecBlock.nil)))
  · have hs1 : ExecStmt config f0 evm (liquidateBadDebtBody[9]!) (.ok f0 evm) :=
      ExecStmt.iteFalse (hcond.trans (by rw [decide_eq_false ho])) ExecBlock.nil
    have hs2 : ExecStmt config f0 evm (liquidateBadDebtBody[10]!)
        (.ok f0 (marketBalanceStore evm id 2 ⟨0⟩)) :=
      ExecStmt.assign (Or.inr hp) (evalWordLocal hr0) (assignMarketBalance 2 _ hm0)
    refine Or.inr ⟨fun h ↦ (ho h).elim, ?_⟩
    simpa only [liquidateFeeFrame, liquidateFeeValue, if_neg ho] using
      (show ExecBlock config frame evm (liquidateBadDebtBody.drop 8)
        (.ok f0 (marketBalanceStore evm id 2 ⟨0⟩)) from ExecBlock.consNormal hs0
          (ExecBlock.consNormal hs1 (ExecBlock.consNormal hs2 ExecBlock.nil)))

end Benchmarks.Midnight
