import Benchmarks.Midnight.LiquidateSourceFrame

variable {fork : Ethereum.Fork}

/-! Source evaluation of liquidation's input-consistency and nonzero-debt guards. -/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Midnight

def liquidateInputGuard : Expr :=
  .binary .or (.binary .eq (.var "repaidUnits") (.intLit 0))
    (.binary .eq (.var "seizedAssets") (.intLit 0))

def liquidateDebtGuard : Expr :=
  .binary .gt (.storage { base := "_position", steps := [.field "debt"] }) (.intLit 0)

theorem liquidateInputGuard_eval {frame : Frame} {evm : State} {seized repaid : UInt256}
    (hs : frame.locals.get? "seizedAssets" = some (.int seized.toNat))
    (hr : frame.locals.get? "repaidUnits" = some (.int repaid.toNat)) :
    evalExpr? config frame evm liquidateInputGuard =
      .ok (.bool (decide (repaid = ⟨0⟩ ∨ seized = ⟨0⟩))) := by
  have hz (w : UInt256) : w.toNat = 0 ↔ w = ⟨0⟩ :=
    ⟨uint256_toNat_eq_zero, by rintro rfl; rfl⟩
  simp only [liquidateInputGuard, evalExpr?, hr, hs, EvalResult.ofOption,
    bind, pure, EvalResult.bind, evalBinaryOp?, Reasoning.VyperDispatch.value_int_beq,
    Int.natCast_eq_zero, hz]
  by_cases h : repaid = ⟨0⟩ <;> simp only [h, decide_true, decide_false, if_true, if_false,
    true_or, false_or]

theorem liquidateDebtGuard_eval {frame : Frame} {evm : State} {id borrower : UInt256}
    (hb : borrower.toNat < EVM.addressModulus)
    (hp : frame.locals.get? "_position" =
      some (.storageRef (positionRef id borrower) positionType)) :
    evalExpr? config frame evm liquidateDebtGuard =
      .ok (.bool (decide (0 < (low128 (healthPositionWord evm id borrower)).toNat))) := by
  rw [liquidateDebtGuard, evalExpr_binary_nonshort (by decide) (by decide), evalHealthDebt hb hp]
  simp only [evalExpr?, bind, pure, EvalResult.bind, evalBinaryOp?, Int.natCast_pos]

theorem liquidateInputRevert {frame : Frame} {evm : State} {seized repaid : UInt256}
    (hs : frame.locals.get? "seizedAssets" = some (.int seized.toNat))
    (hr : frame.locals.get? "repaidUnits" = some (.int repaid.toNat))
    (hbad : ¬ (repaid = ⟨0⟩ ∨ seized = ⟨0⟩)) :
    ExecBlock fork config frame evm (liquidateTransition.body.drop 6) .reverted := by
  apply ExecBlock.consRevert (ExecStmt.requireFalse ?_)
  exact (liquidateInputGuard_eval hs hr).trans (by rw [decide_eq_false hbad])

theorem liquidateDebtRevert {frame : Frame} {evm : State} {id borrower seized repaid : UInt256}
    (hs : frame.locals.get? "seizedAssets" = some (.int seized.toNat))
    (hr : frame.locals.get? "repaidUnits" = some (.int repaid.toNat))
    (hp : frame.locals.get? "_position" =
      some (.storageRef (positionRef id borrower) positionType))
    (hb : borrower.toNat < EVM.addressModulus) (hinput : repaid = ⟨0⟩ ∨ seized = ⟨0⟩)
    (hzero : low128 (healthPositionWord evm id borrower) = ⟨0⟩) :
    ExecBlock fork config frame evm (liquidateTransition.body.drop 6) .reverted := by
  refine ExecBlock.consNormal (ExecStmt.requireTrue ?_)
    (ExecBlock.consRevert (ExecStmt.requireFalse ?_))
  · exact (liquidateInputGuard_eval hs hr).trans (by rw [decide_eq_true hinput])
  · exact (liquidateDebtGuard_eval hb hp).trans (by rw [hzero]; rfl)

theorem liquidateGuardsSource {frame : Frame} {evm : State} {id borrower seized repaid : UInt256}
    {result : ExecResult}
    (hs : frame.locals.get? "seizedAssets" = some (.int seized.toNat))
    (hr : frame.locals.get? "repaidUnits" = some (.int repaid.toNat))
    (hp : frame.locals.get? "_position" =
      some (.storageRef (positionRef id borrower) positionType))
    (hb : borrower.toNat < EVM.addressModulus) (hinput : repaid = ⟨0⟩ ∨ seized = ⟨0⟩)
    (hdebt : 0 < (low128 (healthPositionWord evm id borrower)).toNat)
    (htail : ExecBlock fork config frame evm (liquidateTransition.body.drop 8) result) :
    ExecBlock fork config frame evm (liquidateTransition.body.drop 6) result := by
  refine ExecBlock.consNormal (ExecStmt.requireTrue ?_)
    (ExecBlock.consNormal (ExecStmt.requireTrue ?_) htail)
  · exact (liquidateInputGuard_eval hs hr).trans (by rw [decide_eq_true hinput])
  · exact (liquidateDebtGuard_eval hb hp).trans (by rw [decide_eq_true hdebt])

end Benchmarks.Midnight
