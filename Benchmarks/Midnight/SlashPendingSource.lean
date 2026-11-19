import Benchmarks.Midnight.PositionViewSourceBase

/-! Source execution and reverts for pending-fee slashing. -/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Midnight

def slashPendingFrame (frame : Frame) (credit pending postCredit : UInt256) : Frame :=
  if 0 < credit.toNat then
    wordLocal (wordLocal frame "decrease" (mulDivUp pending (UInt256.sub credit postCredit) credit))
      "postSlashPendingFee" (slashPending credit pending postCredit)
  else frame

theorem slashPendingFrame_contract (frame : Frame) (credit pending postCredit : UInt256) :
    (slashPendingFrame frame credit pending postCredit).contract = frame.contract := by
  unfold slashPendingFrame
  split <;> rfl

theorem slashPendingFrame_get (frame : Frame) (credit pending postCredit : UInt256) (name : Ident)
    (h₁ : "decrease" ≠ name) (h₂ : "postSlashPendingFee" ≠ name) :
    (slashPendingFrame frame credit pending postCredit).locals.get? name = frame.locals.get? name := by
  unfold slashPendingFrame
  split
  · rw [wordLocal_get_ne _ _ _ _ h₂, wordLocal_get_ne _ _ _ _ h₁]
  · rfl

theorem slashPendingFrame_value {frame : Frame} (credit pending postCredit : UInt256)
    (hzero : frame.locals.get? "postSlashPendingFee" = some (.int 0)) :
    (slashPendingFrame frame credit pending postCredit).locals.get? "postSlashPendingFee" =
      some (.int (slashPending credit pending postCredit).toNat) := by
  unfold slashPendingFrame
  split
  · exact wordLocal_get _ _ _
  · rename_i h
    simpa only [slashPending, h, if_false] using hzero

def slashPendingArgs : List Expr :=
  [.var "_pendingFee", .inRange (.uint ⟨256, by decide⟩)
    (.binary .sub (.var "_credit") (.var "postSlashCredit")), .var "_credit"]

theorem evalSlashPendingArgs {cfg : Config} {frame : Frame} {evm : EVM.State}
    {credit pending postCredit : UInt256}
    (hc : frame.locals.get? "_credit" = some (.int credit.toNat))
    (hp : frame.locals.get? "_pendingFee" = some (.int pending.toNat))
    (hpc : frame.locals.get? "postSlashCredit" = some (.int postCredit.toNat))
    (hle : postCredit.toNat ≤ credit.toNat) :
    evalExprs? cfg frame evm slashPendingArgs =
      .ok [.int pending.toNat, .int (UInt256.sub credit postCredit).toNat, .int credit.toNat] := by
  have hsub := evalExpr_uint256_sub (evalWordLocal (cfg := cfg) (evm := evm) hc)
    (evalWordLocal hpc) hle
  simp only [slashPendingArgs, evalExprs?, evalWordLocal hp, evalWordLocal hc, hsub,
    bind, pure, EvalResult.bind, uint256Value, Int.ofNat_eq_natCast]

theorem slashPendingSource {frame : Frame} {evm : EVM.State} {credit pending postCredit : UInt256}
    (hc : frame.contract = contract)
    (hcredit : frame.locals.get? "_credit" = some (.int credit.toNat))
    (hpending : frame.locals.get? "_pendingFee" = some (.int pending.toNat))
    (hpc : frame.locals.get? "postSlashCredit" = some (.int postCredit.toNat))
    (hzero : frame.locals.get? "postSlashPendingFee" = some (.int 0))
    (hsafe : SlashPendingSafe credit pending postCredit) :
    ExecStmt config frame evm (positionViewFunction.body[7]!)
      (.ok (slashPendingFrame frame credit pending postCredit) evm) := by
  by_cases hpos : 0 < credit.toNat
  · obtain ⟨hsub, hmul, hdecrease⟩ := hsafe hpos
    rw [slashPendingFrame, if_pos hpos]
    simp only [slashPending, hpos, if_true]
    apply ExecStmt.iteTrue
      ((evalExpr_uint256_var_positive evm "_credit" credit hcredit).trans
        (by rw [decide_eq_true hpos]))
    apply ExecBlock.consNormal (callMulDivUp hc
      (evalSlashPendingArgs hcredit hpending hpc hsub) hmul (name := "decrease"))
    apply ExecBlock.consNormal (execLocalAssign (old := .int 0) ?_ ?_) ExecBlock.nil
    · change (wordLocal frame "decrease" _).locals.get? "postSlashPendingFee" = some (.int 0)
      rw [wordLocal_get_ne _ _ _ _ (by decide)]
      exact hzero
    · apply evalExpr_uint256_sub _ _ hdecrease
      · apply evalWordLocal
        change (wordLocal frame "decrease" _).locals.get? "_pendingFee" = _
        rw [wordLocal_get_ne _ _ _ _ (by decide)]
        exact hpending
      · exact evalWordLocal (wordLocal_get _ _ _)
  · rw [slashPendingFrame, if_neg hpos]
    exact ExecStmt.iteFalse
      ((evalExpr_uint256_var_positive evm "_credit" credit hcredit).trans
        (by rw [decide_eq_false hpos])) ExecBlock.nil

theorem slashPendingSourceRevert {frame : Frame} {evm : EVM.State} {credit pending postCredit : UInt256}
    (hc : frame.contract = contract)
    (hcredit : frame.locals.get? "_credit" = some (.int credit.toNat))
    (hpending : frame.locals.get? "_pendingFee" = some (.int pending.toNat))
    (hpc : frame.locals.get? "postSlashCredit" = some (.int postCredit.toNat))
    (hbad : ¬ SlashPendingSafe credit pending postCredit) :
    ExecStmt config frame evm (positionViewFunction.body[7]!) .reverted := by
  have hpos : 0 < credit.toNat := by
    by_contra hn
    exact hbad (fun h ↦ False.elim (hn h))
  apply ExecStmt.iteTrue
    ((evalExpr_uint256_var_positive evm "_credit" credit hcredit).trans
      (by rw [decide_eq_true hpos]))
  by_cases hsub : postCredit.toNat ≤ credit.toNat
  · have hargs := evalSlashPendingArgs (cfg := config) (evm := evm) hcredit hpending hpc hsub
    by_cases hmul : MulDivUpSafe pending (UInt256.sub credit postCredit) credit
    · have hdec : pending.toNat < (mulDivUp pending (UInt256.sub credit postCredit) credit).toNat := by
        by_contra hn
        exact hbad (fun _ ↦ ⟨hsub, hmul, by omega⟩)
      apply ExecBlock.consNormal (callMulDivUp hc hargs hmul (name := "decrease"))
      apply ExecBlock.consRevert
      apply ExecStmt.assignExprRevert
      apply evalCheckedSubUnderflow ⟨256, by decide⟩ _ _ hdec
      · apply evalWordLocal
        change (wordLocal frame "decrease" _).locals.get? "_pendingFee" = _
        rw [wordLocal_get_ne _ _ _ _ (by decide)]
        exact hpending
      · exact evalWordLocal (wordLocal_get _ _ _)
    · exact ExecBlock.consRevert (callMulDivUpRevert hc hargs hmul)
  · apply ExecBlock.consRevert
    apply ExecStmt.internalCallArgsRevert
    have hsubEval := evalCheckedSubUnderflow (cfg := config) (evm := evm) ⟨256, by decide⟩
      (evalWordLocal hcredit) (evalWordLocal hpc) (Nat.lt_of_not_ge hsub)
    simp only [evalExprs?, evalWordLocal hpending, hsubEval, bind, EvalResult.bind]

end Benchmarks.Midnight
