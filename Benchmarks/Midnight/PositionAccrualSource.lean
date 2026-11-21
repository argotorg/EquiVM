import Benchmarks.Midnight.PositionViewSourceBase

/-! Source execution and reverts of position fee accrual. -/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Midnight

def positionAccrualFrame (frame : Frame) (pending last maturity time : UInt256) : Frame :=
  if last.toNat < maturity.toNat then
    wordLocal (wordLocal frame "accrued" (mulDivDown pending
      (UInt256.sub (wordMin time maturity) last) (UInt256.sub maturity last)))
      "fee" (positionAccruedFee pending last maturity time)
  else frame

theorem positionAccrualFrame_contract (frame : Frame) (p l m t : UInt256) :
    (positionAccrualFrame frame p l m t).contract = frame.contract := by
  unfold positionAccrualFrame
  split <;> rfl

theorem positionAccrualFrame_get (frame : Frame) (p l m t : UInt256) (name : Ident)
    (h₁ : "accrued" ≠ name) (h₂ : "fee" ≠ name) :
    (positionAccrualFrame frame p l m t).locals.get? name = frame.locals.get? name := by
  unfold positionAccrualFrame
  split
  · rw [wordLocal_get_ne _ _ _ _ h₂, wordLocal_get_ne _ _ _ _ h₁]
  · rfl

theorem positionAccrualFrame_value {frame : Frame} (p l m t : UInt256)
    (hzero : frame.locals.get? "fee" = some (.int 0)) :
    (positionAccrualFrame frame p l m t).locals.get? "fee" =
      some (.int (positionAccruedFee p l m t).toNat) := by
  unfold positionAccrualFrame
  split
  · exact wordLocal_get _ _ _
  · rename_i h
    simpa only [positionAccruedFee, h, if_false] using hzero

def positionAccrualArgs : List Expr :=
  [.var "postSlashPendingFee",
   .inRange (.uint ⟨256, by decide⟩) (.binary .sub (.var "accrualEnd") (.var "_lastAccrual")),
   .inRange (.uint ⟨256, by decide⟩)
     (.binary .sub (.field (.var "market") "maturity") (.var "_lastAccrual"))]

theorem evalPositionAccrualCond {cfg : Config} {frame : Frame} {evm : EVM.State}
    {m : MarketData} {last : UInt256}
    (hm : frame.locals.get? "market" = some (Model.marketValue m.value))
    (hl : frame.locals.get? "_lastAccrual" = some (.int last.toNat)) :
    evalExpr? cfg frame evm (.binary .lt (.var "_lastAccrual") (.field (.var "market") "maturity")) =
      .ok (.bool (decide (last.toNat < m.maturity.toNat))) := by
  rw [evalExpr_binary_nonshort (by decide) (by decide), evalWordLocal hl, evalMarketMaturity hm]
  simp only [bind, EvalResult.bind, evalBinaryOp?, Int.ofNat_lt]

theorem evalPositionAccrualArgs {cfg : Config} {frame : Frame} {evm : EVM.State}
    {m : MarketData} {pending last time : UInt256}
    (hm : frame.locals.get? "market" = some (Model.marketValue m.value))
    (hp : frame.locals.get? "postSlashPendingFee" = some (.int pending.toNat))
    (hl : frame.locals.get? "_lastAccrual" = some (.int last.toNat))
    (ht : frame.locals.get? "accrualEnd" = some (.int (wordMin time m.maturity).toNat))
    (hle : last.toNat ≤ (wordMin time m.maturity).toNat) (hlm : last.toNat ≤ m.maturity.toNat) :
    evalExprs? cfg frame evm positionAccrualArgs =
      .ok [.int pending.toNat, .int (UInt256.sub (wordMin time m.maturity) last).toNat,
        .int (UInt256.sub m.maturity last).toNat] := by
  have hsub := evalExpr_uint256_sub (evalWordLocal (cfg := cfg) (evm := evm) ht)
    (evalWordLocal hl) hle
  have hdiff := evalExpr_uint256_sub (evalMarketMaturity (cfg := cfg) (evm := evm) hm)
    (evalWordLocal hl) hlm
  simp only [positionAccrualArgs, evalExprs?, evalWordLocal hp, hsub, hdiff,
    bind, pure, EvalResult.bind, uint256Value, Int.ofNat_eq_natCast]

theorem positionAccrualSource {frame : Frame} {evm : EVM.State} {m : MarketData}
    {pending last time : UInt256} (hc : frame.contract = contract)
    (hm : frame.locals.get? "market" = some (Model.marketValue m.value))
    (hp : frame.locals.get? "postSlashPendingFee" = some (.int pending.toNat))
    (hl : frame.locals.get? "_lastAccrual" = some (.int last.toNat))
    (ht : frame.locals.get? "accrualEnd" = some (.int (wordMin time m.maturity).toNat))
    (hz : frame.locals.get? "fee" = some (.int 0))
    (hsafe : PositionAccrualSafe pending last m.maturity time) :
    ExecStmt config frame evm (positionViewFunction.body[11]!)
      (.ok (positionAccrualFrame frame pending last m.maturity time) evm) := by
  by_cases hlt : last.toNat < m.maturity.toNat
  · obtain ⟨hsub, hprod⟩ := hsafe hlt
    have hnz : UInt256.sub m.maturity last ≠ ⟨0⟩ := by
      intro he
      have he' := congrArg UInt256.toNat he
      rw [usub_toNat (Nat.le_of_lt hlt)] at he'
      change m.maturity.toNat - last.toNat = 0 at he'
      omega
    rw [positionAccrualFrame, if_pos hlt]
    simp only [positionAccruedFee, hlt, if_true]
    apply ExecStmt.iteTrue ((evalPositionAccrualCond hm hl).trans (by rw [decide_eq_true hlt]))
    apply ExecBlock.consNormal (callMulDivDown hc
      (evalPositionAccrualArgs hm hp hl ht hsub (Nat.le_of_lt hlt)) hprod hnz (name := "accrued"))
    apply ExecBlock.consNormal (execLocalAssign (old := .int 0) ?_ ?_) ExecBlock.nil
    · change (wordLocal frame "accrued" _).locals.get? "fee" = some (.int 0)
      rw [wordLocal_get_ne _ _ _ _ (by decide)]
      exact hz
    · exact evalCast128 (evalWordLocal (wordLocal_get _ _ _))
  · rw [positionAccrualFrame, if_neg hlt]
    exact ExecStmt.iteFalse
      ((evalPositionAccrualCond hm hl).trans (by rw [decide_eq_false hlt])) ExecBlock.nil

theorem positionAccrualSourceRevert {frame : Frame} {evm : EVM.State} {m : MarketData}
    {pending last time : UInt256} (hc : frame.contract = contract)
    (hm : frame.locals.get? "market" = some (Model.marketValue m.value))
    (hp : frame.locals.get? "postSlashPendingFee" = some (.int pending.toNat))
    (hl : frame.locals.get? "_lastAccrual" = some (.int last.toNat))
    (ht : frame.locals.get? "accrualEnd" = some (.int (wordMin time m.maturity).toNat))
    (hbad : ¬ PositionAccrualSafe pending last m.maturity time) :
    ExecStmt config frame evm (positionViewFunction.body[11]!) .reverted := by
  have hlt : last.toNat < m.maturity.toNat := by
    by_contra hn
    exact hbad (fun h ↦ False.elim (hn h))
  apply ExecStmt.iteTrue ((evalPositionAccrualCond hm hl).trans (by rw [decide_eq_true hlt]))
  apply ExecBlock.consRevert
  by_cases hsub : last.toNat ≤ (wordMin time m.maturity).toNat
  · apply callMulDivDownRevert hc
      (evalPositionAccrualArgs hm hp hl ht hsub (Nat.le_of_lt hlt))
    exact fun h ↦ hbad (fun _ ↦ ⟨hsub, h.1⟩)
  · apply ExecStmt.internalCallArgsRevert
    have hsubEval := evalCheckedSubUnderflow (cfg := config) (evm := evm) ⟨256, by decide⟩
      (evalWordLocal ht) (evalWordLocal hl) (Nat.lt_of_not_ge hsub)
    simp only [evalExprs?, evalWordLocal hp, hsubEval, bind, EvalResult.bind]

end Benchmarks.Midnight
