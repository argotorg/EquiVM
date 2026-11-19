import Benchmarks.Midnight.LiquidateRecoverableSource

/-! Saturating remainder and the final recovery-threshold requirement. -/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Midnight

theorem evalMarketRcfThreshold {cfg : Config} {frame : Frame} {evm : State} {m : MarketData}
    (hm : frame.locals.get? "market" = some (Model.marketValue m.value)) :
    evalExpr? cfg frame evm (.field (.var "market") "rcfThreshold") =
      .ok (.int m.rcfThreshold.toNat) := by
  simp only [evalExpr?, hm, EvalResult.ofOption, bind, EvalResult.bind]
  rfl

theorem liquidateThresholdSource {frame : Frame} {evm : State} {m : MarketData}
    {repayable cap : UInt256} (hc : frame.contract = contract)
    (hm : frame.locals.get? "market" = some (Model.marketValue m.value))
    (hp : frame.locals.get? "repayable" = some (.int repayable.toNat))
    (hr : frame.locals.get? "maxRepaid" = some (.int cap.toNat)) :
    let remainder := zeroFloorSubWord repayable cap
    (¬ remainder.toNat < m.rcfThreshold.toNat ∧
      ExecBlock config frame evm (liquidateThresholdBody.drop 2) .reverted) ∨
    (remainder.toNat < m.rcfThreshold.toNat ∧
      ExecBlock config frame evm (liquidateThresholdBody.drop 2)
        (.ok (wordLocal frame "remainder" remainder) evm)) := by
  dsimp only
  let remainder := zeroFloorSubWord repayable cap
  let f1 := wordLocal frame "remainder" remainder
  have ha : evalExprs? config frame evm [.var "repayable", .var "maxRepaid"] =
      .ok [.int repayable.toNat, .int cap.toNat] := by
    simp only [evalExprs?, evalWordLocal hp, evalWordLocal hr, bind, pure, EvalResult.bind]
  have hs0 : ExecStmt config frame evm (liquidateThresholdBody[2]!) (.ok f1 evm) :=
    callZeroFloorSub hc ha
  have hm1 : f1.locals.get? "market" = some (Model.marketValue m.value) := by
    simpa only [f1, wordLocal_get_ne _ _ _ _ (show "remainder" ≠ "market" by decide)] using hm
  have hr1 : f1.locals.get? "remainder" = some (.int remainder.toNat) := wordLocal_get _ _ _
  have he : evalExpr? config f1 evm
      (.binary .lt (.var "remainder") (.field (.var "market") "rcfThreshold")) =
      .ok (.bool (decide (remainder.toNat < m.rcfThreshold.toNat))) := by
    rw [evalExpr_binary_nonshort (by decide) (by decide), evalWordLocal hr1, evalMarketRcfThreshold hm1]
    simp only [bind, EvalResult.bind, evalBinaryOp?, Int.ofNat_lt]
  by_cases hlt : remainder.toNat < m.rcfThreshold.toNat
  · exact Or.inr ⟨hlt, ExecBlock.consNormal hs0
      (ExecBlock.consNormal (ExecStmt.requireTrue (he.trans (by rw [decide_eq_true hlt])))
        ExecBlock.nil)⟩
  · exact Or.inl ⟨hlt, ExecBlock.consNormal hs0
      (ExecBlock.consRevert (ExecStmt.requireFalse (he.trans (by rw [decide_eq_false hlt]))))⟩

end Benchmarks.Midnight
