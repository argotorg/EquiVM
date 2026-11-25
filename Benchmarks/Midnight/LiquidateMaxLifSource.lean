import Benchmarks.Midnight.LiquidateMaxLifTrace
import Benchmarks.Midnight.LiquidateAmountsGuard
import Benchmarks.Midnight.NamedCollateralSource
import Benchmarks.Midnight.MaxLifSource

variable {fork : Ethereum.Fork}

/-! Source lookup of the selected collateral and initialization of its liquidation incentive. -/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Midnight

set_option maxRecDepth 2000000

theorem evalSelectedCollateralLltv {cfg : Config} {frame : Frame} {evm : State}
    {m : MarketData} {index : UInt256}
    (hm : frame.locals.get? "market" = some (Model.marketValue m.value))
    (hi : frame.locals.get? "collateralIndex" = some (.int index.toNat))
    (hbound : index.toNat < m.collaterals.length) :
    evalExpr? cfg frame evm (.field (marketCollateralExpr "collateralIndex") "lltv") =
      .ok (.int m.collaterals[index.toNat].lltv.toNat) := by
  rw [evalExpr?, evalMarketCollateralAt "collateralIndex" hm hi hbound]
  rfl

theorem evalSelectedCollateralCursor {cfg : Config} {frame : Frame} {evm : State}
    {m : MarketData} {index : UInt256}
    (hm : frame.locals.get? "market" = some (Model.marketValue m.value))
    (hi : frame.locals.get? "collateralIndex" = some (.int index.toNat))
    (hbound : index.toNat < m.collaterals.length) :
    evalExpr? cfg frame evm (.field (marketCollateralExpr "collateralIndex") "liquidationCursor") =
      .ok (.int m.collaterals[index.toNat].liquidationCursor.toNat) := by
  rw [evalExpr?, evalMarketCollateralAt "collateralIndex" hm hi hbound]
  rfl

def liquidateMaxLifFrame (frame : Frame) (lltv cursor : UInt256) : Frame :=
  wordLocal (wordLocal (wordLocal frame "lltv" lltv) "_maxLif" (maxLif lltv cursor))
    "lif" (maxLif lltv cursor)

theorem liquidateMaxLifSource {frame : Frame} {evm : State} {m : MarketData} {index : UInt256}
    (hc : frame.contract = contract)
    (hm : frame.locals.get? "market" = some (Model.marketValue m.value))
    (hi : frame.locals.get? "collateralIndex" = some (.int index.toNat)) (rest : List Stmt) :
    (¬ LiquidateMaxLifSafe m index ∧
      ExecBlock fork config frame evm (liquidateAmountsBody.take 3 ++ rest) .reverted) ∨
    ∃ hbound : index.toNat < m.collaterals.length,
      let c := m.collaterals[index.toNat]
      MaxLifSafe c.lltv c.liquidationCursor ∧
        ABlock fork config evm frame (liquidateAmountsBody.take 3 ++ rest)
          (liquidateMaxLifFrame frame c.lltv c.liquidationCursor) rest := by
  by_cases hbound : index.toNat < m.collaterals.length
  · let c := m.collaterals[index.toNat]
    let f1 := wordLocal frame "lltv" c.lltv
    let f2 := wordLocal f1 "_maxLif" (maxLif c.lltv c.liquidationCursor)
    have hs0 : ExecStmt fork config frame evm (liquidateAmountsBody[0]!) (.ok f1 evm) :=
      ExecStmt.letDecl (evalSelectedCollateralLltv hm hi hbound)
    have hm1 : f1.locals.get? "market" = some (Model.marketValue m.value) := by
      simpa only [f1, wordLocal_get_ne _ _ _ _ (show "lltv" ≠ "market" by decide)] using hm
    have hi1 : f1.locals.get? "collateralIndex" = some (.int index.toNat) := by
      simpa only [f1, wordLocal_get_ne _ _ _ _ (show "lltv" ≠ "collateralIndex" by decide)] using hi
    have hl1 : f1.locals.get? "lltv" = some (.int c.lltv.toNat) := wordLocal_get _ _ _
    have hargs : evalExprs? config f1 evm
        [.var "lltv", .field (marketCollateralExpr "collateralIndex") "liquidationCursor"] =
        .ok [.int c.lltv.toNat, .int c.liquidationCursor.toNat] := by
      simp only [evalExprs?, evalWordLocal hl1, evalSelectedCollateralCursor hm1 hi1 hbound,
        bind, pure, EvalResult.bind]
      rfl
    by_cases hsafe : MaxLifSafe c.lltv c.liquidationCursor
    · have hs1 : ExecStmt fork config f1 evm (liquidateAmountsBody[1]!) (.ok f2 evm) :=
        callMaxLif hc hargs hsafe
      have hl2 : f2.locals.get? "_maxLif" = some (.int (maxLif c.lltv c.liquidationCursor).toNat) :=
        wordLocal_get _ _ _
      have hs2 : ExecStmt fork config f2 evm (liquidateAmountsBody[2]!)
          (.ok (liquidateMaxLifFrame frame c.lltv c.liquidationCursor) evm) :=
        ExecStmt.letDecl (evalWordLocal hl2)
      exact Or.inr ⟨hbound, hsafe, ⟨fun h ↦ ExecBlock.consNormal hs0
        (ExecBlock.consNormal hs1 (ExecBlock.consNormal hs2 h))⟩⟩
    · exact Or.inl ⟨fun h ↦ hsafe h.2, ExecBlock.consNormal hs0
        (ExecBlock.consRevert (callMaxLifRevert hc hargs hsafe))⟩
  · refine Or.inl ⟨fun h ↦ hbound h.1, ExecBlock.consRevert (ExecStmt.letDeclRevert ?_)⟩
    change evalExpr? config frame evm
      (.field (marketCollateralExpr "collateralIndex") "lltv") = .revert
    rw [evalExpr?, evalMarketCollateralAtRevert "collateralIndex" hm hi hbound]
    rfl

end Benchmarks.Midnight
