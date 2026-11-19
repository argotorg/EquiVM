import Benchmarks.Midnight.LiquidateGrowth
import Benchmarks.Midnight.LiquidateMaxLifSource

/-! Source evaluation of the checked post-maturity incentive expression. -/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Midnight

def liquidateGrowthExcessExpr : Expr :=
  .inRange (.uint ⟨256, by decide⟩)
    (.binary .sub (.var "_maxLif") (.intLit 1000000000000000000))

def liquidateGrowthElapsedExpr : Expr :=
  .inRange (.uint ⟨256, by decide⟩)
    (.binary .sub (.env .timestamp) (.field (.var "market") "maturity"))

def liquidateGrowthProductExpr : Expr :=
  .inRange (.uint ⟨256, by decide⟩)
    (.binary .mul liquidateGrowthExcessExpr liquidateGrowthElapsedExpr)

def liquidateGrowthExpr : Expr :=
  .inRange (.uint ⟨256, by decide⟩) (.binary .add (.intLit 1000000000000000000)
    (.binary .div liquidateGrowthProductExpr (.intLit 3600)))

-- LIBRARY CANDIDATE: the source timestamp is the EVM's uint256 timestamp word.
theorem evalWordTimestamp {cfg : Config} {frame : Frame} {evm : State} :
    evalExpr? cfg frame evm (.env .timestamp) =
      .ok (.int (UInt256.ofNat evm.executionEnv.header.timestamp).toNat) := by
  simp only [evalExpr?, envValue, pure, Int.ofNat_eq_natCast]

theorem evalLiquidateGrowth {cfg : Config} {frame : Frame} {evm : State}
    {m : MarketData} {maximum : UInt256}
    (hm : frame.locals.get? "market" = some (Model.marketValue m.value))
    (hx : frame.locals.get? "_maxLif" = some (.int maximum.toNat))
    (hsafe : LiquidateGrowthSafe maximum (UInt256.ofNat evm.executionEnv.header.timestamp)
      m.maturity) :
    evalExpr? cfg frame evm liquidateGrowthExpr = .ok (.int
      (liquidateGrowth maximum (UInt256.ofNat evm.executionEnv.header.timestamp) m.maturity).toNat) := by
  apply checkedAddSourceOk evalLifScale
    (divSourceOk (evalExpr_uint256_mul
      (evalExpr_uint256_sub (evalWordLocal hx) evalLifScale hsafe.1)
      (evalExpr_uint256_sub evalWordTimestamp (evalMarketMaturity hm) hsafe.2.1) hsafe.2.2)
      (show evalExpr? cfg frame evm (.intLit 3600) = .ok (.int (⟨3600⟩ : UInt256).toNat) by
        simp only [evalExpr?, pure]; rfl)
      (by decide))
    (liquidateGrowth_add_fit _)

theorem evalLiquidateGrowthRevert {cfg : Config} {frame : Frame} {evm : State}
    {m : MarketData} {maximum : UInt256}
    (hm : frame.locals.get? "market" = some (Model.marketValue m.value))
    (hx : frame.locals.get? "_maxLif" = some (.int maximum.toNat))
    (hbad : ¬ LiquidateGrowthSafe maximum (UInt256.ofNat evm.executionEnv.header.timestamp)
      m.maturity) :
    evalExpr? cfg frame evm liquidateGrowthExpr = .revert := by
  let timestamp := UInt256.ofNat evm.executionEnv.header.timestamp
  have hp : evalExpr? cfg frame evm liquidateGrowthProductExpr = .revert := by
    by_cases hxfit : lifScale.toNat ≤ maximum.toNat
    · have he : evalExpr? cfg frame evm liquidateGrowthExcessExpr =
          .ok (.int (UInt256.sub maximum lifScale).toNat) :=
        evalExpr_uint256_sub (evalWordLocal hx) evalLifScale hxfit
      by_cases htfit : m.maturity.toNat ≤ timestamp.toNat
      · exact evalExpr_uint256_mul_overflow he
          (evalExpr_uint256_sub evalWordTimestamp (evalMarketMaturity hm) htfit)
          (Nat.le_of_not_gt (fun h ↦ hbad ⟨hxfit, htfit, h⟩))
      · have ht : evalExpr? cfg frame evm liquidateGrowthElapsedExpr = .revert :=
          evalCheckedSubUnderflow ⟨256, by decide⟩ evalWordTimestamp (evalMarketMaturity hm)
            (Nat.lt_of_not_ge htfit)
        rw [liquidateGrowthProductExpr, evalExpr?,
          evalExpr_binary_nonshort (by decide) (by decide), he]
        simp only [bind, EvalResult.bind, ht]
    · have he : evalExpr? cfg frame evm liquidateGrowthExcessExpr = .revert :=
        evalCheckedSubUnderflow ⟨256, by decide⟩ (evalWordLocal hx) evalLifScale
          (Nat.lt_of_not_ge hxfit)
      rw [liquidateGrowthProductExpr, evalExpr?,
        evalExpr_binary_nonshort (by decide) (by decide), he]
      rfl
  rw [liquidateGrowthExpr, evalExpr?, evalExpr_binary_nonshort (by decide) (by decide),
    evalLifScale]
  simp only [bind, EvalResult.bind]
  rw [evalExpr_binary_nonshort (by decide) (by decide), hp]
  rfl

def liquidateGrownFrame (frame : Frame) (grown : UInt256) : Frame :=
  wordLocal (wordLocal frame "grown" grown) "lif" grown

theorem liquidateGrowthSource {frame : Frame} {evm : State} {m : MarketData}
    {maximum oldLif : UInt256} (hc : frame.contract = contract)
    (hm : frame.locals.get? "market" = some (Model.marketValue m.value))
    (hx : frame.locals.get? "_maxLif" = some (.int maximum.toNat))
    (hl : frame.locals.get? "lif" = some (.int oldLif.toNat)) :
    let timestamp := UInt256.ofNat evm.executionEnv.header.timestamp
    let body := [.internalCall "UtilsLib_min" [.var "_maxLif", liquidateGrowthExpr] "grown",
      .assign .localVar { base := "lif" } (.var "grown")]
    (¬ LiquidateGrowthSafe maximum timestamp m.maturity ∧ ExecBlock config frame evm body .reverted) ∨
    (LiquidateGrowthSafe maximum timestamp m.maturity ∧ ExecBlock config frame evm body
      (.ok (liquidateGrownFrame frame (liquidateGrownLif maximum timestamp m.maturity)) evm)) := by
  dsimp only
  by_cases hsafe : LiquidateGrowthSafe maximum (UInt256.ofNat evm.executionEnv.header.timestamp)
      m.maturity
  · refine Or.inr ⟨hsafe, ?_⟩
    let grown := liquidateGrownLif maximum (UInt256.ofNat evm.executionEnv.header.timestamp) m.maturity
    have ha : evalExprs? config frame evm [.var "_maxLif", liquidateGrowthExpr] =
        .ok [.int maximum.toNat, .int
          (liquidateGrowth maximum (UInt256.ofNat evm.executionEnv.header.timestamp)
            m.maturity).toNat] := by
      simp only [evalExprs?, evalWordLocal hx, evalLiquidateGrowth hm hx hsafe,
        bind, pure, EvalResult.bind]
    have hs0 : ExecStmt config frame evm
        (.internalCall "UtilsLib_min" [.var "_maxLif", liquidateGrowthExpr] "grown")
        (.ok (wordLocal frame "grown" grown) evm) := callMin hc ha
    have hl1 : (wordLocal frame "grown" grown).locals.get? "lif" = some (.int oldLif.toNat) := by
      simpa only [wordLocal_get_ne _ _ _ _ (show "grown" ≠ "lif" by decide)] using hl
    exact ExecBlock.consNormal hs0 (ExecBlock.consNormal
      (execLocalAssign hl1 (evalWordLocal (wordLocal_get _ "grown" _))) ExecBlock.nil)
  · refine Or.inl ⟨hsafe, ExecBlock.consRevert (ExecStmt.internalCallArgsRevert ?_)⟩
    simp only [evalExprs?, evalWordLocal hx, evalLiquidateGrowthRevert hm hx hsafe,
      bind, pure, EvalResult.bind]

end Benchmarks.Midnight
