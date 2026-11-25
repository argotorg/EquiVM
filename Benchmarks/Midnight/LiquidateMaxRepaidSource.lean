import Benchmarks.Midnight.LiquidateMaxRepaid
import Benchmarks.Midnight.LiquidateMaxLifSource

variable {fork : Ethereum.Fork}

/-! Source execution of the maximum-repayment calculation and every arithmetic failure. -/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Midnight

set_option maxRecDepth 10000

def liquidateRcfBody : List Stmt :=
  match liquidateAmountsBody[5]! with
  | .ite _ body _ => body
  | _ => []

def liquidateShortfallExpr : Expr :=
  .inRange (.uint ⟨256, by decide⟩) (.binary .sub
    (.storage { base := "_position", steps := [.field "debt"] }) (.var "maxDebt"))

def liquidateSquaredScaleExpr : Expr :=
  .inRange (.uint ⟨256, by decide⟩)
    (.binary .mul (.intLit 1000000000000000000) (.intLit 1000000000000000000))

def liquidateLifLltvExpr : Expr :=
  .inRange (.uint ⟨256, by decide⟩) (.binary .mul (.var "lif") (.var "lltv"))

def liquidateRcfDenominatorExpr : Expr :=
  .inRange (.uint ⟨256, by decide⟩)
    (.binary .sub liquidateSquaredScaleExpr liquidateLifLltvExpr)

theorem evalLiquidateSquaredScale {cfg : Config} {frame : Frame} {evm : State} :
    evalExpr? cfg frame evm liquidateSquaredScaleExpr = .ok (.int liquidatePriceScale.toNat) := by
  simpa only [lifScale_squared] using
    (evalExpr_uint256_mul (cfg := cfg) (caller := frame) (evm := evm)
      evalLifScale evalLifScale (by decide))

theorem liquidateMaxRepaidSource {frame : Frame} {evm : State} {id borrower maxDebt lif lltv : UInt256}
    (hc : frame.contract = contract) (hcanon : borrower.toNat < EVM.addressModulus)
    (hp : frame.locals.get? "_position" = some (.storageRef (positionRef id borrower) positionType))
    (hm : frame.locals.get? "maxDebt" = some (.int maxDebt.toNat))
    (hl : frame.locals.get? "lif" = some (.int lif.toNat))
    (hll : frame.locals.get? "lltv" = some (.int lltv.toNat)) :
    let debt := low128 (healthPositionWord evm id borrower)
    (¬ LiquidateMaxRepaidSafe debt maxDebt lif lltv ∧
      ExecStmt fork config frame evm (liquidateRcfBody[0]!) .reverted) ∨
    (LiquidateMaxRepaidSafe debt maxDebt lif lltv ∧
      ExecStmt fork config frame evm (liquidateRcfBody[0]!)
        (.ok (wordLocal frame "maxRepaid" (liquidateMaxRepaid debt maxDebt lif lltv)) evm)) := by
  dsimp only
  let debt := low128 (healthPositionWord evm id borrower)
  by_cases hd : maxDebt.toNat ≤ debt.toNat
  · have hshort : evalExpr? config frame evm liquidateShortfallExpr =
        .ok (.int (UInt256.sub debt maxDebt).toNat) :=
      evalExpr_uint256_sub (evalHealthDebt hcanon hp) (evalWordLocal hm) hd
    by_cases hmul : lif.toNat * lltv.toNat < UInt256.size
    · have hprod : evalExpr? config frame evm liquidateLifLltvExpr =
          .ok (.int (UInt256.mul lif lltv).toNat) :=
        evalExpr_uint256_mul (evalWordLocal hl) (evalWordLocal hll) hmul
      by_cases hle : (UInt256.mul lif lltv).toNat ≤ liquidatePriceScale.toNat
      · have hden : evalExpr? config frame evm liquidateRcfDenominatorExpr =
            .ok (.int (liquidateRcfDenominator lif lltv).toNat) :=
          evalExpr_uint256_sub evalLiquidateSquaredScale hprod hle
        have hargs : evalExprs? config frame evm
            [liquidateShortfallExpr, liquidateSquaredScaleExpr, liquidateRcfDenominatorExpr] =
            .ok [.int (UInt256.sub debt maxDebt).toNat, .int liquidatePriceScale.toNat,
              .int (liquidateRcfDenominator lif lltv).toNat] := by
          simp only [evalExprs?, hshort, evalLiquidateSquaredScale, hden, bind, pure, EvalResult.bind]
        by_cases hlt : (UInt256.mul lif lltv).toNat < liquidatePriceScale.toNat
        · exact Or.inr ⟨⟨hd, hmul, hlt⟩, callMulDivUp hc hargs
            (liquidateMaxRepaid_mulDivSafe (low128_lt _) hd hlt)⟩
        · have he : UInt256.mul lif lltv = liquidatePriceScale := u256_inj (by omega)
          have hz : liquidateRcfDenominator lif lltv = ⟨0⟩ := by
            rw [liquidateRcfDenominator, he, u256_sub_self]
          refine Or.inl ⟨fun h ↦ hlt h.2.2, callMulDivUpRevert hc hargs ?_⟩
          intro hs
          have hpos := hs.2.1
          rw [hz] at hpos
          exact Nat.lt_irrefl 0 hpos
      · have hden : evalExpr? config frame evm liquidateRcfDenominatorExpr = .revert :=
          evalCheckedSubUnderflow ⟨256, by decide⟩ evalLiquidateSquaredScale hprod
            (Nat.lt_of_not_ge hle)
        refine Or.inl ⟨fun h ↦ hle (Nat.le_of_lt h.2.2), ExecStmt.internalCallArgsRevert ?_⟩
        change evalExprs? config frame evm
          [liquidateShortfallExpr, liquidateSquaredScaleExpr, liquidateRcfDenominatorExpr] = .revert
        simp only [evalExprs?, hshort, evalLiquidateSquaredScale, hden, bind, pure, EvalResult.bind]
    · have hprod : evalExpr? config frame evm liquidateLifLltvExpr = .revert :=
        evalExpr_uint256_mul_overflow (evalWordLocal hl) (evalWordLocal hll) (Nat.le_of_not_gt hmul)
      have hden : evalExpr? config frame evm liquidateRcfDenominatorExpr = .revert := by
        rw [liquidateRcfDenominatorExpr, evalExpr?,
          evalExpr_binary_nonshort (by decide) (by decide), evalLiquidateSquaredScale]
        simp only [bind, EvalResult.bind, hprod]
      refine Or.inl ⟨fun h ↦ hmul h.2.1, ExecStmt.internalCallArgsRevert ?_⟩
      change evalExprs? config frame evm
        [liquidateShortfallExpr, liquidateSquaredScaleExpr, liquidateRcfDenominatorExpr] = .revert
      simp only [evalExprs?, hshort, evalLiquidateSquaredScale, hden, bind, pure, EvalResult.bind]
  · have hshort : evalExpr? config frame evm liquidateShortfallExpr = .revert :=
      evalCheckedSubUnderflow ⟨256, by decide⟩ (evalHealthDebt hcanon hp) (evalWordLocal hm)
        (Nat.lt_of_not_ge hd)
    refine Or.inl ⟨fun h ↦ hd h.1, ExecStmt.internalCallArgsRevert ?_⟩
    change evalExprs? config frame evm
      [liquidateShortfallExpr, liquidateSquaredScaleExpr, liquidateRcfDenominatorExpr] = .revert
    simp only [evalExprs?, hshort, bind, EvalResult.bind]

end Benchmarks.Midnight
