import Benchmarks.Midnight.LiquidateBadDebtSource
import Benchmarks.Midnight.LiquidateLossArithmetic
import Benchmarks.Midnight.MarketLossStorage
import Benchmarks.Midnight.MulDivCall
import Benchmarks.Midnight.ToUint128Source

/-! Source reads and checked arithmetic preceding the loss-factor storage write. -/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Midnight

set_option maxRecDepth 2000000

def liquidateLossArgs : List Expr :=
  [.inRange (.uint ⟨256, by decide⟩)
    (.binary .sub (.intLit (2 ^ 128 - 1)) (.var "_lossFactor")),
   .inRange (.uint ⟨256, by decide⟩) (.binary .sub (.var "_totalUnits") (.var "badDebt")),
   .var "_totalUnits"]

def liquidateLossFrame (frame : Frame) (total loss badDebt : UInt256) : Frame :=
  wordLocal (wordLocal (wordLocal (wordLocal frame "_totalUnits" total) "_lossFactor" loss)
    "__c12" (liquidateLossQuotient total loss badDebt))
    "__c13" (liquidateNextLoss total loss badDebt)

theorem liquidateLossSource {frame : Frame} {evm : State} {id badDebt : UInt256}
    (hc : frame.contract = contract)
    (hm : frame.locals.get? "_marketState" = some (.storageRef (marketStateRef id) marketStateType))
    (hd : frame.locals.get? "badDebt" = some (.int badDebt.toNat)) (rest : List Stmt) :
    let total := marketBalanceWord evm id 0
    let loss := marketLossWord evm id
    (¬ (badDebt.toNat ≤ total.toNat ∧ total ≠ ⟨0⟩) ∧
      ExecBlock config frame evm ((liquidateBadDebtBody.drop 1).take 4 ++ rest) .reverted) ∨
    (badDebt.toNat ≤ total.toNat ∧ total ≠ ⟨0⟩ ∧
      ABlock config evm frame ((liquidateBadDebtBody.drop 1).take 4 ++ rest)
        (liquidateLossFrame frame total loss badDebt) rest) := by
  dsimp only
  let total := marketBalanceWord evm id 0
  let loss := marketLossWord evm id
  let f0 := wordLocal frame "_totalUnits" total
  let f1 := wordLocal f0 "_lossFactor" loss
  let f2 := wordLocal f1 "__c12" (liquidateLossQuotient total loss badDebt)
  have ht : total.toNat < 2 ^ 128 := marketBalanceWord_lt evm id 0
  have hl : loss.toNat < 2 ^ 128 := shiftRight128_lt _
  have hs0 : ExecStmt config frame evm (liquidateBadDebtBody[1]!) (.ok f0 evm) :=
    ExecStmt.letDecl (evalMarketBalance 0 hm)
  have hm0 : f0.locals.get? "_marketState" =
      some (.storageRef (marketStateRef id) marketStateType) := by
    simpa only [f0, wordLocal_get_ne _ _ _ _ (show "_totalUnits" ≠ "_marketState" by decide)] using hm
  have hs1 : ExecStmt config f0 evm (liquidateBadDebtBody[2]!) (.ok f1 evm) :=
    ExecStmt.letDecl (evalMarketAliasLoss hm0)
  have ht1 : f1.locals.get? "_totalUnits" = some (.int total.toNat) := by
    rw [wordLocal_get_ne _ _ _ _ (show "_lossFactor" ≠ "_totalUnits" by decide)]
    exact wordLocal_get _ _ _
  have hl1 : f1.locals.get? "_lossFactor" = some (.int loss.toNat) := wordLocal_get _ _ _
  have hd1 : f1.locals.get? "badDebt" = some (.int badDebt.toNat) := by
    simpa only [f1, f0, wordLocal_get_ne _ _ _ _ (show "_lossFactor" ≠ "badDebt" by decide),
      wordLocal_get_ne _ _ _ _ (show "_totalUnits" ≠ "badDebt" by decide)] using hd
  have hleft := evalComplement128As256 (cfg := config) (evm := evm) (evalWordLocal hl1) hl
  by_cases hle : badDebt.toNat ≤ total.toNat
  · have hsub := evalExpr_uint256_sub (cfg := config) (evm := evm)
      (evalWordLocal ht1) (evalWordLocal hd1) hle
    have hargs : evalExprs? config f1 evm liquidateLossArgs =
        .ok [.int (complement128 loss).toNat, .int (UInt256.sub total badDebt).toNat,
          .int total.toNat] := by
      simp only [liquidateLossArgs, evalExprs?, hleft, hsub, evalWordLocal ht1,
        bind, EvalResult.bind, pure, uint256Value, Int.ofNat_eq_natCast]
    by_cases hnz : total ≠ ⟨0⟩
    · have hs2 : ExecStmt config f1 evm (liquidateBadDebtBody[3]!) (.ok f2 evm) :=
        callMulDivDown hc hargs (liquidateLossProduct_lt ht hl hle) hnz
      have hc12 : f2.locals.get? "__c12" =
          some (.int (liquidateLossQuotient total loss badDebt).toNat) := wordLocal_get _ _ _
      have he := evalComplement128As256 (cfg := config) (evm := evm)
        (evalWordLocal hc12)
        (liquidateLossQuotient_lt ht hl hle)
      have ha : evalExprs? config f2 evm
          [.inRange (.uint ⟨256, by decide⟩)
            (.binary .sub (.intLit (2 ^ 128 - 1)) (.var "__c12"))] =
          .ok [.int (liquidateNextLoss total loss badDebt).toNat] := by
        simp only [evalExprs?, he, bind, EvalResult.bind, pure]
        rfl
      have hs3 : ExecStmt config f2 evm (liquidateBadDebtBody[4]!)
          (.ok (liquidateLossFrame frame total loss badDebt) evm) :=
        callToUint128 hc ha (liquidateNextLoss_lt ht hl hle)
      exact Or.inr ⟨hle, hnz, ⟨fun h ↦ ExecBlock.consNormal hs0
        (ExecBlock.consNormal hs1 (ExecBlock.consNormal hs2 (ExecBlock.consNormal hs3 h)))⟩⟩
    · exact Or.inl ⟨fun h ↦ hnz h.2, ExecBlock.consNormal hs0
        (ExecBlock.consNormal hs1 (ExecBlock.consRevert
          (callMulDivDownRevert hc hargs (fun h ↦ hnz h.2))))⟩
  · have hsub := evalCheckedSubUnderflow (cfg := config) (evm := evm) ⟨256, by decide⟩
      (evalWordLocal ht1) (evalWordLocal hd1) (Nat.lt_of_not_ge hle)
    have hs2 : ExecStmt config f1 evm (liquidateBadDebtBody[3]!) .reverted := by
      apply ExecStmt.internalCallArgsRevert
      change evalExprs? config f1 evm liquidateLossArgs = .revert
      simp only [liquidateLossArgs, evalExprs?, hleft, hsub, bind, EvalResult.bind]
    exact Or.inl ⟨fun h ↦ hle h.1,
      ExecBlock.consNormal hs0 (ExecBlock.consNormal hs1 (ExecBlock.consRevert hs2))⟩

end Benchmarks.Midnight
