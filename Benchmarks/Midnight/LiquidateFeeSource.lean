import Benchmarks.Midnight.LiquidateTotalSource
import Benchmarks.Midnight.LiquidateFeeArithmetic

/-! The source branch that calculates and converts the remaining continuous fees. -/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Midnight

set_option maxRecDepth 2000000

def liquidateFeeInner : List Stmt :=
  match liquidateBadDebtBody[9]! with
  | .ite _ body _ => body
  | _ => []

def liquidateFeeInnerFrame (frame : Frame) (amount : UInt256) : Frame :=
  wordLocal (wordLocal (wordLocal frame "amount" amount) "checkedAmount" amount) "remainingFees" amount

def liquidateFeeArgs : List Expr :=
  [.storage { base := "_marketState", steps := [.field "continuousFeeCredit"] },
   .inRange packedUInt128Int (.binary .sub (.intLit (2 ^ 128 - 1))
     (.storage { base := "_marketState", steps := [.field "lossFactor"] })),
   .inRange (.uint ⟨256, by decide⟩) (.binary .sub (.intLit (2 ^ 128 - 1)) (.var "_lossFactor"))]

theorem liquidateFeeInnerSource {frame : Frame} {evm : State} {id oldLoss : UInt256}
    (hc : frame.contract = contract)
    (hm : frame.locals.get? "_marketState" = some (.storageRef (marketStateRef id) marketStateType))
    (hl : frame.locals.get? "_lossFactor" = some (.int oldLoss.toNat))
    (hr : frame.locals.get? "remainingFees" = some (.int (⟨0⟩ : UInt256).toNat))
    (ho : oldLoss.toNat < 2 ^ 128 - 1) :
    let remaining := liquidateRemainingFees (marketBalanceWord evm id 2) oldLoss (marketLossWord evm id)
    (2 ^ 128 ≤ remaining.toNat ∧ ExecBlock config frame evm liquidateFeeInner .reverted) ∨
    (remaining.toNat < 2 ^ 128 ∧ ExecBlock config frame evm liquidateFeeInner
      (.ok (liquidateFeeInnerFrame frame remaining) evm)) := by
  dsimp only
  let fee := marketBalanceWord evm id 2
  let loss := marketLossWord evm id
  let remaining := liquidateRemainingFees fee oldLoss loss
  let f1 := wordLocal frame "amount" remaining
  let f2 := wordLocal f1 "checkedAmount" remaining
  have he1 := evalMarketBalance (evm := evm) 2 hm
  change evalExpr? config frame evm
    (.storage { base := "_marketState", steps := [.field "continuousFeeCredit"] }) =
      .ok (.int fee.toNat) at he1
  have he2 := evalComplement128 (evalMarketAliasLoss (evm := evm) hm) (shiftRight128_lt _)
  have he3 := evalComplement128As256 (cfg := config) (evm := evm) (evalWordLocal hl) (by omega)
  have he : evalExprs? config frame evm liquidateFeeArgs =
      .ok [.int fee.toNat, .int (complement128 loss).toNat, .int (complement128 oldLoss).toNat] := by
    simp only [liquidateFeeArgs, evalExprs?, he1, he2, he3, bind, pure, EvalResult.bind]
    rfl
  have hnz : complement128 oldLoss ≠ ⟨0⟩ := by
    intro hz
    have hh := complement128_pos ho
    rw [hz] at hh
    contradiction
  have hs0 : ExecStmt config frame evm (liquidateFeeInner[0]!) (.ok f1 evm) :=
    callMulDivDown hc he (uint128_product_bound (marketBalanceWord_lt evm id 2)
      (complement128_lt (shiftRight128_lt _))) hnz
  have ha1 : f1.locals.get? "amount" = some (.int remaining.toNat) := wordLocal_get _ _ _
  have hargs : evalExprs? config f1 evm [.var "amount"] = .ok [.int remaining.toNat] := by
    simp only [evalExprs?, evalWordLocal ha1, bind, pure, EvalResult.bind]
  by_cases hfit : remaining.toNat < 2 ^ 128
  · have hs1 : ExecStmt config f1 evm (liquidateFeeInner[1]!) (.ok f2 evm) :=
      callToUint128 hc hargs hfit
    have hr2 : f2.locals.get? "remainingFees" = some (.int (⟨0⟩ : UInt256).toNat) := by
      simpa only [f2, f1,
        wordLocal_get_ne _ _ _ _ (show "checkedAmount" ≠ "remainingFees" by decide),
        wordLocal_get_ne _ _ _ _ (show "amount" ≠ "remainingFees" by decide)] using hr
    have hc2 : f2.locals.get? "checkedAmount" = some (.int remaining.toNat) := wordLocal_get _ _ _
    have hs2 : ExecStmt config f2 evm (liquidateFeeInner[2]!)
        (.ok (liquidateFeeInnerFrame frame remaining) evm) := execLocalAssign hr2 (evalWordLocal hc2)
    exact Or.inr ⟨hfit, ExecBlock.consNormal hs0
      (ExecBlock.consNormal hs1 (ExecBlock.consNormal hs2 ExecBlock.nil))⟩
  · exact Or.inl ⟨Nat.le_of_not_gt hfit,
      ExecBlock.consNormal hs0 (ExecBlock.consRevert (callToUint128Revert hc hargs (by omega)))⟩

end Benchmarks.Midnight
