import Benchmarks.Midnight.LiquidateLossSource

/-! Ordered loss-factor storage and checked total-unit subtraction at source level. -/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Midnight

set_option maxRecDepth 2000000

def liquidateLossState (evm : State) (id newLoss : UInt256) : State :=
  storeHigh128 evm (solcMappingSlot ⟨1⟩ id) newLoss

def liquidateTotalState (evm : State) (id newLoss badDebt : UInt256) : State :=
  let evm' := liquidateLossState evm id newLoss
  marketBalanceStore evm' id 0 (UInt256.sub (marketBalanceWord evm' id 0) badDebt)

theorem liquidateTotalSource {frame : Frame} {evm : State} {id newLoss badDebt : UInt256}
    (hc : frame.contract = contract)
    (hm : frame.locals.get? "_marketState" = some (.storageRef (marketStateRef id) marketStateType))
    (hl : frame.locals.get? "__c13" = some (.int newLoss.toNat))
    (hd : frame.locals.get? "badDebt" = some (.int badDebt.toNat))
    (hp : evm.executionEnv.perm = true) :
    let total := marketBalanceWord (liquidateLossState evm id newLoss) id 0
    (¬ (badDebt.toNat < 2 ^ 128 ∧ badDebt.toNat ≤ total.toNat) ∧
      ExecBlock config frame evm ((liquidateBadDebtBody.drop 5).take 3) .reverted) ∨
    (badDebt.toNat < 2 ^ 128 ∧ badDebt.toNat ≤ total.toNat ∧
      ExecBlock config frame evm ((liquidateBadDebtBody.drop 5).take 3)
        (.ok (wordLocal frame "__c14" badDebt) (liquidateTotalState evm id newLoss badDebt))) := by
  dsimp only
  let evm' := liquidateLossState evm id newLoss
  let total := marketBalanceWord evm' id 0
  let f := wordLocal frame "__c14" badDebt
  have hs0 : ExecStmt config frame evm (liquidateBadDebtBody[5]!) (.ok frame evm') :=
    ExecStmt.assign (Or.inr hp) (evalWordLocal hl) (assignMarketAliasLoss _ hm)
  have hp' : evm'.executionEnv.perm = true := by
    simpa only [evm', liquidateLossState, storeHigh128_env] using hp
  have he : evalExprs? config frame evm' [.var "badDebt"] = .ok [.int badDebt.toNat] := by
    simp only [evalExprs?, evalWordLocal hd, EvalResult.bind, bind, pure]
  by_cases hfit : badDebt.toNat < 2 ^ 128
  · have hs1 : ExecStmt config frame evm' (liquidateBadDebtBody[6]!) (.ok f evm') :=
      callToUint128 hc he hfit
    have hm' : f.locals.get? "_marketState" =
        some (.storageRef (marketStateRef id) marketStateType) := by
      simpa only [f, wordLocal_get_ne _ _ _ _ (show "__c14" ≠ "_marketState" by decide)] using hm
    have hd' : f.locals.get? "__c14" = some (.int badDebt.toNat) := wordLocal_get _ _ _
    by_cases hle : badDebt.toNat ≤ total.toNat
    · have hs2 : ExecStmt config f evm' (liquidateBadDebtBody[7]!)
          (.ok f (liquidateTotalState evm id newLoss badDebt)) :=
        ExecStmt.assign (Or.inr hp')
          (evalCheckedSub128 (evalMarketBalance 0 hm') (evalWordLocal hd')
            (marketBalanceWord_lt evm' id 0) hle) (assignMarketBalance 0 _ hm')
      exact Or.inr ⟨hfit, hle, ExecBlock.consNormal hs0
        (ExecBlock.consNormal hs1 (ExecBlock.consNormal hs2 ExecBlock.nil))⟩
    · exact Or.inl ⟨fun h ↦ hle h.2, ExecBlock.consNormal hs0
        (ExecBlock.consNormal hs1 (ExecBlock.consRevert (ExecStmt.assignExprRevert
          (evalCheckedSubUnderflow ⟨128, by decide⟩ (evalMarketBalance 0 hm')
            (evalWordLocal hd') (Nat.lt_of_not_ge hle)))))⟩
  · exact Or.inl ⟨fun h ↦ hfit h.1,
      ExecBlock.consNormal hs0 (ExecBlock.consRevert (callToUint128Revert hc he (by omega)))⟩

end Benchmarks.Midnight
