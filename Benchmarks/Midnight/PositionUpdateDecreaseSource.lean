import Benchmarks.Midnight.PositionUpdateSourceFrames

/-! Source proofs for the two checked position-balance decreases. -/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Midnight

theorem positionUpdateValues_alias (evm : EVM.State) (imms : Store) (m : MarketData) (id user : UInt256) :
    (positionUpdateValuesFrame evm imms m id user).locals.get? "_position" =
      some (.storageRef (positionRef id user) positionType) := by
  simp [positionUpdateValuesFrame, wordLocal, positionUpdateTupleFrame, resumeAfterInternalCall,
    positionViewAliasFrame, Std.HashMap.getElem_insert]

theorem positionUpdateValues_credit (evm : EVM.State) (imms : Store) (m : MarketData) (id user : UInt256) :
    (positionUpdateValuesFrame evm imms m id user).locals.get? "newCredit" =
      some (.int (positionNewCredit evm m id user).toNat) := by
  simp [positionUpdateValuesFrame, wordLocal, Std.HashMap.getElem_insert]

theorem positionUpdateCredit_alias (evm : EVM.State) (imms : Store) (m : MarketData) (id user : UInt256) :
    (positionUpdateCreditFrame evm imms m id user).locals.get? "_position" =
      some (.storageRef (positionRef id user) positionType) := by
  rw [positionUpdateCreditFrame, wordLocal_get_ne _ _ _ _ (by decide)]
  exact positionUpdateValues_alias ..

theorem positionUpdateCredit_pending (evm : EVM.State) (imms : Store) (m : MarketData) (id user : UInt256) :
    (positionUpdateCreditFrame evm imms m id user).locals.get? "newPendingFee" =
      some (.int (positionNewPending evm m id user).toNat) := by
  simp [positionUpdateCreditFrame, positionUpdateValuesFrame, wordLocal, Std.HashMap.getElem_insert]

theorem positionUpdateCreditPrefix (evm : EVM.State) (imms : Store) (m : MarketData) (id user : UInt256)
    (hcanon : user.toNat < EVM.addressModulus) (hsafe : PositionViewSourceSafe evm m id user)
    (hc : (positionNewCredit evm m id user).toNat ≤ (positionFieldWord evm id user 0).toNat) :
    ABlock config evm (positionViewCallFrame imms m id user) positionUpdateFunction.body
      (positionUpdateCreditFrame evm imms m id user) (positionUpdateFunction.body.drop 6) := by
  apply (positionUpdateValuesPrefix evm imms m id user hcanon hsafe).letStep
  exact evalCheckedSub128 (evalPositionAliasField 0 hcanon (positionUpdateValues_alias ..))
    (evalWordLocal (positionUpdateValues_credit ..)) (positionFieldWord_lt ..) hc

theorem positionUpdateWritesPrefix (evm : EVM.State) (imms : Store) (m : MarketData) (id user : UInt256)
    (hcanon : user.toNat < EVM.addressModulus) (hsafe : PositionViewSourceSafe evm m id user)
    (hc : (positionNewCredit evm m id user).toNat ≤ (positionFieldWord evm id user 0).toNat)
    (hp : (positionNewPending evm m id user).toNat ≤ (positionFieldWord evm id user 1).toNat) :
    ABlock config evm (positionViewCallFrame imms m id user) positionUpdateFunction.body
      (positionUpdateWritesFrame evm imms m id user) (positionUpdateFunction.body.drop 7) := by
  apply (positionUpdateCreditPrefix evm imms m id user hcanon hsafe hc).letStep
  exact evalCheckedSub128 (evalPositionAliasField 1 hcanon (positionUpdateCredit_alias ..))
    (evalWordLocal (positionUpdateCredit_pending ..)) (positionFieldWord_lt ..) hp

theorem positionUpdateDecreaseReverts (evm : EVM.State) (imms : Store) (m : MarketData) (id user : UInt256)
    (hcanon : user.toNat < EVM.addressModulus) (hsafe : PositionViewSourceSafe evm m id user)
    (hbad : ¬ ((positionNewCredit evm m id user).toNat ≤ (positionFieldWord evm id user 0).toNat ∧
      (positionNewPending evm m id user).toNat ≤ (positionFieldWord evm id user 1).toNat)) :
    ExecFuncBody config (positionViewCallFrame imms m id user) evm positionUpdateFunction.body .reverted := by
  apply ExecFuncBody.execBlockRevert
  by_cases hc : (positionNewCredit evm m id user).toNat ≤ (positionFieldWord evm id user 0).toNat
  · apply (positionUpdateCreditPrefix evm imms m id user hcanon hsafe hc).run
    apply ExecBlock.consRevert (ExecStmt.letDeclRevert _)
    exact evalCheckedSubUnderflow ⟨128, by decide⟩
      (evalPositionAliasField 1 hcanon (positionUpdateCredit_alias ..))
      (evalWordLocal (positionUpdateCredit_pending ..)) (Nat.lt_of_not_ge (fun hp ↦ hbad ⟨hc, hp⟩))
  · apply (positionUpdateValuesPrefix evm imms m id user hcanon hsafe).run
    apply ExecBlock.consRevert (ExecStmt.letDeclRevert _)
    exact evalCheckedSubUnderflow ⟨128, by decide⟩
      (evalPositionAliasField 0 hcanon (positionUpdateValues_alias ..))
      (evalWordLocal (positionUpdateValues_credit ..)) (Nat.lt_of_not_ge hc)

end Benchmarks.Midnight
