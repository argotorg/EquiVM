import Benchmarks.Midnight.PositionViewSourceFrames

/-! Complete source execution of the internal position-view function. -/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Midnight

set_option maxRecDepth 2000000
set_option maxHeartbeats 1000000

attribute [local simp] wordLocal_get wordLocal_get_ne slashCreditFrame_get
  slashCreditFrame_contract slashPendingFrame_get slashPendingFrame_contract
  positionAccrualFrame_get positionAccrualFrame_contract

def PositionViewSourceSafe (evm : EVM.State) (m : MarketData) (id user : UInt256) : Prop :=
  PositionViewSafe (positionFieldWord evm id user 0) (positionFieldWord evm id user 1)
    (positionFieldWord evm id user 2) (marketLossWord evm id) (positionFieldWord evm id user 3)
    m.maturity (UInt256.ofNat evm.executionEnv.header.timestamp)

instance (evm : EVM.State) (m : MarketData) (id user : UInt256) :
    Decidable (PositionViewSourceSafe evm m id user) := inferInstanceAs (Decidable (PositionViewSafe ..))

theorem positionViewAccrualStart_market (evm : EVM.State) (imms : Store) (m : MarketData)
    (id user : UInt256) :
    (positionViewAccrualStartFrame evm imms m id user).locals.get? "market" =
      some (Model.marketValue m.value) := by
  simp [-Std.HashMap.get?_eq_getElem?, positionViewAccrualStartFrame,
    positionViewPendingDoneFrame, positionViewPendingFrame, positionViewCreditFrame,
    positionViewAliasFrame, positionViewArguments]
  simp [Std.HashMap.getElem_insert]

theorem positionViewAccrualStart_credit (evm : EVM.State) (imms : Store) (m : MarketData)
    (id user : UInt256) :
    (positionViewAccrualStartFrame evm imms m id user).locals.get? "postSlashCredit" =
      some (.int (positionPostCredit evm id user).toNat) := by
  simp [-Std.HashMap.get?_eq_getElem?, positionViewAccrualStartFrame, positionViewPendingDoneFrame,
    positionViewPendingFrame_postCredit]

theorem positionViewAccrualStart_pending (evm : EVM.State) (imms : Store) (m : MarketData)
    (id user : UInt256) :
    (positionViewAccrualStartFrame evm imms m id user).locals.get? "postSlashPendingFee" =
      some (.int (positionPostPending evm id user).toNat) := by
  simp [-Std.HashMap.get?_eq_getElem?, positionViewAccrualStartFrame]
  exact slashPendingFrame_value _ _ _ (wordLocal_get _ _ _)

theorem positionViewAccrualStep (evm : EVM.State) (imms : Store) (m : MarketData) (id user : UInt256)
    (hsafe : PositionAccrualSafe (positionPostPending evm id user) (positionFieldWord evm id user 3)
      m.maturity (UInt256.ofNat evm.executionEnv.header.timestamp)) :
    ExecStmt config (positionViewAccrualStartFrame evm imms m id user) evm
      (positionViewFunction.body[11]!) (.ok (positionViewResultFrame evm imms m id user) evm) := by
  apply positionAccrualSource
    (by simp [positionViewAccrualStartFrame, positionViewPendingDoneFrame, positionViewPendingFrame,
      wordLocal, positionViewCreditFrame, positionViewAliasFrame, positionViewCallFrame])
    (positionViewAccrualStart_market evm imms m id user)
    (positionViewAccrualStart_pending evm imms m id user) _ _ (wordLocal_get _ _ _) hsafe
  · simp [-Std.HashMap.get?_eq_getElem?, positionViewAccrualStartFrame]
  · simp [-Std.HashMap.get?_eq_getElem?, positionViewAccrualStartFrame]

theorem positionViewAccrualStepRevert (evm : EVM.State) (imms : Store) (m : MarketData) (id user : UInt256)
    (hbad : ¬ PositionAccrualSafe (positionPostPending evm id user) (positionFieldWord evm id user 3)
      m.maturity (UInt256.ofNat evm.executionEnv.header.timestamp)) :
    ExecStmt config (positionViewAccrualStartFrame evm imms m id user) evm
      (positionViewFunction.body[11]!) .reverted := by
  apply positionAccrualSourceRevert
    (by simp [positionViewAccrualStartFrame, positionViewPendingDoneFrame, positionViewPendingFrame,
      wordLocal, positionViewCreditFrame, positionViewAliasFrame, positionViewCallFrame])
    (positionViewAccrualStart_market evm imms m id user)
    (positionViewAccrualStart_pending evm imms m id user) _ _ hbad
  · simp [-Std.HashMap.get?_eq_getElem?, positionViewAccrualStartFrame]
  · simp [-Std.HashMap.get?_eq_getElem?, positionViewAccrualStartFrame]

theorem positionViewResult_credit (evm : EVM.State) (imms : Store) (m : MarketData) (id user : UInt256) :
    (positionViewResultFrame evm imms m id user).locals.get? "postSlashCredit" =
      some (.int (positionPostCredit evm id user).toNat) := by
  simp [-Std.HashMap.get?_eq_getElem?, positionViewResultFrame, positionViewAccrualStart_credit]

theorem positionViewResult_pending (evm : EVM.State) (imms : Store) (m : MarketData) (id user : UInt256) :
    (positionViewResultFrame evm imms m id user).locals.get? "postSlashPendingFee" =
      some (.int (positionPostPending evm id user).toNat) := by
  simp [-Std.HashMap.get?_eq_getElem?, positionViewResultFrame, positionViewAccrualStart_pending]

theorem positionViewResult_fee (evm : EVM.State) (imms : Store) (m : MarketData) (id user : UInt256) :
    (positionViewResultFrame evm imms m id user).locals.get? "fee" =
      some (.int (positionViewFee evm m id user).toNat) :=
  positionAccrualFrame_value _ _ _ _ (wordLocal_get _ _ _)

theorem positionViewInternalReturns (evm : EVM.State) (imms : Store) (m : MarketData) (id user : UInt256)
    (hcanon : user.toNat < EVM.addressModulus) (hsafe : PositionViewSourceSafe evm m id user) :
    ExecFuncBody config (positionViewCallFrame imms m id user) evm positionViewFunction.body
      (.returned (positionViewResultFrame evm imms m id user) evm
        (some (positionViewReturnValues (positionPostCredit evm id user) (positionPostPending evm id user)
          (positionViewFee evm m id user)))) := by
  apply ExecFuncBody.execBlockRet
  apply (sourceNormalStep (positionViewAccrualPrefix evm imms m id user hcanon hsafe.1)
    (positionViewAccrualStep evm imms m id user hsafe.2.1)).run
  exact positionViewReturnSource (positionViewResult_credit evm imms m id user)
    (positionViewResult_pending evm imms m id user) (positionViewResult_fee evm imms m id user)
    hsafe.2.2.1 hsafe.2.2.2

theorem positionViewInternalReverts (evm : EVM.State) (imms : Store) (m : MarketData) (id user : UInt256)
    (hcanon : user.toNat < EVM.addressModulus) (hbad : ¬ PositionViewSourceSafe evm m id user) :
    ExecFuncBody config (positionViewCallFrame imms m id user) evm positionViewFunction.body .reverted := by
  apply ExecFuncBody.execBlockRevert
  by_cases hp : SlashPendingSafe (positionFieldWord evm id user 0) (positionFieldWord evm id user 1)
      (positionPostCredit evm id user)
  · have hprefix := positionViewAccrualPrefix evm imms m id user hcanon hp
    by_cases ha : PositionAccrualSafe (positionPostPending evm id user) (positionFieldWord evm id user 3)
        m.maturity (UInt256.ofNat evm.executionEnv.header.timestamp)
    · apply (sourceNormalStep hprefix (positionViewAccrualStep evm imms m id user ha)).run
      apply positionViewReturnSourceRevert (positionViewResult_credit evm imms m id user)
        (positionViewResult_pending evm imms m id user) (positionViewResult_fee evm imms m id user)
      exact fun h ↦ hbad ⟨hp, ha, h⟩
    · exact hprefix.run (ExecBlock.consRevert (positionViewAccrualStepRevert evm imms m id user ha))
  · apply (positionViewPendingPrefix evm imms m id user hcanon).run
    apply ExecBlock.consRevert
    apply slashPendingSourceRevert
      (by simp [positionViewPendingFrame, wordLocal, positionViewCreditFrame,
        positionViewAliasFrame, positionViewCallFrame])
      _ _ (positionViewPendingFrame_postCredit evm imms m id user) hp
    · simp [-Std.HashMap.get?_eq_getElem?, positionViewPendingFrame, positionViewCreditFrame]
    · simp [-Std.HashMap.get?_eq_getElem?, positionViewPendingFrame]

end Benchmarks.Midnight
