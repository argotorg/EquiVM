import Benchmarks.Midnight.SlashCreditSource
import Benchmarks.Midnight.SlashPendingSource
import Benchmarks.Midnight.PositionAccrualSource
import Benchmarks.Midnight.PositionViewReturnSource

/-! Source frames and the initial storage-reading prefix of a position view. -/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Midnight

set_option maxRecDepth 2000000
set_option maxHeartbeats 1000000

attribute [local simp] wordLocal_get wordLocal_get_ne slashCreditFrame_get
  slashCreditFrame_contract slashPendingFrame_get slashPendingFrame_contract
  positionAccrualFrame_get positionAccrualFrame_contract

def positionViewArguments (m : MarketData) (id user : UInt256) : Store :=
  (((∅ : Store).insert "user" (.address (AccountAddress.ofNat user.toNat))).insert
    "id" (wordBytes32Value id)).insert "market" (Model.marketValue m.value)

def positionViewCallFrame (imms : Store) (m : MarketData) (id user : UInt256) : Frame :=
  { contract := contract, locals := positionViewArguments m id user, immutables := imms }

def positionViewAliasFrame (imms : Store) (m : MarketData) (id user : UInt256) : Frame :=
  { (positionViewCallFrame imms m id user) with
    locals := (positionViewArguments m id user).insert "_position"
      (.storageRef (positionRef id user) positionType) }

def positionViewCreditFrame (evm : EVM.State) (imms : Store) (m : MarketData) (id user : UInt256) : Frame :=
  wordLocal (wordLocal (wordLocal (positionViewAliasFrame imms m id user)
    "_credit" (positionFieldWord evm id user 0)) "_lastLossFactor" (positionFieldWord evm id user 2))
    "postSlashCredit" ⟨0⟩

def positionPostCredit (evm : EVM.State) (id user : UInt256) : UInt256 :=
  slashCredit (positionFieldWord evm id user 0) (positionFieldWord evm id user 2) (marketLossWord evm id)

def positionViewPendingFrame (evm : EVM.State) (imms : Store) (m : MarketData) (id user : UInt256) : Frame :=
  wordLocal (wordLocal (slashCreditFrame (positionViewCreditFrame evm imms m id user)
    (positionFieldWord evm id user 0) (positionFieldWord evm id user 2) (marketLossWord evm id))
    "_pendingFee" (positionFieldWord evm id user 1)) "postSlashPendingFee" ⟨0⟩

def positionPostPending (evm : EVM.State) (id user : UInt256) : UInt256 :=
  slashPending (positionFieldWord evm id user 0) (positionFieldWord evm id user 1)
    (positionPostCredit evm id user)

def positionViewPendingDoneFrame (evm : EVM.State) (imms : Store) (m : MarketData)
    (id user : UInt256) : Frame :=
  slashPendingFrame (positionViewPendingFrame evm imms m id user)
    (positionFieldWord evm id user 0) (positionFieldWord evm id user 1) (positionPostCredit evm id user)

def positionViewAccrualStartFrame (evm : EVM.State) (imms : Store) (m : MarketData)
    (id user : UInt256) : Frame :=
  wordLocal (wordLocal (wordLocal (positionViewPendingDoneFrame evm imms m id user)
    "accrualEnd" (wordMin (UInt256.ofNat evm.executionEnv.header.timestamp) m.maturity))
    "_lastAccrual" (positionFieldWord evm id user 3)) "fee" ⟨0⟩

def positionViewFee (evm : EVM.State) (m : MarketData) (id user : UInt256) : UInt256 :=
  positionAccruedFee (positionPostPending evm id user) (positionFieldWord evm id user 3)
    m.maturity (UInt256.ofNat evm.executionEnv.header.timestamp)

def positionViewResultFrame (evm : EVM.State) (imms : Store) (m : MarketData)
    (id user : UInt256) : Frame :=
  positionAccrualFrame (positionViewAccrualStartFrame evm imms m id user)
    (positionPostPending evm id user) (positionFieldWord evm id user 3)
    m.maturity (UInt256.ofNat evm.executionEnv.header.timestamp)

theorem positionViewCreditPrefix (evm : EVM.State) (imms : Store) (m : MarketData)
    (id user : UInt256) (hcanon : user.toNat < EVM.addressModulus) :
    ABlock config evm (positionViewCallFrame imms m id user) positionViewFunction.body
      (positionViewCreditFrame evm imms m id user) (positionViewFunction.body.drop 4) := by
  have ha : ABlock config evm (positionViewCallFrame imms m id user) positionViewFunction.body
      (positionViewAliasFrame imms m id user) (positionViewFunction.body.drop 1) := by
    refine ⟨fun h ↦ ExecBlock.consNormal (ExecStmt.letStorage ?_) h⟩
    apply resolvePositionRef rfl
    · simp [positionViewCallFrame, positionViewArguments]
    · simp [positionViewCallFrame, positionViewArguments, Std.HashMap.getElem_insert]
    · simp [positionViewCallFrame, positionViewArguments, Std.HashMap.getElem_insert]
  have ha1 := ha.letStep (evalPositionAliasField (evm := evm) 0 hcanon (store_get_self _ _ _))
  have ha2 := ha1.letStep (evalPositionAliasField (evm := evm) 2 hcanon (by
    exact (store_get_ne _ _ (by decide)).trans (store_get_self _ _ _)))
  exact ha2.letStep (by simp [evalExpr?, pure, UInt256.toNat])

theorem positionViewPendingPrefix (evm : EVM.State) (imms : Store) (m : MarketData)
    (id user : UInt256) (hcanon : user.toNat < EVM.addressModulus) :
    ABlock config evm (positionViewCallFrame imms m id user) positionViewFunction.body
      (positionViewPendingFrame evm imms m id user) (positionViewFunction.body.drop 7) := by
  have hp := positionViewCreditPrefix evm imms m id user hcanon
  have hs := slashCreditSource (frame := positionViewCreditFrame evm imms m id user)
    (evm := evm) (id := id) (credit := positionFieldWord evm id user 0)
    (lastLoss := positionFieldWord evm id user 2) rfl
    (by simp [positionViewCreditFrame, wordLocal, positionViewAliasFrame, positionViewArguments,
      Std.HashMap.getElem_insert])
    (by simp [positionViewCreditFrame, wordLocal, positionViewAliasFrame, positionViewArguments,
      Std.HashMap.getElem_insert])
    (by simp [positionViewCreditFrame, wordLocal, Std.HashMap.getElem_insert])
    (by simp [positionViewCreditFrame, wordLocal, Std.HashMap.getElem_insert])
    (wordLocal_get _ _ _) (positionFieldWord_lt evm id user 0)
  have hp1 := sourceNormalStep hp hs
  have hp2 := hp1.letStep (evalPositionAliasField (evm := evm) (id := id) 1 hcanon (by
    rw [slashCreditFrame_get _ _ _ _ _ (by decide) (by decide)]
    simp [positionViewCreditFrame, wordLocal, positionViewAliasFrame, Std.HashMap.getElem_insert]))
  exact hp2.letStep (by simp [evalExpr?, pure, UInt256.toNat])

theorem positionViewPendingFrame_postCredit (evm : EVM.State) (imms : Store) (m : MarketData)
    (id user : UInt256) :
    (positionViewPendingFrame evm imms m id user).locals.get? "postSlashCredit" =
      some (.int (positionPostCredit evm id user).toNat) := by
  dsimp only [positionViewPendingFrame]
  rw [wordLocal_get_ne _ _ _ _ (by decide), wordLocal_get_ne _ _ _ _ (by decide)]
  exact slashCreditFrame_value _ _ _ (wordLocal_get _ _ _)

theorem positionViewAccrualPrefix (evm : EVM.State) (imms : Store) (m : MarketData)
    (id user : UInt256) (hcanon : user.toNat < EVM.addressModulus)
    (hsafe : SlashPendingSafe (positionFieldWord evm id user 0) (positionFieldWord evm id user 1)
      (positionPostCredit evm id user)) :
    ABlock config evm (positionViewCallFrame imms m id user) positionViewFunction.body
      (positionViewAccrualStartFrame evm imms m id user) (positionViewFunction.body.drop 11) := by
  have hp := positionViewPendingPrefix evm imms m id user hcanon
  have hs := slashPendingSource (frame := positionViewPendingFrame evm imms m id user)
    (evm := evm) (credit := positionFieldWord evm id user 0)
    (pending := positionFieldWord evm id user 1) (postCredit := positionPostCredit evm id user)
    (by simp [positionViewPendingFrame, wordLocal, positionViewCreditFrame,
      positionViewAliasFrame, positionViewCallFrame])
    (by simp [-Std.HashMap.get?_eq_getElem?, positionViewPendingFrame, positionViewCreditFrame])
    (by simp [-Std.HashMap.get?_eq_getElem?, positionViewPendingFrame])
    (positionViewPendingFrame_postCredit evm imms m id user) (wordLocal_get _ _ _) hsafe
  have hp1 := sourceNormalStep hp hs
  have hm : (positionViewPendingDoneFrame evm imms m id user).locals.get? "market" =
      some (Model.marketValue m.value) := by
    simp [-Std.HashMap.get?_eq_getElem?, positionViewPendingDoneFrame, positionViewPendingFrame,
      positionViewCreditFrame, positionViewAliasFrame, positionViewArguments]
    simp [Std.HashMap.getElem_insert]
  have hargs : evalExprs? config (positionViewPendingDoneFrame evm imms m id user) evm
      [.env .timestamp, .field (.var "market") "maturity"] =
      .ok [.int (UInt256.ofNat evm.executionEnv.header.timestamp).toNat, .int m.maturity.toNat] := by
    simp only [evalExprs?, evalMarketMaturity hm, evalExpr?, envValue, bind, pure, EvalResult.bind,
      Int.ofNat_eq_natCast]
  have hp2 := sourceNormalStep hp1 (callMin (name := "accrualEnd")
    (by simp [positionViewPendingDoneFrame, positionViewPendingFrame, wordLocal,
      positionViewCreditFrame, positionViewAliasFrame, positionViewCallFrame]) hargs)
  have hp3 := hp2.letStep (evalPositionAliasField (evm := evm) (id := id) 3 hcanon (by
    change (wordLocal (positionViewPendingDoneFrame evm imms m id user) "accrualEnd" _).locals.get?
      "_position" = _
    simp [-Std.HashMap.get?_eq_getElem?, positionViewPendingDoneFrame, positionViewPendingFrame,
      positionViewCreditFrame, positionViewAliasFrame]
    exact store_get_self _ _ _))
  exact hp3.letStep (by simp [evalExpr?, pure, UInt256.toNat])

end Benchmarks.Midnight
