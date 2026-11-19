import Benchmarks.Midnight.ClaimSettlementSource
import Benchmarks.Midnight.TakeConsumptionValues
import Benchmarks.Midnight.PackedStorageSourceState

/-! Source storage operations for the trade's settlement fee and consumed counter. -/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Midnight

def takeSettlementRef : StorageRef :=
  { base := "claimableSettlementFee", steps :=
    [.mindex (.field (.field (.var "offer") "market") "loanToken")] }

def takeSettlementState (evm : State) (offer : OfferData) (delta : UInt256) : State :=
  Stele.EVM.storageStore evm evm.executionEnv.codeOwner (claimSettlementSlot offer.market.loanToken)
    (claimSettlementBalance evm offer.market.loanToken + delta)

theorem evalOfferLoanToken {cfg : Config} {frame : Frame} {evm : State} {offer : OfferData}
    (ho : frame.locals.get? "offer" = some (Model.offerValue offer.value)) :
    evalExpr? cfg frame evm (.field (.field (.var "offer") "market") "loanToken") =
      .ok (.address offer.market.loanToken) := by
  rw [evalExpr?, evalOfferMarket ho]
  rfl

theorem takeSettlementResolve {frame : Frame} {evm : State} {offer : OfferData}
    (ho : frame.locals.get? "offer" = some (Model.offerValue offer.value)) :
    evalStorageRef config frame evm takeSettlementRef = .ok
      { base := "claimableSettlementFee", steps := [.mindex (.address offer.market.loanToken)] } := by
  simp only [takeSettlementRef, evalStorageRef, evalStorageRefSteps, evalStorageRefStep,
    evalOfferLoanToken ho, EvalResult.bind, valueToKey?, EvalResult.ofOption, pure, bind]

theorem evalTakeSettlement {frame : Frame} {evm : State} {offer : OfferData}
    (hc : frame.contract = contract) (hn : frame.locals.get? "claimableSettlementFee" = none)
    (ho : frame.locals.get? "offer" = some (Model.offerValue offer.value)) :
    evalExpr? config frame evm (.storage takeSettlementRef) =
      .ok (.int (claimSettlementBalance evm offer.market.loanToken).toNat) := by
  apply evalExpr_storage_scalar_value
    (er := { base := "claimableSettlementFee", steps := [.mindex (.address offer.market.loanToken)] })
    (loc := {
      slot := claimSettlementSlot offer.market.loanToken, offset := 0, size := 32,
      hbound := by decide, type := .int (.uint ⟨256, by decide⟩) })
    (t := .int (.uint ⟨256, by decide⟩))
  · exact hn
  · exact takeSettlementResolve ho
  · rw [hc]; rfl
  · rfl
  · exact claimSettlementLayout offer.market.loanToken
  · exact storageLocLoad_uint256 evm _

theorem assignTakeSettlement {frame : Frame} {evm : State} {offer : OfferData} (delta : UInt256)
    (hc : frame.contract = contract) (hn : frame.locals.get? "claimableSettlementFee" = none)
    (ho : frame.locals.get? "offer" = some (Model.offerValue offer.value)) :
    assignStorageRef? config frame evm .storage takeSettlementRef
      (.int (claimSettlementBalance evm offer.market.loanToken + delta).toNat) =
      .ok (frame, takeSettlementState evm offer delta) := by
  apply assignStorageRef_storage_scalar_value
    (er := { base := "claimableSettlementFee", steps := [.mindex (.address offer.market.loanToken)] })
    (loc := {
      slot := claimSettlementSlot offer.market.loanToken, offset := 0, size := 32,
      hbound := by decide, type := .int (.uint ⟨256, by decide⟩) })
    (ty := .elem (.int (.uint ⟨256, by decide⟩))) (layout := midnightStorageLayout)
  · exact hn
  · exact takeSettlementResolve ho
  · rw [hc]; rfl
  · rfl
  · exact claimSettlementLayout offer.market.loanToken
  · exact Or.inl ⟨_, rfl⟩
  · exact storageLocStore_uint256 evm _ _

theorem assignTakeConsumed {frame : Frame} {evm : State} {offer : OfferData} (value : UInt256)
    (hc : frame.contract = contract) (hn : frame.locals.get? "consumed" = none)
    (ho : frame.locals.get? "offer" = some (Model.offerValue offer.value)) :
    assignStorageRef? config frame evm .storage takeConsumedRef (.int value.toNat) =
      .ok (frame, storeLow128 evm (consumedSlot offer.group (UInt256.ofNat offer.maker.val)) value)
      := by
  apply assignStorageRef_storage_scalar_value
    (loc := uint128LowLoc (consumedSlot offer.group (UInt256.ofNat offer.maker.val)))
    (er := { base := "consumed", steps := [.mindex (.address offer.maker),
      .mindex (.fixedBytes abiBytes32Width (EVM.Word.toBytesBE offer.group))] })
    (ty := .elem (.int packedUInt128Int)) (layout := midnightStorageLayout)
  · exact hn
  · simp only [takeConsumedRef, evalStorageRef, evalStorageRefSteps, evalStorageRefStep,
      evalOfferMaker ho, evalOfferGroup ho, EvalResult.bind, valueToKey?, wordBytes32Value,
      pure, bind]
    have hlen : (EVM.Word.toBytesBE offer.group).length = 32 := by
      simpa using word_toBytesBE_toByteArray_size offer.group
    simp only [hlen, abiBytes32Width]
    rfl
  · rw [hc]; rfl
  · rfl
  · change some (StorageAddr.leaf {
      slot := solcMappingSlot (solcMappingSlot ⟨2⟩ (keyValueToWord (.address offer.maker)))
        (keyValueToWord (.fixedBytes abiBytes32Width (EVM.Word.toBytesBE offer.group))),
      offset := 0, size := 16, hbound := by decide, type := .int packedUInt128Int }) = _
    simp only [keyValueToWord_address, keyValueToWord_fixedBytes32, abiBytes32Width]
    rfl
  · exact Or.inl ⟨_, rfl⟩
  · exact storageLocStore_uint128_low_word ..

end Benchmarks.Midnight
