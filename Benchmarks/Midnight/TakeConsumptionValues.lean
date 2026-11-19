import Benchmarks.Midnight.TakeAmounts
import Benchmarks.Midnight.SetConsumed

/-! The offer's consumed counter, selected increment, and corresponding cap. -/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Midnight

set_option maxRecDepth 10000

def takeConsumedRef : StorageRef :=
  { base := "consumed", steps := [.mindex (.field (.var "offer") "maker"),
    .mindex (.field (.var "offer") "group")] }

def takeConsumedStored (evm : State) (offer : OfferData) : UInt256 :=
  consumedStored evm offer.group (UInt256.ofNat offer.maker.val)

def takeConsumedDelta (offer : OfferData) (units bought sold : UInt256) : UInt256 :=
  if offer.maxAssets = ⟨0⟩ then units else if offer.buy = ⟨0⟩ then sold else bought

def takeConsumedCap (offer : OfferData) : UInt256 :=
  if offer.maxAssets = ⟨0⟩ then offer.maxUnits else offer.maxAssets

def TakeConsumptionSafe (old : UInt256) (offer : OfferData) (units bought sold : UInt256) : Prop :=
  old.toNat + (takeConsumedDelta offer units bought sold).toNat ≤ (takeConsumedCap offer).toNat

theorem evalTakeConsumed {frame : Frame} {evm : State} {offer : OfferData}
    (hc : frame.contract = contract) (hn : frame.locals.get? "consumed" = none)
    (ho : frame.locals.get? "offer" = some (Model.offerValue offer.value)) :
    evalExpr? config frame evm (.storage takeConsumedRef) =
      .ok (.int (takeConsumedStored evm offer).toNat) := by
  apply evalExpr_storage_scalar_value
    (loc := uint128LowLoc (consumedSlot offer.group (UInt256.ofNat offer.maker.val)))
    (er := { base := "consumed", steps := [.mindex (.address offer.maker),
      .mindex (.fixedBytes abiBytes32Width (EVM.Word.toBytesBE offer.group))] })
    (t := .int packedUInt128Int)
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
  · exact storageLocLoad_uint_offset0 evm _ 16 ⟨128, by decide⟩ (by decide) (by decide)

def takeConsumedAssetExpr : Expr :=
  .ite (.field (.var "offer") "buy") (.var "buyerAssets") (.var "sellerAssets")

theorem evalTakeConsumedAsset {cfg : Config} {frame : Frame} {evm : State} {offer : OfferData}
    {bought sold : UInt256}
    (ho : frame.locals.get? "offer" = some (Model.offerValue offer.value))
    (hb : frame.locals.get? "buyerAssets" = some (.int bought.toNat))
    (hs : frame.locals.get? "sellerAssets" = some (.int sold.toNat)) :
    evalExpr? cfg frame evm takeConsumedAssetExpr =
      .ok (.int (if offer.buy = ⟨0⟩ then sold else bought).toNat) := by
  rw [takeConsumedAssetExpr, evalExpr?, evalOfferBuy ho]
  simp only [wordToElemBool, bind, EvalResult.bind]
  by_cases hbuy : offer.buy = ⟨0⟩
  · simpa only [hbuy, decide_true, Bool.not_true, if_true] using evalWordLocal hs
  · simpa only [hbuy, decide_false, Bool.not_false, if_false] using evalWordLocal hb

theorem evalTakeConsumedMode {cfg : Config} {frame : Frame} {evm : State} {offer : OfferData}
    (ho : frame.locals.get? "offer" = some (Model.offerValue offer.value)) :
    evalExpr? cfg frame evm (.binary .gt (.field (.var "offer") "maxAssets") (.intLit 0)) =
      .ok (.bool (!decide (offer.maxAssets = ⟨0⟩))) := by
  rw [evalExpr_binary_nonshort (by decide) (by decide), evalOfferMaxAssets ho]
  simp only [evalExpr?, pure, bind, EvalResult.bind, evalBinaryOp?, Int.ofNat_lt]
  have hz : 0 < offer.maxAssets.toNat ↔ offer.maxAssets ≠ ⟨0⟩ := by
    constructor
    · intro h he; rw [he] at h; contradiction
    · intro h
      exact Nat.pos_of_ne_zero (fun he ↦ h (uint256_toNat_eq_zero he))
  simp only [gt_iff_lt, Int.natCast_pos, hz, decide_not]

end Benchmarks.Midnight
