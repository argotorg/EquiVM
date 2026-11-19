import Benchmarks.Midnight.TakeBasicGuardsSource
import Benchmarks.Midnight.TakeReceiverGuard
import Benchmarks.Midnight.PackedFields

/-! Source evaluation of the offer fee, tick, timing, and participant checks. -/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Midnight

set_option maxRecDepth 10000

theorem evalMarketAliasContinuousFee {frame : Frame} {evm : State} {id : UInt256}
    (hm : frame.locals.get? "_marketState" =
      some (.storageRef (marketStateRef id) marketStateType)) :
    evalExpr? config frame evm
      (.storage { base := "_marketState", steps := [.field "continuousFee"] }) =
      .ok (.int (marketContinuousFee (marketFeeWord evm id)).toNat) := by
  apply evalStorageAliasField (loc := {
      slot := solcMappingSlot ⟨1⟩ id + ⟨2⟩, offset := 14, size := 4,
      hbound := by decide, type := .int (.uint ⟨32, by decide⟩) }) hm rfl rfl ?_ ?_
  · change some (StorageAddr.leaf {
      slot := solcMappingSlot ⟨1⟩
        (keyValueToWord (.fixedBytes abiBytes32Width (EVM.Word.toBytesBE id))) + ⟨2⟩,
      offset := 14, size := 4, hbound := by decide, type := .int (.uint ⟨32, by decide⟩) }) = _
    simp only [abiBytes32Width, keyValueToWord_fixedBytes32]
  · exact storageLocLoad_uint32_offset14 evm _

def takeFeeCapGuard : Expr :=
  .binary .le (.storage { base := "_marketState", steps := [.field "continuousFee"] })
    (.field (.var "offer") "continuousFeeCap")

def takeTickGuard : Expr :=
  .binary .eq (.binary .mod (.field (.var "offer") "tick")
    (.storage { base := "_marketState", steps := [.field "tickSpacing"] })) (.intLit 0)

def takeStartGuard : Expr :=
  .binary .ge (.env .timestamp) (.field (.var "offer") "start")

def takeExpiryGuard : Expr :=
  .binary .le (.env .timestamp) (.field (.var "offer") "expiry")

def takeSelfGuard : Expr :=
  .binary .ne (.field (.var "offer") "maker") (.var "taker")

def takeReceiverGuard : Expr :=
  .ite (.field (.var "offer") "buy")
    (.binary .eq (.field (.var "offer") "receiverIfMakerIsSeller")
      (.cast (.intLit 0) (.elem .address)))
    (.binary .eq (.var "receiverIfTakerIsSeller") (.cast (.intLit 0) (.elem .address)))

theorem evalTakeFeeCapGuard {frame : Frame} {evm : State} {offer : OfferData} {id : UInt256}
    (hm : frame.locals.get? "_marketState" =
      some (.storageRef (marketStateRef id) marketStateType))
    (ho : frame.locals.get? "offer" = some (Model.offerValue offer.value)) :
    evalExpr? config frame evm takeFeeCapGuard =
      .ok (.bool (decide ((marketContinuousFee (marketFeeWord evm id)).toNat ≤
        offer.continuousFeeCap.toNat))) := by
  unfold takeFeeCapGuard
  rw [evalExpr_binary_nonshort (by decide) (by decide),
    evalMarketAliasContinuousFee hm, evalOfferContinuousFeeCap ho]
  simp only [bind, EvalResult.bind, evalBinaryOp?]
  norm_cast

theorem evalTakeTickGuard {frame : Frame} {evm : State} {offer : OfferData} {id : UInt256}
    (hm : frame.locals.get? "_marketState" =
      some (.storageRef (marketStateRef id) marketStateType))
    (ho : frame.locals.get? "offer" = some (Model.offerValue offer.value))
    (hne : marketTickSpacing (marketFeeWord evm id) ≠ ⟨0⟩) :
    evalExpr? config frame evm takeTickGuard =
      .ok (.bool (decide (offer.tick.toNat %
        (marketTickSpacing (marketFeeWord evm id)).toNat = 0))) := by
  have hn : ((marketTickSpacing (marketFeeWord evm id)).toNat : Int) ≠ 0 := by
    exact_mod_cast fun h ↦ hne (uint256_toNat_eq_zero h)
  unfold takeTickGuard
  rw [evalExpr_binary_nonshort (by decide) (by decide),
    evalExpr_binary_nonshort (by decide : BinaryOp.mod ≠ .and) (by decide : BinaryOp.mod ≠ .or),
    evalOfferTick ho, evalMarketAliasTickSpacing hm]
  simp only [evalExpr?, bind, pure, EvalResult.bind, evalBinaryOp?, hn, if_false,
    Reasoning.VyperDispatch.value_int_beq]
  norm_cast

theorem evalTakeTickGuard_zero {frame : Frame} {evm : State} {offer : OfferData} {id : UInt256}
    (hm : frame.locals.get? "_marketState" =
      some (.storageRef (marketStateRef id) marketStateType))
    (ho : frame.locals.get? "offer" = some (Model.offerValue offer.value))
    (hz : marketTickSpacing (marketFeeWord evm id) = ⟨0⟩) :
    evalExpr? config frame evm takeTickGuard = .revert := by
  unfold takeTickGuard
  rw [evalExpr_binary_nonshort (by decide) (by decide),
    evalExpr_binary_nonshort (by decide : BinaryOp.mod ≠ .and) (by decide : BinaryOp.mod ≠ .or),
    evalOfferTick ho, evalMarketAliasTickSpacing hm, hz]
  rfl

theorem evalTakeStartGuard {frame : Frame} {evm : State} {offer : OfferData}
    (ho : frame.locals.get? "offer" = some (Model.offerValue offer.value)) :
    evalExpr? config frame evm takeStartGuard =
      .ok (.bool (decide (offer.start.toNat ≤
        (UInt256.ofNat evm.executionEnv.header.timestamp).toNat))) := by
  unfold takeStartGuard
  rw [evalExpr_binary_nonshort (by decide) (by decide), evalOfferStart ho]
  simp only [evalExpr?, envValue, bind, pure, EvalResult.bind, evalBinaryOp?,
    Int.ofNat_eq_natCast]
  norm_cast

theorem evalTakeExpiryGuard {frame : Frame} {evm : State} {offer : OfferData}
    (ho : frame.locals.get? "offer" = some (Model.offerValue offer.value)) :
    evalExpr? config frame evm takeExpiryGuard =
      .ok (.bool (decide ((UInt256.ofNat evm.executionEnv.header.timestamp).toNat ≤
        offer.expiry.toNat))) := by
  unfold takeExpiryGuard
  rw [evalExpr_binary_nonshort (by decide) (by decide), evalOfferExpiry ho]
  simp only [evalExpr?, envValue, bind, pure, EvalResult.bind, evalBinaryOp?,
    Int.ofNat_eq_natCast]
  norm_cast

-- LIBRARY CANDIDATE: compare a source address with a canonical EVM address word.
theorem address_eq_canonical_word (address : AccountAddress) (word : UInt256)
    (hc : word.toNat < EVM.addressModulus) :
    address = AccountAddress.ofNat word.toNat ↔ UInt256.ofNat address.val = word := by
  have h := accountAddress_ofUInt256_eq_iff_of_canonical (addressWord_canonical address) hc
  simpa only [accountAddress_ofUInt256_eq_ofNat_toNat,
    UInt256.toNat_ofNat_of_lt (Nat.lt_trans address.isLt (by decide)),
    accountAddress_ofNat_val] using h

theorem evalTakeSelfGuard {frame : Frame} {evm : State} {offer : OfferData} {taker : UInt256}
    (ho : frame.locals.get? "offer" = some (Model.offerValue offer.value))
    (ht : frame.locals.get? "taker" = some (.address (AccountAddress.ofNat taker.toNat)))
    (hc : taker.toNat < EVM.addressModulus) :
    evalExpr? config frame evm takeSelfGuard =
      .ok (.bool (decide (UInt256.ofNat offer.maker.val ≠ taker))) := by
  unfold takeSelfGuard
  rw [evalExpr_binary_nonshort (by decide) (by decide), evalOfferMaker ho]
  simp only [evalExpr?, ht, EvalResult.ofOption, bind, EvalResult.bind, evalBinaryOp?,
    Reasoning.VyperDispatch.value_address_beq, address_eq_canonical_word _ _ hc, decide_not]

theorem evalTakeReceiverGuard {frame : Frame} {evm : State} {offer : OfferData}
    {receiver : AccountAddress}
    (ho : frame.locals.get? "offer" = some (Model.offerValue offer.value))
    (hr : frame.locals.get? "receiverIfTakerIsSeller" = some (.address receiver)) :
    evalExpr? config frame evm takeReceiverGuard =
      .ok (.bool (decide (takeUnusedReceiverWord offer receiver = ⟨0⟩))) := by
  have hz (address : AccountAddress) :
      (address = AccountAddress.ofNat 0) ↔ UInt256.ofNat address.val = ⟨0⟩ :=
    address_eq_canonical_word address ⟨0⟩ (by decide)
  unfold takeReceiverGuard
  rw [evalExpr?, evalOfferBuy ho]
  simp only [wordToElemBool, bind, EvalResult.bind]
  by_cases hb : offer.buy = ⟨0⟩
  · simp only [hb, decide_true, Bool.not_true, takeUnusedReceiverWord, if_true]
    rw [evalExpr_binary_nonshort (by decide) (by decide)]
    simp only [evalExpr?, hr, EvalResult.ofOption, bind, pure, EvalResult.bind]
    change evalBinaryOp? .eq (.address receiver) (.address (AccountAddress.ofNat 0)) = _
    simp only [evalBinaryOp?, Reasoning.VyperDispatch.value_address_beq, hz]
  · simp only [hb, decide_false, Bool.not_false, takeUnusedReceiverWord, if_false]
    rw [evalExpr_binary_nonshort (by decide) (by decide), evalOfferReceiverIfMakerIsSeller ho]
    simp only [evalExpr?, EvalResult.ofOption, bind, pure, EvalResult.bind]
    change evalBinaryOp? .eq (.address offer.receiverIfMakerIsSeller)
      (.address (AccountAddress.ofNat 0)) = _
    simp only [evalBinaryOp?, Reasoning.VyperDispatch.value_address_beq, hz]

end Benchmarks.Midnight
