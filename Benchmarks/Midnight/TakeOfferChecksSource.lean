import Benchmarks.Midnight.TakeOfferGuardsSource

variable {fork : Ethereum.Fork}

/-! The source offer checks, including every early revert before ratifier authorization. -/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Midnight

set_option maxRecDepth 10000

structure TakeOfferChecks (evm : State) (offer : OfferData) (id taker : UInt256)
    (receiver : AccountAddress) : Prop where
  loss : (marketLossWord evm id).toNat < 2^128 - 1
  caps : TakeCapsValid offer
  fee : (marketContinuousFee (marketFeeWord evm id)).toNat ≤ offer.continuousFeeCap.toNat
  spacing : marketTickSpacing (marketFeeWord evm id) ≠ ⟨0⟩
  tick : offer.tick.toNat % (marketTickSpacing (marketFeeWord evm id)).toNat = 0
  time : TakeTimeValid evm.executionEnv offer
  self : UInt256.ofNat offer.maker.val ≠ taker
  receiver : takeUnusedReceiverWord offer receiver = ⟨0⟩

theorem takeOfferChecks_shape : takeTransition.body.drop 6 =
    [.require takeLossGuard, .require takeCapsGuard, .require takeFeeCapGuard,
      .require takeTickGuard, .require takeStartGuard, .require takeExpiryGuard,
      .require takeSelfGuard, .require takeReceiverGuard] ++ takeTransition.body.drop 14 := rfl

theorem takeOfferChecksSource {frame : Frame} {evm : State} {offer : OfferData} {id taker : UInt256}
    {receiver : AccountAddress}
    (hm : frame.locals.get? "_marketState" =
      some (.storageRef (marketStateRef id) marketStateType))
    (ho : frame.locals.get? "offer" = some (Model.offerValue offer.value))
    (ht : frame.locals.get? "taker" = some (.address (AccountAddress.ofNat taker.toNat)))
    (hr : frame.locals.get? "receiverIfTakerIsSeller" = some (.address receiver))
    (hc : taker.toNat < EVM.addressModulus) (hs : TakeOfferChecks evm offer id taker receiver) :
    ABlock fork config evm frame (takeTransition.body.drop 6) frame (takeTransition.body.drop 14) := by
  rw [takeOfferChecks_shape]
  exact ABlock.start
    |>.requireStep ((evalTakeLossGuard hm).trans (by rw [decide_eq_true hs.loss]))
    |>.requireStep ((evalTakeCapsGuard ho).trans (by rw [decide_eq_true hs.caps]))
    |>.requireStep ((evalTakeFeeCapGuard hm ho).trans (by rw [decide_eq_true hs.fee]))
    |>.requireStep ((evalTakeTickGuard hm ho hs.spacing).trans (by rw [decide_eq_true hs.tick]))
    |>.requireStep ((evalTakeStartGuard ho).trans (by rw [decide_eq_true hs.time.1]))
    |>.requireStep ((evalTakeExpiryGuard ho).trans (by rw [decide_eq_true hs.time.2]))
    |>.requireStep ((evalTakeSelfGuard ho ht hc).trans (by rw [decide_eq_true hs.self]))
    |>.requireStep ((evalTakeReceiverGuard ho hr).trans (by rw [decide_eq_true hs.receiver]))

theorem takeOfferChecksRevert {frame : Frame} {evm : State} {offer : OfferData} {id taker : UInt256}
    {receiver : AccountAddress}
    (hm : frame.locals.get? "_marketState" =
      some (.storageRef (marketStateRef id) marketStateType))
    (ho : frame.locals.get? "offer" = some (Model.offerValue offer.value))
    (ht : frame.locals.get? "taker" = some (.address (AccountAddress.ofNat taker.toNat)))
    (hr : frame.locals.get? "receiverIfTakerIsSeller" = some (.address receiver))
    (hc : taker.toNat < EVM.addressModulus) (hbad : ¬ TakeOfferChecks evm offer id taker receiver) :
    ExecBlock fork config frame evm (takeTransition.body.drop 6) .reverted := by
  rw [takeOfferChecks_shape]
  by_cases hl : (marketLossWord evm id).toNat < 2^128 - 1
  · apply ExecBlock.consNormal (ExecStmt.requireTrue ((evalTakeLossGuard hm).trans
      (by rw [decide_eq_true hl])))
    by_cases hcap : TakeCapsValid offer
    · apply ExecBlock.consNormal (ExecStmt.requireTrue ((evalTakeCapsGuard ho).trans
        (by rw [decide_eq_true hcap])))
      by_cases hf : (marketContinuousFee (marketFeeWord evm id)).toNat ≤ offer.continuousFeeCap.toNat
      · apply ExecBlock.consNormal (ExecStmt.requireTrue ((evalTakeFeeCapGuard hm ho).trans
          (by rw [decide_eq_true hf])))
        by_cases hspacing : marketTickSpacing (marketFeeWord evm id) = ⟨0⟩
        · exact ExecBlock.consRevert (ExecStmt.requireRevert
            (evalTakeTickGuard_zero hm ho hspacing))
        · by_cases htick : offer.tick.toNat % (marketTickSpacing (marketFeeWord evm id)).toNat = 0
          · apply ExecBlock.consNormal (ExecStmt.requireTrue
              ((evalTakeTickGuard hm ho hspacing).trans (by rw [decide_eq_true htick])))
            by_cases hstart : offer.start.toNat ≤
                (UInt256.ofNat evm.executionEnv.header.timestamp).toNat
            · apply ExecBlock.consNormal (ExecStmt.requireTrue ((evalTakeStartGuard ho).trans
                (by rw [decide_eq_true hstart])))
              by_cases hexpiry : (UInt256.ofNat evm.executionEnv.header.timestamp).toNat ≤
                  offer.expiry.toNat
              · apply ExecBlock.consNormal (ExecStmt.requireTrue ((evalTakeExpiryGuard ho).trans
                  (by rw [decide_eq_true hexpiry])))
                by_cases hself : UInt256.ofNat offer.maker.val = taker
                · exact ExecBlock.consRevert (ExecStmt.requireFalse
                    ((evalTakeSelfGuard ho ht hc).trans (by rw [decide_eq_false (not_not.mpr hself)])))
                · apply ExecBlock.consNormal (ExecStmt.requireTrue ((evalTakeSelfGuard ho ht hc).trans
                    (by rw [decide_eq_true hself])))
                  have hreceiver : takeUnusedReceiverWord offer receiver ≠ ⟨0⟩ := fun h ↦
                    hbad ⟨hl, hcap, hf, hspacing, htick, ⟨hstart, hexpiry⟩, hself, h⟩
                  exact ExecBlock.consRevert (ExecStmt.requireFalse
                    ((evalTakeReceiverGuard ho hr).trans (by rw [decide_eq_false hreceiver])))
              · exact ExecBlock.consRevert (ExecStmt.requireFalse
                  ((evalTakeExpiryGuard ho).trans (by rw [decide_eq_false hexpiry])))
            · exact ExecBlock.consRevert (ExecStmt.requireFalse
                ((evalTakeStartGuard ho).trans (by rw [decide_eq_false hstart])))
          · exact ExecBlock.consRevert (ExecStmt.requireFalse
              ((evalTakeTickGuard hm ho hspacing).trans (by rw [decide_eq_false htick])))
      · exact ExecBlock.consRevert (ExecStmt.requireFalse
          ((evalTakeFeeCapGuard hm ho).trans (by rw [decide_eq_false hf])))
    · exact ExecBlock.consRevert (ExecStmt.requireFalse
        ((evalTakeCapsGuard ho).trans (by rw [decide_eq_false hcap])))
  · exact ExecBlock.consRevert (ExecStmt.requireFalse
      ((evalTakeLossGuard hm).trans (by rw [decide_eq_false hl])))

end Benchmarks.Midnight
