import Benchmarks.Midnight.TickPriceSource
import Benchmarks.Midnight.TakePricePrepare
import Benchmarks.Midnight.OfferSourceValues
import Benchmarks.Midnight.SettlementSource

variable {fork : Ethereum.Fork}

/-! Source calls producing the offer price, time to maturity, and settlement fee. -/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Midnight

set_option maxRecDepth 10000

def takePriceFrame (frame : Frame) (offer : OfferData) : Frame :=
  wordLocal frame "offerPrice" (tickPriceWord offer.tick.toNat)

def takeTimeFrame (frame : Frame) (I : ExecutionEnv) (offer : OfferData) : Frame :=
  wordLocal (takePriceFrame frame offer) "timeToMaturity" (takeTimeToMaturity I offer)

def takePricingFrame (frame : Frame) (I : ExecutionEnv) (offer : OfferData)
    (fee : UInt256) : Frame := wordLocal (takeTimeFrame frame I offer) "_settlementFee" fee

theorem TakeSourceFrame.pricing {frame : Frame} {offer : OfferData} {id units taker fee : UInt256}
    {receiver callback : AccountAddress} {ratifierData data : ByteArray} (I : ExecutionEnv)
    (hf : TakeSourceFrame frame offer id units taker receiver callback ratifierData data) :
    TakeSourceFrame (takePricingFrame frame I offer fee) offer id units taker receiver callback
      ratifierData data :=
  ((hf.insert "offerPrice" (.int (tickPriceWord offer.tick.toNat).toNat) (by decide)).insert
    "timeToMaturity" (.int (takeTimeToMaturity I offer).toNat) (by decide)).insert
      "_settlementFee" (.int fee.toNat) (by decide)

theorem takePricing_shape : takeTransition.body.drop 17 =
    takeTransition.body[17]! :: takeTransition.body[18]! :: takeTransition.body[19]! ::
      takeTransition.body.drop 20 := rfl

theorem takePriceSource {frame : Frame} {evm : State} {offer : OfferData}
    (hc : frame.contract = contract)
    (ho : frame.locals.get? "offer" = some (Model.offerValue offer.value))
    (hb : offer.tick.toNat ≤ 6744) :
    ExecStmt fork config frame evm takeTransition.body[17]! (.ok (takePriceFrame frame offer) evm) := by
  apply callTickToPrice hc _ hb
  simp only [evalExprs?, evalOfferTick ho, pure, bind, EvalResult.bind]

theorem takePriceSourceRevert {frame : Frame} {evm : State} {offer : OfferData}
    (hc : frame.contract = contract)
    (ho : frame.locals.get? "offer" = some (Model.offerValue offer.value))
    (hb : 6744 < offer.tick.toNat) :
    ExecStmt fork config frame evm takeTransition.body[17]! .reverted := by
  apply callTickToPriceRevert hc _ hb
  simp only [evalExprs?, evalOfferTick ho, pure, bind, EvalResult.bind]

theorem takeTimeSource {frame : Frame} {evm : State} {offer : OfferData}
    (hc : frame.contract = contract)
    (ho : frame.locals.get? "offer" = some (Model.offerValue offer.value)) :
    ExecStmt fork config (takePriceFrame frame offer) evm takeTransition.body[18]!
      (.ok (takeTimeFrame frame evm.executionEnv offer) evm) := by
  have ho1 : (takePriceFrame frame offer).locals.get? "offer" =
      some (Model.offerValue offer.value) := (store_get_ne _ _ (by decide)).trans ho
  apply callZeroFloorSub (frame := takePriceFrame frame offer) hc
  have he : evalExpr? config (takePriceFrame frame offer) evm
      (.field (.field (.var "offer") "market") "maturity") =
      .ok (.int offer.market.maturity.toNat) := by
    simp only [evalExpr?, ho1, EvalResult.ofOption, bind, EvalResult.bind]
    rfl
  simp only [evalExprs?, he, evalExpr?, envValue, bind, pure, EvalResult.bind]
  rfl

theorem callSettlementFee {frame : Frame} {evm : State} {id time : UInt256}
    {args : List Expr} {name : Ident} (hc : frame.contract = contract)
    (he : evalExprs? config frame evm args = .ok [wordBytes32Value id, .int time.toNat])
    (hspace : marketTickSpacing (marketFeeWord evm id) ≠ ⟨0⟩) :
    ExecStmt fork config frame evm (.internalCall "settlementFee_body" args name)
      (.ok (wordLocal frame name (settlementFeeValue (marketFeeWord evm id) time)) evm) := by
  obtain ⟨frame', hbody⟩ := settlementFeeInternalReturns (fork := fork) evm frame.immutables id time hspace
  apply internalCallFunctionReturn (callee := settlementFeeFunction)
    (locals := settlementFeeArguments id time)
    (value := some [.int (settlementFeeValue (marketFeeWord evm id) time).toNat]) he
  · rw [hc]; rfl
  · rfl
  · have hh : { frame with locals := settlementFeeArguments id time } =
        settlementCallFrame frame.immutables id time := by
      cases frame
      simp_all only [settlementCallFrame]
    rw [hh]
    exact hbody

theorem callSettlementFeeRevert {frame : Frame} {evm : State} {id time : UInt256}
    {args : List Expr} {name : Ident} (hc : frame.contract = contract)
    (he : evalExprs? config frame evm args = .ok [wordBytes32Value id, .int time.toNat])
    (hspace : marketTickSpacing (marketFeeWord evm id) = ⟨0⟩) :
    ExecStmt fork config frame evm (.internalCall "settlementFee_body" args name) .reverted := by
  apply internalCallFunctionRevert (callee := settlementFeeFunction)
    (locals := settlementFeeArguments id time) he
  · rw [hc]; rfl
  · rfl
  · have hh : { frame with locals := settlementFeeArguments id time } =
        settlementCallFrame frame.immutables id time := by
      cases frame
      simp_all only [settlementCallFrame]
    rw [hh]
    exact settlementFeeInternalReverts evm frame.immutables id time hspace

theorem takeSettlementArgs {frame : Frame} {evm : State} {offer : OfferData} {id : UInt256}
    (hi : frame.locals.get? "id" = some (wordBytes32Value id)) :
    evalExprs? config (takeTimeFrame frame evm.executionEnv offer) evm
      [.var "id", .var "timeToMaturity"] =
      .ok [wordBytes32Value id, .int (takeTimeToMaturity evm.executionEnv offer).toNat] := by
  have hid : (takeTimeFrame frame evm.executionEnv offer).locals.get? "id" =
      some (wordBytes32Value id) := by
    exact (store_get_ne _ _ (by decide)).trans ((store_get_ne _ _ (by decide)).trans hi)
  have ht : (takeTimeFrame frame evm.executionEnv offer).locals.get? "timeToMaturity" =
      some (.int (takeTimeToMaturity evm.executionEnv offer).toNat) := store_get_self ..
  simp only [evalExprs?, evalExpr?, hid, ht, EvalResult.ofOption, bind, pure, EvalResult.bind]

theorem takePricingSource {frame : Frame} {evm : State} {offer : OfferData} {id : UInt256}
    (hc : frame.contract = contract)
    (ho : frame.locals.get? "offer" = some (Model.offerValue offer.value))
    (hi : frame.locals.get? "id" = some (wordBytes32Value id))
    (hb : offer.tick.toNat ≤ 6744)
    (hspace : marketTickSpacing (marketFeeWord evm id) ≠ ⟨0⟩) :
    ABlock fork config evm frame (takeTransition.body.drop 17)
      (takePricingFrame frame evm.executionEnv offer
        (settlementFeeValue (marketFeeWord evm id) (takeTimeToMaturity evm.executionEnv offer)))
      (takeTransition.body.drop 20) := by
  rw [takePricing_shape]
  refine ⟨fun h ↦ ExecBlock.consNormal (takePriceSource hc ho hb)
    (ExecBlock.consNormal (takeTimeSource hc ho)
      (ExecBlock.consNormal ?_ h))⟩
  exact callSettlementFee (frame := takeTimeFrame frame evm.executionEnv offer) hc
    (takeSettlementArgs hi) hspace

theorem takePricingSourceRevert {frame : Frame} {evm : State} {offer : OfferData} {id : UInt256}
    (hc : frame.contract = contract)
    (ho : frame.locals.get? "offer" = some (Model.offerValue offer.value))
    (hi : frame.locals.get? "id" = some (wordBytes32Value id))
    (hbad : 6744 < offer.tick.toNat ∨ marketTickSpacing (marketFeeWord evm id) = ⟨0⟩) :
    ExecBlock fork config frame evm (takeTransition.body.drop 17) .reverted := by
  rw [takePricing_shape]
  by_cases hb : offer.tick.toNat ≤ 6744
  · have hz : marketTickSpacing (marketFeeWord evm id) = ⟨0⟩ :=
      hbad.elim (fun h ↦ False.elim (by omega)) (fun h ↦ h)
    apply ExecBlock.consNormal (takePriceSource hc ho hb)
    apply ExecBlock.consNormal (takeTimeSource hc ho)
    exact ExecBlock.consRevert
      (callSettlementFeeRevert (frame := takeTimeFrame frame evm.executionEnv offer) hc
        (takeSettlementArgs hi) hz)
  · exact ExecBlock.consRevert (takePriceSourceRevert hc ho (by omega))

end Benchmarks.Midnight
