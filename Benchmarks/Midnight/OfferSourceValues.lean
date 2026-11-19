import Benchmarks.Midnight.TakeSourceFrame

/-! Source evaluation of the fifteen typed offer fields. -/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Midnight

theorem evalOfferMarket {cfg : Config} {frame : Frame} {evm : State} {offer : OfferData}
    (ho : frame.locals.get? "offer" = some (Model.offerValue offer.value)) :
    evalExpr? cfg frame evm (.field (.var "offer") "market") =
      .ok (Model.marketValue offer.market.value) := by
  simp only [evalExpr?, ho, EvalResult.ofOption, bind, EvalResult.bind]
  rfl

theorem evalOfferBuy {cfg : Config} {frame : Frame} {evm : State} {offer : OfferData}
    (ho : frame.locals.get? "offer" = some (Model.offerValue offer.value)) :
    evalExpr? cfg frame evm (.field (.var "offer") "buy") =
      .ok (wordToElem .bool offer.buy) := by
  simp only [evalExpr?, ho, EvalResult.ofOption, bind, EvalResult.bind]
  rfl

theorem evalOfferMaker {cfg : Config} {frame : Frame} {evm : State} {offer : OfferData}
    (ho : frame.locals.get? "offer" = some (Model.offerValue offer.value)) :
    evalExpr? cfg frame evm (.field (.var "offer") "maker") =
      .ok (.address offer.maker) := by
  simp only [evalExpr?, ho, EvalResult.ofOption, bind, EvalResult.bind]
  rfl

theorem evalOfferStart {cfg : Config} {frame : Frame} {evm : State} {offer : OfferData}
    (ho : frame.locals.get? "offer" = some (Model.offerValue offer.value)) :
    evalExpr? cfg frame evm (.field (.var "offer") "start") =
      .ok (.int offer.start.toNat) := by
  simp only [evalExpr?, ho, EvalResult.ofOption, bind, EvalResult.bind]
  rfl

theorem evalOfferExpiry {cfg : Config} {frame : Frame} {evm : State} {offer : OfferData}
    (ho : frame.locals.get? "offer" = some (Model.offerValue offer.value)) :
    evalExpr? cfg frame evm (.field (.var "offer") "expiry") =
      .ok (.int offer.expiry.toNat) := by
  simp only [evalExpr?, ho, EvalResult.ofOption, bind, EvalResult.bind]
  rfl

theorem evalOfferTick {cfg : Config} {frame : Frame} {evm : State} {offer : OfferData}
    (ho : frame.locals.get? "offer" = some (Model.offerValue offer.value)) :
    evalExpr? cfg frame evm (.field (.var "offer") "tick") =
      .ok (.int offer.tick.toNat) := by
  simp only [evalExpr?, ho, EvalResult.ofOption, bind, EvalResult.bind]
  rfl

theorem evalOfferGroup {cfg : Config} {frame : Frame} {evm : State} {offer : OfferData}
    (ho : frame.locals.get? "offer" = some (Model.offerValue offer.value)) :
    evalExpr? cfg frame evm (.field (.var "offer") "group") =
      .ok (wordBytes32Value offer.group) := by
  simp only [evalExpr?, ho, EvalResult.ofOption, bind, EvalResult.bind]
  rfl

theorem evalOfferCallback {cfg : Config} {frame : Frame} {evm : State} {offer : OfferData}
    (ho : frame.locals.get? "offer" = some (Model.offerValue offer.value)) :
    evalExpr? cfg frame evm (.field (.var "offer") "callback") =
      .ok (.address offer.callback) := by
  simp only [evalExpr?, ho, EvalResult.ofOption, bind, EvalResult.bind]
  rfl

theorem evalOfferCallbackData {cfg : Config} {frame : Frame} {evm : State} {offer : OfferData}
    (ho : frame.locals.get? "offer" = some (Model.offerValue offer.value)) :
    evalExpr? cfg frame evm (.field (.var "offer") "callbackData") =
      .ok (.bytes offer.callbackData) := by
  simp only [evalExpr?, ho, EvalResult.ofOption, bind, EvalResult.bind]
  rfl

theorem evalOfferReceiverIfMakerIsSeller {cfg : Config} {frame : Frame} {evm : State} {offer : OfferData}
    (ho : frame.locals.get? "offer" = some (Model.offerValue offer.value)) :
    evalExpr? cfg frame evm (.field (.var "offer") "receiverIfMakerIsSeller") =
      .ok (.address offer.receiverIfMakerIsSeller) := by
  simp only [evalExpr?, ho, EvalResult.ofOption, bind, EvalResult.bind]
  rfl

theorem evalOfferRatifier {cfg : Config} {frame : Frame} {evm : State} {offer : OfferData}
    (ho : frame.locals.get? "offer" = some (Model.offerValue offer.value)) :
    evalExpr? cfg frame evm (.field (.var "offer") "ratifier") =
      .ok (.address offer.ratifier) := by
  simp only [evalExpr?, ho, EvalResult.ofOption, bind, EvalResult.bind]
  rfl

theorem evalOfferReduceOnly {cfg : Config} {frame : Frame} {evm : State} {offer : OfferData}
    (ho : frame.locals.get? "offer" = some (Model.offerValue offer.value)) :
    evalExpr? cfg frame evm (.field (.var "offer") "reduceOnly") =
      .ok (wordToElem .bool offer.reduceOnly) := by
  simp only [evalExpr?, ho, EvalResult.ofOption, bind, EvalResult.bind]
  rfl

theorem evalOfferMaxUnits {cfg : Config} {frame : Frame} {evm : State} {offer : OfferData}
    (ho : frame.locals.get? "offer" = some (Model.offerValue offer.value)) :
    evalExpr? cfg frame evm (.field (.var "offer") "maxUnits") =
      .ok (.int offer.maxUnits.toNat) := by
  simp only [evalExpr?, ho, EvalResult.ofOption, bind, EvalResult.bind]
  rfl

theorem evalOfferMaxAssets {cfg : Config} {frame : Frame} {evm : State} {offer : OfferData}
    (ho : frame.locals.get? "offer" = some (Model.offerValue offer.value)) :
    evalExpr? cfg frame evm (.field (.var "offer") "maxAssets") =
      .ok (.int offer.maxAssets.toNat) := by
  simp only [evalExpr?, ho, EvalResult.ofOption, bind, EvalResult.bind]
  rfl

theorem evalOfferContinuousFeeCap {cfg : Config} {frame : Frame} {evm : State} {offer : OfferData}
    (ho : frame.locals.get? "offer" = some (Model.offerValue offer.value)) :
    evalExpr? cfg frame evm (.field (.var "offer") "continuousFeeCap") =
      .ok (.int offer.continuousFeeCap.toNat) := by
  simp only [evalExpr?, ho, EvalResult.ofOption, bind, EvalResult.bind]
  rfl

end Benchmarks.Midnight
