import Benchmarks.Midnight.TakeEventArithmetic
import Benchmarks.Midnight.OfferBytesSource

/-! Evaluation of the trade event, including its checked signed credit difference. -/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Midnight

set_option maxRecDepth 10000

def takeEventArgs : List Expr :=
  [.env .caller, .keccak256 (.var "encodedOffer"), .var "id", .field (.var "offer") "buy",
    .field (.var "offer") "maker", .field (.var "offer") "group",
    .field (.var "offer") "ratifier", .var "ratifierData", .var "units", .var "taker",
    .var "buyerAssets", .var "sellerAssets", .var "newConsumed", .var "buyerPendingFeeIncrease",
    .var "sellerPendingFeeDecrease", takeCreditDifferenceExpr, .var "receiver", .var "payer"]

theorem takeEvent_shape : takeTransition.body.drop 65 =
    .emit "Take" takeEventArgs :: takeTransition.body.drop 66 := rfl

theorem takeEventArgs_eval {frame : Frame} {evm : State} {offer : OfferData}
    {id units taker bought sold consumed buyerFee sellerFee increase decrease : UInt256}
    {receiver callback recipient payer : AccountAddress} {ratifierData data encoded : ByteArray}
    (hf : TakeSourceFrame frame offer id units taker receiver callback ratifierData data)
    (he : frame.locals.get? "encodedOffer" = some (.bytes encoded))
    (hb : frame.locals.get? "buyerAssets" = some (.int bought.toNat))
    (hs : frame.locals.get? "sellerAssets" = some (.int sold.toNat))
    (hn : frame.locals.get? "newConsumed" = some (.int consumed.toNat))
    (hbf : frame.locals.get? "buyerPendingFeeIncrease" = some (.int buyerFee.toNat))
    (hsf : frame.locals.get? "sellerPendingFeeDecrease" = some (.int sellerFee.toNat))
    (hi : frame.locals.get? "buyerCreditIncrease" = some (.int increase.toNat))
    (hd : frame.locals.get? "sellerCreditDecrease" = some (.int decrease.toNat))
    (hr : frame.locals.get? "receiver" = some (.address recipient))
    (hp : frame.locals.get? "payer" = some (.address payer))
    (hi128 : increase.toNat < 2^128) (hd128 : decrease.toNat < 2^128) :
    evalExprs? config frame evm takeEventArgs = .ok
      [.address evm.executionEnv.source, .fixedBytes ⟨31, by decide⟩ (KEC encoded).toList,
        wordBytes32Value id, wordToElem .bool offer.buy, .address offer.maker,
        wordBytes32Value offer.group, .address offer.ratifier, .bytes ratifierData,
        .int units.toNat, .address (AccountAddress.ofNat taker.toNat), .int bought.toNat,
        .int sold.toNat, .int consumed.toNat, .int buyerFee.toNat, .int sellerFee.toNat,
        .int ((increase.toNat : Int) - decrease.toNat), .address recipient, .address payer] := by
  simp only [takeEventArgs, evalExprs?, evalTakeCreditDifference hi hd hi128 hd128,
    evalOfferBuy hf.offerValue, evalOfferMaker hf.offerValue, evalOfferGroup hf.offerValue,
    evalOfferRatifier hf.offerValue, evalExpr?, envValue, hf.idValue, hf.ratifierData,
    hf.units, hf.taker, he, hb, hs, hn, hbf, hsf, hr, hp,
    EvalResult.ofOption, EvalResult.bind, bind, pure]

end Benchmarks.Midnight
