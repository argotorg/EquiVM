import Benchmarks.Midnight.TakeAccounting
import Benchmarks.Midnight.TransferHeap
import Benchmarks.Midnight.InitMarketDefaultsSource

/-! Source argument lists for the fee transfer and seller payment. -/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Midnight

def takeFeeTransferArgs : List Expr :=
  [.field (.field (.var "offer") "market") "loanToken", .var "payer", .env .this,
    takeAssetDifferenceExpr]

def takeSellerTransferArgs : List Expr :=
  [.field (.field (.var "offer") "market") "loanToken", .var "payer", .var "receiver",
    .var "sellerAssets"]

theorem takeTransfers_shape : takeTransition.body.drop 68 =
    .internalCall "SafeTransferLib_safeTransferFrom" takeFeeTransferArgs "__c28" ::
    .internalCall "SafeTransferLib_safeTransferFrom" takeSellerTransferArgs "__c29" ::
    takeTransition.body.drop 70 := rfl

theorem takeFeeTransferArgs_eval {frame : Frame} {evm : State} {offer : OfferData}
    {bought sold : UInt256} {payer : AccountAddress}
    (ho : frame.locals.get? "offer" = some (Model.offerValue offer.value))
    (hp : frame.locals.get? "payer" = some (.address payer))
    (hb : frame.locals.get? "buyerAssets" = some (.int bought.toNat))
    (hs : frame.locals.get? "sellerAssets" = some (.int sold.toNat))
    (hle : sold.toNat ≤ bought.toNat) :
    evalExprs? config frame evm takeFeeTransferArgs =
      .ok [.address offer.market.loanToken, .address payer,
        .address evm.executionEnv.codeOwner, .int (UInt256.sub bought sold).toNat] := by
  have he : evalExpr? config frame evm takeAssetDifferenceExpr =
      .ok (.int (UInt256.sub bought sold).toNat) :=
    uint256RangeSourceOk (subSourceOk (evalWordLocal hb) (evalWordLocal hs) hle)
      (UInt256.sub bought sold).val.isLt
  simp only [takeFeeTransferArgs, evalExprs?, evalOfferLoanToken ho, he,
    evalExpr?, hp, envValue, EvalResult.ofOption, EvalResult.bind, bind, pure]

theorem takeSellerTransferArgs_eval {frame : Frame} {evm : State} {offer : OfferData}
    {sold : UInt256} {payer receiver : AccountAddress}
    (ho : frame.locals.get? "offer" = some (Model.offerValue offer.value))
    (hp : frame.locals.get? "payer" = some (.address payer))
    (hr : frame.locals.get? "receiver" = some (.address receiver))
    (hs : frame.locals.get? "sellerAssets" = some (.int sold.toNat)) :
    evalExprs? config frame evm takeSellerTransferArgs =
      .ok [.address offer.market.loanToken, .address payer, .address receiver, .int sold.toNat] := by
  simp only [takeSellerTransferArgs, evalExprs?, evalOfferLoanToken ho,
    evalExpr?, hp, hr, hs, EvalResult.ofOption, EvalResult.bind, bind, pure]

end Benchmarks.Midnight
