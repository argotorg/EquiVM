import Benchmarks.CompoundIII.Comet.QuoteModel

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Benchmarks.CompoundIII.Comet.Immutables

namespace Benchmarks.CompoundIII.Comet

/-- The second price query and the arithmetic guards after the first price is known. -/
inductive QuoteFinish (v : CometWithExtendedAssetListImmutables) (assetOut : ByteArray)
    (amount assetPrice : UInt256) : EVM.State → Option (EVM.State × UInt256) → Prop where
  | discountFailed {evm} (hd : ¬ QuoteDiscountValid v assetOut assetPrice) :
      QuoteFinish v assetOut amount assetPrice evm none
  | priceFailed {evm evm' z out} (hd : QuoteDiscountValid v assetOut assetPrice)
      (hc : callViaEVM evm v.baseTokenPriceFeed 0 pricePayload (z, evm', out) false)
      (hh : out.size < 2^255) (hv : ¬ (z = true ∧ PriceValid out)) :
      QuoteFinish v assetOut amount assetPrice evm none
  | result {evm evm' out} (hd : QuoteDiscountValid v assetOut assetPrice)
      (hc : callViaEVM evm v.baseTokenPriceFeed 0 pricePayload (true, evm', out) false)
      (hh : out.size < 2^255) (hv : PriceValid out) :
      QuoteFinish v assetOut amount assetPrice evm
        (if QuoteResultValid v assetOut amount (calldataWord out 32)
            (quoteDiscountedPrice v assetOut assetPrice) then
          some (evm', quoteResultWord v assetOut amount (calldataWord out 32)
            (quoteDiscountedPrice v assetOut assetPrice)) else none)

/-- The first price query, after the asset-address search succeeds. -/
inductive QuoteAfterAsset (v : CometWithExtendedAssetListImmutables) (assetOut : ByteArray)
    (amount : UInt256) : EVM.State → Option (EVM.State × UInt256) → Prop where
  | priceFailed {evm evm' z out}
      (hc : callViaEVM evm (AccountAddress.ofNat (calldataWord assetOut 64).toNat) 0
        pricePayload (z, evm', out) false)
      (hh : out.size < 2^255) (hv : ¬ (z = true ∧ PriceValid out)) :
      QuoteAfterAsset v assetOut amount evm none
  | priceOk {evm evm' out result}
      (hc : callViaEVM evm (AccountAddress.ofNat (calldataWord assetOut 64).toNat) 0
        pricePayload (true, evm', out) false)
      (hh : out.size < 2^255) (hv : PriceValid out)
      (ht : QuoteFinish v assetOut amount (calldataWord out 32) evm' result) :
      QuoteAfterAsset v assetOut amount evm result

/-- The opaque external-call trace of `quoteCollateral`, including every revert path. -/
inductive QuoteTrace (v : CometWithExtendedAssetListImmutables) (asset : AccountAddress)
    (amount : UInt256) : EVM.State → Option (EVM.State × UInt256) → Prop where
  | assetFailed {evm} (hs : AssetSearch v asset 0 evm none) : QuoteTrace v asset amount evm none
  | assetOk {evm evm' out result} (hs : AssetSearch v asset 0 evm (some (evm', out)))
      (ht : QuoteAfterAsset v out amount evm' result) : QuoteTrace v asset amount evm result

def QuoteSourceResult (frame : Frame) (evm : EVM.State) (body : List Stmt)
    (result : Option (EVM.State × UInt256)) : Prop :=
  match result with
  | none => ExecBlock config frame evm body .reverted
  | some (evm', value) => ∃ final, ExecBlock config frame evm body
      (.returned final evm' (some [.int value.toNat]))

end Benchmarks.CompoundIII.Comet
