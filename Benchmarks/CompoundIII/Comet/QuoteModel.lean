import Benchmarks.CompoundIII.Comet.AssetSearch
import Benchmarks.CompoundIII.Comet.ArithmeticSource
import Benchmarks.CompoundIII.Comet.NarrowArithmetic
import Benchmarks.CompoundIII.Comet.PriceSource

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Benchmarks.CompoundIII.Comet.Immutables

namespace Benchmarks.CompoundIII.Comet

def quoteFactorScale : UInt256 := ⟨1000000000000000000⟩

def quoteDiscountFactor (v : CometWithExtendedAssetListImmutables)
    (assetOut : ByteArray) : UInt256 :=
  mulFactorWord v.storeFrontPriceFactor (UInt256.sub quoteFactorScale (calldataWord assetOut 192))

def quoteDiscountedPrice (v : CometWithExtendedAssetListImmutables)
    (assetOut : ByteArray) (price : UInt256) : UInt256 :=
  mulFactorWord price (UInt256.sub quoteFactorScale (quoteDiscountFactor v assetOut))

def QuoteDiscountValid (v : CometWithExtendedAssetListImmutables)
    (assetOut : ByteArray) (price : UInt256) : Prop :=
  (calldataWord assetOut 192).toNat ≤ quoteFactorScale.toNat ∧
  v.storeFrontPriceFactor.toNat *
    (UInt256.sub quoteFactorScale (calldataWord assetOut 192)).toNat < UInt256.size ∧
  (quoteDiscountFactor v assetOut).toNat ≤ quoteFactorScale.toNat ∧
  price.toNat * (UInt256.sub quoteFactorScale (quoteDiscountFactor v assetOut)).toNat < UInt256.size

instance (v : CometWithExtendedAssetListImmutables) (out : ByteArray) (price : UInt256) :
    Decidable (QuoteDiscountValid v out price) := inferInstanceAs (Decidable (_ ∧ _ ∧ _ ∧ _))

def quoteResultWord (v : CometWithExtendedAssetListImmutables)
    (assetOut : ByteArray) (amount price discounted : UInt256) : UInt256 :=
  UInt256.div (UInt256.div (UInt256.mul (UInt256.mul price amount) (calldataWord assetOut 96))
    discounted) v.baseScale

def QuoteResultValid (v : CometWithExtendedAssetListImmutables)
    (assetOut : ByteArray) (amount price discounted : UInt256) : Prop :=
  price.toNat * amount.toNat < UInt256.size ∧
  (UInt256.mul price amount).toNat * (calldataWord assetOut 96).toNat < UInt256.size ∧
  discounted ≠ ⟨0⟩ ∧ v.baseScale ≠ ⟨0⟩

instance (v : CometWithExtendedAssetListImmutables) (out : ByteArray) (amount price d : UInt256) :
    Decidable (QuoteResultValid v out amount price d) := inferInstanceAs (Decidable (_ ∧ _ ∧ _ ∧ _))

def quoteDiscountBlock : List Stmt :=
  [.internalCall "mulFactor" [.immutable "storeFrontPriceFactor",
      .inRange (.uint ⟨64, by decide⟩) (.binary .sub (.intLit 1000000000000000000)
        (.field (.var "assetInfo") "liquidationFactor"))] "discountFactor",
    .internalCall "mulFactor" [.var "assetPrice",
      .inRange (.uint ⟨256, by decide⟩) (.binary .sub (.intLit 1000000000000000000)
        (.var "discountFactor"))] "assetPriceDiscounted"]

def quoteResultExpr : Expr :=
  .binary .div (.binary .div
    (.inRange (.uint ⟨256, by decide⟩) (.binary .mul
      (.inRange (.uint ⟨256, by decide⟩) (.binary .mul (.var "basePrice") (.var "baseAmount")))
      (.field (.var "assetInfo") "scale"))) (.var "assetPriceDiscounted")) (.immutable "baseScale")

def quoteTailBlock : List Stmt := quoteDiscountBlock ++
  [.internalCall "getPrice_body" [.immutable "baseTokenPriceFeed"] "basePrice",
    .return [quoteResultExpr]]

def quoteAfterAssetBlock : List Stmt :=
  .internalCall "getPrice_body" [.field (.var "assetInfo") "priceFeed"] "assetPrice" ::
    quoteTailBlock

def quoteCallable : CallableDecl :=
  { params := [⟨"asset", abiAddress⟩, ⟨"baseAmount", abiUInt256⟩], returnType := [abiUInt256],
    body := .internalCall "getAssetInfoByAddress_body" [.var "asset"] "assetInfo" ::
      quoteAfterAssetBlock }

theorem quoteCallable_lookup :
    lookupCallable? contract "quoteCollateral_body" = some quoteCallable := rfl

def quoteEntry (v : CometWithExtendedAssetListImmutables) (asset : AccountAddress)
    (amount : UInt256) : Frame :=
  { contract := contract, immutables := immStore v,
    locals :=
      ((∅ : Store).insert "baseAmount" (.int amount.toNat)).insert "asset" (.address asset) }

def quoteAssetFrame (v : CometWithExtendedAssetListImmutables) (asset : AccountAddress)
    (amount : UInt256) (out : ByteArray) : Frame :=
  { quoteEntry v asset amount with
    locals := (quoteEntry v asset amount).locals.insert "assetInfo" (assetValue out) }

def quotePriceFrame (v : CometWithExtendedAssetListImmutables) (asset : AccountAddress)
    (amount : UInt256) (out : ByteArray) (price : UInt256) : Frame :=
  { quoteAssetFrame v asset amount out with
    locals := (quoteAssetFrame v asset amount out).locals.insert "assetPrice" (.int price.toNat) }

def quoteDiscountFrame (v : CometWithExtendedAssetListImmutables) (asset : AccountAddress)
    (amount : UInt256) (out : ByteArray) (price : UInt256) : Frame :=
  { quotePriceFrame v asset amount out price with
    locals := ((quotePriceFrame v asset amount out price).locals.insert
      "discountFactor" (.int (quoteDiscountFactor v out).toNat)).insert
      "assetPriceDiscounted" (.int (quoteDiscountedPrice v out price).toNat) }

def quoteFinalFrame (v : CometWithExtendedAssetListImmutables) (asset : AccountAddress)
    (amount : UInt256) (out : ByteArray) (assetPrice basePrice : UInt256) : Frame :=
  { quoteDiscountFrame v asset amount out assetPrice with
    locals := (quoteDiscountFrame v asset amount out assetPrice).locals.insert
      "basePrice" (.int basePrice.toNat) }

end Benchmarks.CompoundIII.Comet
