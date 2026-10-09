import Benchmarks.CompoundIII.Comet.CollateralMath
import Benchmarks.CompoundIII.Comet.UserCollateralRead
import Benchmarks.CompoundIII.Comet.PriceSource

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Benchmarks.CompoundIII.Comet.Immutables

namespace Benchmarks.CompoundIII.Comet

def collateralBalanceWord (evm : EVM.State) (account : AccountAddress)
    (assetOut : ByteArray) : UInt256 :=
  low128 (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner
    (userCollateralSlot account (AccountAddress.ofNat (calldataWord assetOut 32).toNat)))

structure CollateralValueData where
  assetOut : ByteArray
  amount : UInt256
  price : UInt256

def CollateralValueData.value (d : CollateralValueData) (borrow : Bool) : UInt256 :=
  collateralValueWord borrow d.amount d.price d.assetOut

def collateralAssetFrame (frame : Frame) (out : ByteArray) : Frame :=
  { frame with locals := frame.locals.insert "asset" (assetValue out) }

def collateralBalanceFrame (frame : Frame) (out : ByteArray) (amount : UInt256) : Frame :=
  let f := collateralAssetFrame frame out
  { f with locals := f.locals.insert "collateralBalance" (.int amount.toNat) }

def collateralPriceFrame (frame : Frame) (out : ByteArray) (amount price : UInt256) : Frame :=
  let f := collateralBalanceFrame frame out amount
  { f with locals := f.locals.insert "__c5" (.int price.toNat) }

def collateralValueFrame (frame : Frame) (borrow : Bool) (d : CollateralValueData) : Frame :=
  collateralMathFinal (collateralPriceFrame frame d.assetOut d.amount d.price)
    borrow d.amount d.price d.assetOut

def collateralBalanceExpr : Expr :=
  .storage ⟨"userCollateral", [.mindex (.var "account"),
    .mindex (.field (.var "asset") "asset"), .field "balance"]⟩

def collateralAfterAssetBlock (borrow : Bool) : List Stmt :=
  [.letDecl "collateralBalance" (some (.elem (.int (.uint ⟨128, by decide⟩))))
      collateralBalanceExpr,
    .internalCall "getPrice_body" [.field (.var "asset") "priceFeed"] "__c5"] ++
    collateralMathBlock borrow

def collateralValueBlock (borrow : Bool) : List Stmt :=
  .internalCall "getAssetInfo_body" [.var "i"] "asset" :: collateralAfterAssetBlock borrow

/-- The price query uses the balance read before that external call. -/
inductive CollateralAfterAsset (borrow : Bool) (assetOut : ByteArray) (amount : UInt256) :
    EVM.State → Option (EVM.State × CollateralValueData) → Prop where
  | priceFailed {evm evm' z out}
      (hc : callViaEVM evm (AccountAddress.ofNat (calldataWord assetOut 64).toNat) 0
        pricePayload (z, evm', out) false)
      (hh : out.size < 2^255) (hv : ¬ (z = true ∧ PriceValid out)) :
      CollateralAfterAsset borrow assetOut amount evm none
  | result {evm evm' out}
      (hc : callViaEVM evm (AccountAddress.ofNat (calldataWord assetOut 64).toNat) 0
        pricePayload (true, evm', out) false)
      (hh : out.size < 2^255) (hv : PriceValid out) :
      CollateralAfterAsset borrow assetOut amount evm
        (if CollateralMathValid borrow amount (calldataWord out 32) assetOut then
          some (evm', ⟨assetOut, amount, calldataWord out 32⟩) else none)

/-- One selected collateral asset, including malformed responses and arithmetic reverts. -/
inductive CollateralValueTrace (v : CometWithExtendedAssetListImmutables)
    (borrow : Bool) (account : AccountAddress) (i : UInt256) :
    EVM.State → Option (EVM.State × CollateralValueData) → Prop where
  | assetFailed {evm evm' z out}
      (hc : callViaEVM evm v.assetList 0 (assetPayload i) (z, evm', out) false)
      (hh : out.size < 2^255) (hv : ¬ (z = true ∧ AssetValid out)) :
      CollateralValueTrace v borrow account i evm none
  | assetOk {evm evm' out result}
      (hc : callViaEVM evm v.assetList 0 (assetPayload i) (true, evm', out) false)
      (hh : out.size < 2^255) (hv : AssetValid out)
      (ht : CollateralAfterAsset borrow out (collateralBalanceWord evm' account out)
        evm' result) :
      CollateralValueTrace v borrow account i evm result

def CollateralValueSourceResult (frame : Frame) (evm : EVM.State) (borrow : Bool)
    (body : List Stmt) (result : Option (EVM.State × CollateralValueData)) : Prop :=
  match result with
  | none => ExecBlock config frame evm body .reverted
  | some (evm', d) => ExecBlock config frame evm body
      (.ok (collateralValueFrame frame borrow d) evm')

end Benchmarks.CompoundIII.Comet
