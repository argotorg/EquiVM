import Benchmarks.CompoundIII.Comet.CollateralMath
import Benchmarks.CompoundIII.Comet.UserCollateralRead
import Benchmarks.CompoundIII.Comet.PriceSource

variable {fork : Ethereum.Fork}

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Benchmarks.CompoundIII.Comet.Immutables

namespace Benchmarks.CompoundIII.Comet

def collateralBalanceWord (evm : EVM.State) (account : AccountAddress)
    (assetOut : ByteArray) : UInt256 :=
  low128 (Stele.EVM.storageLoad evm evm.executionEnv.codeOwner
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
inductive CollateralAfterAsset (fork : Ethereum.Fork) (borrow : Bool) (assetOut : ByteArray) (amount : UInt256) :
    EVM.State → Option (EVM.State × CollateralValueData) → Prop where
  | priceFailed {evm evm' z out}
      (hc : callViaEVM fork evm (AccountAddress.ofNat (calldataWord assetOut 64).toNat) 0
        pricePayload (z, evm', out) false)
      (hh : out.size < 2^255) (hv : ¬ (z = true ∧ PriceValid out)) :
      CollateralAfterAsset fork borrow assetOut amount evm none
  | result {evm evm' out}
      (hc : callViaEVM fork evm (AccountAddress.ofNat (calldataWord assetOut 64).toNat) 0
        pricePayload (true, evm', out) false)
      (hh : out.size < 2^255) (hv : PriceValid out) :
      CollateralAfterAsset fork borrow assetOut amount evm
        (if CollateralMathValid borrow amount (calldataWord out 32) assetOut then
          some (evm', ⟨assetOut, amount, calldataWord out 32⟩) else none)

/-- One selected collateral asset, including malformed responses and arithmetic reverts. -/
inductive CollateralValueTrace (fork : Ethereum.Fork) (v : CometWithExtendedAssetListImmutables)
    (borrow : Bool) (account : AccountAddress) (i : UInt256) :
    EVM.State → Option (EVM.State × CollateralValueData) → Prop where
  | assetFailed {evm evm' z out}
      (hc : callViaEVM fork evm v.assetList 0 (assetPayload i) (z, evm', out) false)
      (hh : out.size < 2^255) (hv : ¬ (z = true ∧ AssetValid out)) :
      CollateralValueTrace fork v borrow account i evm none
  | assetOk {evm evm' out result}
      (hc : callViaEVM fork evm v.assetList 0 (assetPayload i) (true, evm', out) false)
      (hh : out.size < 2^255) (hv : AssetValid out)
      (ht : CollateralAfterAsset fork borrow out (collateralBalanceWord evm' account out)
        evm' result) :
      CollateralValueTrace fork v borrow account i evm result

def CollateralValueSourceResult (fork : Ethereum.Fork) (frame : Frame) (evm : EVM.State) (borrow : Bool)
    (body : List Stmt) (result : Option (EVM.State × CollateralValueData)) : Prop :=
  match result with
  | none => ExecBlock fork config frame evm body .reverted
  | some (evm', d) => ExecBlock fork config frame evm body
      (.ok (collateralValueFrame frame borrow d) evm')

theorem CollateralAfterAsset.executionEnv_eq {borrow assetOut amount evm result}
    (ht : CollateralAfterAsset fork borrow assetOut amount evm result) :
    ∀ evm' d, result = some (evm', d) → evm'.executionEnv = evm.executionEnv := by
  cases ht with
  | priceFailed _ _ _ => intro evm' d he; cases he
  | result hc _ _ =>
    intro evm' d he
    split at he
    · cases he
      exact callViaEVM_executionEnv_eq hc
    · cases he

theorem CollateralValueTrace.executionEnv_eq {v borrow account i evm result}
    (ht : CollateralValueTrace fork v borrow account i evm result) :
    ∀ evm' d, result = some (evm', d) → evm'.executionEnv = evm.executionEnv := by
  cases ht with
  | assetFailed _ _ _ => intro evm' d he; cases he
  | assetOk hc _ _ ht =>
    intro evm' d he
    exact (ht.executionEnv_eq evm' d he).trans (callViaEVM_executionEnv_eq hc)

end Benchmarks.CompoundIII.Comet
