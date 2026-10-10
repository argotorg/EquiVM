import Benchmarks.CompoundIII.Comet.CollateralLoopSource
import Benchmarks.CompoundIII.Comet.SignedPresentValueSource
import Benchmarks.CompoundIII.Comet.SignedMulPriceSource
import Benchmarks.CompoundIII.Comet.UserBasicRead
import Benchmarks.CompoundIII.Comet.UintCastWord

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Benchmarks.CompoundIII.Comet.Immutables

namespace Benchmarks.CompoundIII.Comet

def collateralBasicWord (evm : EVM.State) (account : AccountAddress) : UInt256 :=
  Solm.EVM.storageLoad evm evm.executionEnv.codeOwner (userBasicSlot account)

def collateralBaseScale (v : CometWithExtendedAssetListImmutables) : UInt256 :=
  uintCastWord ⟨64, by decide⟩ v.baseScale

def collateralCheckName (borrow : Bool) : Ident :=
  if borrow then "isBorrowCollateralized_body" else "isLiquidatable_body"

def collateralPrincipalExpr : Expr :=
  .storage ⟨"userBasic", [.mindex (.var "account"), .field "principal"]⟩

def collateralBasicExpr (name : Ident) : Expr :=
  .storage ⟨"userBasic", [.mindex (.var "account"), .field name]⟩

def collateralPrincipalCond : Expr := .binary .ge (.var "principal") (.intLit 0)

def collateralBitsBlock : List Stmt :=
  [.letDecl "assetsIn" (some (.elem (.int (.uint ⟨16, by decide⟩))))
      (collateralBasicExpr "assetsIn"),
    .letDecl "_reserved" (some (.elem (.int (.uint ⟨8, by decide⟩))))
      (collateralBasicExpr "_reserved")]

def collateralDebtPrefix : List Stmt :=
  collateralBitsBlock ++ [.internalCall "presentValue" [.var "principal"] "__c0"]

def collateralDebtPriceBlock : List Stmt :=
  [.internalCall "getPrice_body" [.immutable "baseTokenPriceFeed"] "__c1",
    .internalCall "signedMulPrice" [.var "__c0", .var "__c1",
      .cast (.immutable "baseScale") (.elem (.int (.uint ⟨64, by decide⟩)))] "liquidity"]

def collateralDebtTail (borrow : Bool) : List Stmt :=
  collateralDebtPriceBlock ++
    [.letDecl "i" (some (.elem (.int (.uint ⟨8, by decide⟩)))) (.intLit 0)] ++
    collateralLoopTail borrow

def collateralCheckCallable (borrow : Bool) : CallableDecl :=
  { params := [⟨"account", abiAddress⟩], returnType := [.elem .bool],
    body := .letDecl "principal" (some (.elem (.int (.sint ⟨104, by decide⟩))))
        collateralPrincipalExpr ::
      .ite collateralPrincipalCond [.return [.boolLit borrow]] [] ::
      (collateralBitsBlock ++ (.internalCall "presentValue" [.var "principal"] "__c0" ::
        collateralDebtTail borrow)) }

theorem collateralCheckCallable_lookup (borrow : Bool) :
    lookupCallable? contract (collateralCheckName borrow) = some (collateralCheckCallable borrow) := by
  cases borrow <;> rfl

def collateralCheckEntry (v : CometWithExtendedAssetListImmutables)
    (account : AccountAddress) : Frame :=
  { contract := contract, immutables := immStore v,
    locals := (∅ : Store).insert "account" (.address account) }

def collateralPrincipalFrame (v : CometWithExtendedAssetListImmutables)
    (account : AccountAddress) (basic : UInt256) : Frame :=
  let f := collateralCheckEntry v account
  { f with locals := f.locals.insert "principal" (.int (signed104 basic)) }

def collateralBitsFrame (v : CometWithExtendedAssetListImmutables)
    (account : AccountAddress) (basic : UInt256) : Frame :=
  let f := collateralPrincipalFrame v account basic
  { f with
    locals := (f.locals.insert "assetsIn" (.int (userBasicFieldWord basic 2).toNat)).insert
      "_reserved" (.int (userBasicFieldWord basic 3).toNat) }

def collateralPresentFrame (v : CometWithExtendedAssetListImmutables)
    (account : AccountAddress) (basic magnitude : UInt256) : Frame :=
  let f := collateralBitsFrame v account basic
  { f with locals := f.locals.insert "__c0" (.int (-Int.ofNat magnitude.toNat)) }

def collateralBasePriceFrame (v : CometWithExtendedAssetListImmutables)
    (account : AccountAddress) (basic magnitude price : UInt256) : Frame :=
  let f := collateralPresentFrame v account basic magnitude
  { f with locals := f.locals.insert "__c1" (.int price.toNat) }

def collateralLiquidityFrame (v : CometWithExtendedAssetListImmutables)
    (account : AccountAddress) (basic magnitude price : UInt256) : Frame :=
  let f := collateralBasePriceFrame v account basic magnitude price
  { f with
    locals := f.locals.insert "liquidity"
      (.int (signedDebtPriceInt magnitude price (collateralBaseScale v))) }

def collateralInitialFrame (v : CometWithExtendedAssetListImmutables)
    (account : AccountAddress) (basic magnitude price : UInt256) : Frame :=
  let f := collateralLiquidityFrame v account basic magnitude price
  { f with locals := f.locals.insert "i" (.int 0) }

inductive CollateralDebtTrace (v : CometWithExtendedAssetListImmutables) (borrow : Bool)
    (account : AccountAddress) (basic magnitude : UInt256) :
    EVM.State → Option (EVM.State × Bool) → Prop where
  | priceFailed {evm evm' z out}
      (hc : callViaEVM evm v.baseTokenPriceFeed 0 pricePayload (z, evm', out) false)
      (hh : out.size < 2^255) (hv : ¬ (z = true ∧ PriceValid out)) :
      CollateralDebtTrace v borrow account basic magnitude evm none
  | mathFailed {evm evm' out}
      (hc : callViaEVM evm v.baseTokenPriceFeed 0 pricePayload (true, evm', out) false)
      (hh : out.size < 2^255) (hv : PriceValid out)
      (hm : ¬ signedDebtPriceValid magnitude (calldataWord out 32) (collateralBaseScale v)) :
      CollateralDebtTrace v borrow account basic magnitude evm none
  | loop {evm evm' out result}
      (hc : callViaEVM evm v.baseTokenPriceFeed 0 pricePayload (true, evm', out) false)
      (hh : out.size < 2^255) (hv : PriceValid out)
      (hm : signedDebtPriceValid magnitude (calldataWord out 32) (collateralBaseScale v))
      (ht : CollateralLoopTrace v borrow account (userBasicFieldWord basic 2)
        (userBasicFieldWord basic 3) 0
        (signedDebtPriceWord magnitude (calldataWord out 32) (collateralBaseScale v)) evm' result) :
      CollateralDebtTrace v borrow account basic magnitude evm result

inductive CollateralCheckTrace (v : CometWithExtendedAssetListImmutables) (borrow : Bool)
    (account : AccountAddress) : EVM.State → Option (EVM.State × Bool) → Prop where
  | solvent {evm} (hp : 0 ≤ signed104 (collateralBasicWord evm account)) :
      CollateralCheckTrace v borrow account evm (some (evm, borrow))
  | minimum {evm} (hp : signed104 (collateralBasicWord evm account) < 0)
      (hm : ¬ -(2^103 : Int) < signed104 (collateralBasicWord evm account)) :
      CollateralCheckTrace v borrow account evm none
  | debt {evm result} (hp : signed104 (collateralBasicWord evm account) < 0)
      (hm : -(2^103 : Int) < signed104 (collateralBasicWord evm account))
      (ht : CollateralDebtTrace v borrow account (collateralBasicWord evm account)
        (signedPresentMagnitude evm (collateralBasicWord evm account) true) evm result) :
      CollateralCheckTrace v borrow account evm result

end Benchmarks.CompoundIII.Comet
