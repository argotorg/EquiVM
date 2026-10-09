import Benchmarks.CompoundIII.Comet.ReservesTrace
import Benchmarks.CompoundIII.Comet.TransferInModel
import Benchmarks.CompoundIII.Comet.QuoteTrace
import Benchmarks.CompoundIII.Comet.CollateralReservesTrace
import Benchmarks.CompoundIII.Comet.TransferOutSource
import Benchmarks.CompoundIII.Comet.AuthorizationSource
import Benchmarks.CompoundIII.Comet.ReentrancyModel

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Benchmarks.CompoundIII.Comet.Immutables

namespace Benchmarks.CompoundIII.Comet

def BuyCollateralForSale (v : CometWithExtendedAssetListImmutables) (reserves : UInt256) : Prop :=
  ¬ (0 ≤ signedWord reserves ∧ v.targetReserves.toNat ≤ reserves.toNat)

instance (v : CometWithExtendedAssetListImmutables) (reserves : UInt256) :
    Decidable (BuyCollateralForSale v reserves) := by
  unfold BuyCollateralForSale
  infer_instance

inductive BuyCollateralTransfer (asset recipient : AccountAddress) (amount : UInt256)
    (evm : EVM.State) : InternalOutcome → Prop where
  | tooLarge (hw : ¬ amount.toNat < 2^128) :
      BuyCollateralTransfer asset recipient amount evm .reverted
  | failed (hw : amount.toNat < 2^128) (ht : TransferOutTrace asset recipient amount evm none) :
      BuyCollateralTransfer asset recipient amount evm .reverted
  | done {evm'} (hw : amount.toNat < 2^128)
      (ht : TransferOutTrace asset recipient amount evm (some evm'))
      (hp : evm'.executionEnv.perm = true) :
      BuyCollateralTransfer asset recipient amount evm (.ok (reentrancyState evm' false))

inductive BuyCollateralAfterQuote (asset recipient : AccountAddress) (minimum amount : UInt256)
    (evm : EVM.State) : InternalOutcome → Prop where
  | minimumFailed (hm : ¬ minimum.toNat ≤ amount.toNat) :
      BuyCollateralAfterQuote asset recipient minimum amount evm .reverted
  | reservesFailed (hm : minimum.toNat ≤ amount.toNat)
      (ht : CollateralReservesTrace asset evm none) :
      BuyCollateralAfterQuote asset recipient minimum amount evm .reverted
  | insufficient {evm' reserves} (hm : minimum.toNat ≤ amount.toNat)
      (ht : CollateralReservesTrace asset evm (some (evm', reserves)))
      (hs : ¬ amount.toNat ≤ reserves.toNat) :
      BuyCollateralAfterQuote asset recipient minimum amount evm .reverted
  | transfer {evm' reserves result} (hm : minimum.toNat ≤ amount.toNat)
      (ht : CollateralReservesTrace asset evm (some (evm', reserves)))
      (hs : amount.toNat ≤ reserves.toNat)
      (hn : BuyCollateralTransfer asset recipient amount evm' result) :
      BuyCollateralAfterQuote asset recipient minimum amount evm result

inductive BuyCollateralAfterIn (v : CometWithExtendedAssetListImmutables)
    (asset recipient : AccountAddress) (minimum received : UInt256) (evm : EVM.State) :
    InternalOutcome → Prop where
  | failed (ht : QuoteTrace v asset received evm none) :
      BuyCollateralAfterIn v asset recipient minimum received evm .reverted
  | quote {evm' amount result} (ht : QuoteTrace v asset received evm (some (evm', amount)))
      (hn : BuyCollateralAfterQuote asset recipient minimum amount evm' result) :
      BuyCollateralAfterIn v asset recipient minimum received evm result

inductive BuyCollateralAfterReserves (v : CometWithExtendedAssetListImmutables)
    (asset recipient : AccountAddress) (minimum base reserves : UInt256) (evm : EVM.State) :
    InternalOutcome → Prop where
  | notForSale (hv : ¬ BuyCollateralForSale v reserves) :
      BuyCollateralAfterReserves v asset recipient minimum base reserves evm .reverted
  | failed (hv : BuyCollateralForSale v reserves)
      (ht : TransferInTrace v.baseToken evm.executionEnv.source base evm none) :
      BuyCollateralAfterReserves v asset recipient minimum base reserves evm .reverted
  | received {evm' amount result} (hv : BuyCollateralForSale v reserves)
      (ht : TransferInTrace v.baseToken evm.executionEnv.source base evm (some (evm', amount)))
      (hn : BuyCollateralAfterIn v asset recipient minimum amount evm' result) :
      BuyCollateralAfterReserves v asset recipient minimum base reserves evm result

inductive BuyCollateralAfterLock (v : CometWithExtendedAssetListImmutables)
    (asset recipient : AccountAddress) (minimum base : UInt256) (evm : EVM.State) :
    InternalOutcome → Prop where
  | paused (hp : (pauseBitWord evm ⟨4, by decide⟩).toNat ≠ 0) :
      BuyCollateralAfterLock v asset recipient minimum base evm .reverted
  | failed (hp : (pauseBitWord evm ⟨4, by decide⟩).toNat = 0)
      (ht : ReservesTrace v evm none) :
      BuyCollateralAfterLock v asset recipient minimum base evm .reverted
  | reserves {evm' reserves result} (hp : (pauseBitWord evm ⟨4, by decide⟩).toNat = 0)
      (ht : ReservesTrace v evm (some (evm', reserves)))
      (hn : BuyCollateralAfterReserves v asset recipient minimum base reserves evm' result) :
      BuyCollateralAfterLock v asset recipient minimum base evm result

inductive BuyCollateralTrace (v : CometWithExtendedAssetListImmutables)
    (asset recipient : AccountAddress) (minimum base : UInt256) (evm : EVM.State) :
    InternalOutcome → Prop where
  | reverted (he : reentrancyOutcome evm true = .reverted) :
      BuyCollateralTrace v asset recipient minimum base evm .reverted
  | staticViolation (he : reentrancyOutcome evm true = .staticViolation) :
      BuyCollateralTrace v asset recipient minimum base evm .staticViolation
  | done {evm' result} (he : reentrancyOutcome evm true = .ok evm')
      (ht : BuyCollateralAfterLock v asset recipient minimum base evm' result) :
      BuyCollateralTrace v asset recipient minimum base evm result

def buyCollateralForSaleExpr : Expr :=
  .unary .not (.binary .and (.binary .ge (.var "reserves") (.intLit 0))
    (.binary .ge (.cast (.var "reserves") (.elem (.int (.uint ⟨256, by decide⟩))))
      (.immutable "targetReserves")))

def buyCollateralTransferBody : List Stmt :=
  [.internalCall "safe128" [.var "collateralAmount"] "__c6",
    .internalCall "doTransferOut" [.var "asset", .var "recipient", .var "__c6"] "__c7",
    .emit "BuyCollateral" [.env .caller, .var "asset", .var "baseAmount", .var "collateralAmount"],
    .internalCall "nonReentrantAfter" [] "__c8"]

def buyCollateralAfterQuoteBody : List Stmt :=
  [.require (.binary .ge (.var "collateralAmount") (.var "minAmount")),
    .internalCall "getCollateralReserves_body" [.var "asset"] "__c5",
    .require (.binary .le (.var "collateralAmount") (.var "__c5"))] ++ buyCollateralTransferBody

def buyCollateralAfterInBody : List Stmt :=
  .internalCall "quoteCollateral_body" [.var "asset", .var "baseAmount"] "collateralAmount" ::
    buyCollateralAfterQuoteBody

def buyCollateralAfterReservesBody : List Stmt :=
  [.require buyCollateralForSaleExpr,
    .internalCall "doTransferIn" [.immutable "baseToken", .env .caller, .var "baseAmount"] "__c3",
    .assign .localVar ⟨"baseAmount", []⟩ (.var "__c3")] ++ buyCollateralAfterInBody

def buyCollateralAfterLockBody : List Stmt :=
  [.internalCall "isBuyPaused_body" [] "__c1", .require (.unary .not (.var "__c1")),
    .internalCall "getReserves_body" [] "reserves"] ++ buyCollateralAfterReservesBody

def buyCollateralBody : List Stmt :=
  .internalCall "nonReentrantBefore" [] "__c0" :: buyCollateralAfterLockBody

theorem buyCollateralTransition_body :
    buyCollateralTransition.body = calldataPrologue buyCollateralBody := rfl

end Benchmarks.CompoundIII.Comet
