import Benchmarks.CompoundIII.Comet.TotalsCollateralData
import Benchmarks.CompoundIII.Comet.WithdrawCollateralModel
import Benchmarks.CompoundIII.Comet.TransferInModel

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Benchmarks.CompoundIII.Comet.Immutables

namespace Benchmarks.CompoundIII.Comet

def supplyCollateralReserved (evm : EVM.State) (asset : AccountAddress) : UInt256 :=
  high128 (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner (totalsCollateralSlot asset))

def supplyCollateralTotalNext (evm : EVM.State) (asset : AccountAddress) (amount : UInt256) :
    UInt256 := withdrawCollateralTotal evm asset + amount

def supplyCollateralNext (evm : EVM.State) (dst asset : AccountAddress) (amount : UInt256) :
    UInt256 := withdrawCollateralBalance evm dst asset + amount

def supplyCollateralState (evm : EVM.State) (dst asset : AccountAddress) (amount : UInt256) :
    EVM.State :=
  storePackedWord (storeTotalsCollateral evm asset (supplyCollateralTotalNext evm asset amount)
      (supplyCollateralReserved evm asset))
    (userCollateralSlot dst asset) (supplyCollateralNext evm dst asset amount) 0 16

def supplyCollateralPrefixOutcome (evm : EVM.State) (dst asset : AccountAddress)
    (amount : UInt256) (out : ByteArray) : InternalOutcome :=
  if (withdrawCollateralTotal evm asset).toNat + amount.toNat < 2^128 then
    if (supplyCollateralTotalNext evm asset amount).toNat ≤ (calldataWord out 224).toNat then
      if (withdrawCollateralBalance evm dst asset).toNat + amount.toNat < 2^128 then
        if evm.executionEnv.perm then .ok (supplyCollateralState evm dst asset amount)
        else .staticViolation
      else .reverted
    else .reverted
  else .reverted

def supplyCollateralOutcome (evm : EVM.State) (dst asset : AccountAddress)
    (amount : UInt256) (out : ByteArray) : InternalOutcome :=
  match supplyCollateralPrefixOutcome evm dst asset amount out with
  | .ok evm' => assetMembershipResult evm' dst (calldataWord out 0)
      (withdrawCollateralBalance evm dst asset) (supplyCollateralNext evm dst asset amount)
  | .reverted => .reverted
  | .staticViolation => .staticViolation

def supplyCollateralTotalExpr : Expr :=
  .inRange (.uint ⟨128, by decide⟩)
    (.binary .add (.field (.var "totals") "totalSupplyAsset") (.var "amount"))

def supplyCollateralCapExpr : Expr :=
  .binary .le (.field (.var "totals") "totalSupplyAsset") (.field (.var "assetInfo") "supplyCap")

def supplyCollateralBalanceExpr : Expr :=
  .storage ⟨"userCollateral", [.mindex (.var "dst"), .mindex (.var "asset"), .field "balance"]⟩

def supplyCollateralPrefix : List Stmt :=
  [.letDecl "totals" (some (.tuple [.elem (.int (.uint ⟨128, by decide⟩)),
      .elem (.int (.uint ⟨128, by decide⟩))]))
      (.storage ⟨"totalsCollateral", [.mindex (.var "asset")]⟩),
    .assign .localVar ⟨"totals", [.field "totalSupplyAsset"]⟩ supplyCollateralTotalExpr,
    .require supplyCollateralCapExpr,
    .letDecl "dstCollateral" (some (.elem (.int (.uint ⟨128, by decide⟩))))
      supplyCollateralBalanceExpr,
    .letDecl "dstCollateralNew" (some (.elem (.int (.uint ⟨128, by decide⟩))))
      (.inRange (.uint ⟨128, by decide⟩) (.binary .add (.var "dstCollateral") (.var "amount"))),
    .assign .storage ⟨"totalsCollateral", [.mindex (.var "asset")]⟩ (.var "totals"),
    .assign .storage
      ⟨"userCollateral", [.mindex (.var "dst"), .mindex (.var "asset"), .field "balance"]⟩
      (.var "dstCollateralNew")]

def supplyCollateralTail : List Stmt :=
  [.internalCall "updateAssetsIn"
      [.var "dst", .var "assetInfo", .var "dstCollateral", .var "dstCollateralNew"] "__c3",
    .emit "SupplyCollateral" [.var "from", .var "dst", .var "asset", .var "amount"]]

def supplyCollateralCallable : CallableDecl :=
  { params := [⟨"from", .elem .address⟩, ⟨"dst", .elem .address⟩, ⟨"asset", .elem .address⟩,
      ⟨"amount", .elem (.int (.uint ⟨128, by decide⟩))⟩]
    returnType := []
    body := [.internalCall "doTransferIn" [.var "asset", .var "from", .var "amount"] "__c0",
      .internalCall "safe128" [.var "__c0"] "__c1",
      .assign .localVar ⟨"amount", []⟩ (.var "__c1"),
      .internalCall "getAssetInfoByAddress_body" [.var "asset"] "assetInfo"] ++
      supplyCollateralPrefix ++ supplyCollateralTail }

theorem supplyCollateralCallable_lookup : lookupCallable? contract "supplyCollateral" =
    some supplyCollateralCallable := rfl

def supplyCollateralEntry (imms : Store) (sender dst asset : AccountAddress)
    (amount : UInt256) : Frame :=
  { contract := contract, immutables := imms,
    locals := (∅ : Store) |>.insert "amount" (.int amount.toNat)
      |>.insert "asset" (.address asset) |>.insert "dst" (.address dst)
      |>.insert "from" (.address sender) }

def supplyCollateralTotalsFrame (frame : Frame) (evm : EVM.State) (asset : AccountAddress)
    (amount : UInt256) : Frame :=
  let reserved := supplyCollateralReserved evm asset
  { frame with
    locals := (frame.locals.insert "totals"
      (totalsCollateralValue (withdrawCollateralTotal evm asset) reserved)).insert "totals"
        (totalsCollateralValue (supplyCollateralTotalNext evm asset amount) reserved) }

def supplyCollateralReadyFrame (frame : Frame) (evm : EVM.State) (dst asset : AccountAddress)
    (amount : UInt256) : Frame :=
  let frame := supplyCollateralTotalsFrame frame evm asset amount
  { frame with
    locals := (frame.locals.insert "dstCollateral"
      (.int (withdrawCollateralBalance evm dst asset).toNat)).insert "dstCollateralNew"
        (.int (supplyCollateralNext evm dst asset amount).toNat) }

def supplyCollateralPrefixResult (frame : Frame) (evm : EVM.State) (dst asset : AccountAddress)
    (amount : UInt256) (out : ByteArray) : ExecResult :=
  match supplyCollateralPrefixOutcome evm dst asset amount out with
  | .ok evm' => .ok (supplyCollateralReadyFrame frame evm dst asset amount) evm'
  | .reverted => .reverted
  | .staticViolation => .staticViolation

inductive SupplyCollateralTrace (v : CometWithExtendedAssetListImmutables)
    (sender dst asset : AccountAddress) (amount : UInt256) (evm : EVM.State) :
    InternalOutcome → Prop where
  | transferFailed (ht : TransferInTrace asset sender amount evm none) :
      SupplyCollateralTrace v sender dst asset amount evm .reverted
  | tooLarge {evm' received}
      (ht : TransferInTrace asset sender amount evm (some (evm', received)))
      (hw : ¬ received.toNat < 2^128) :
      SupplyCollateralTrace v sender dst asset amount evm .reverted
  | assetFailed {evm' received}
      (ht : TransferInTrace asset sender amount evm (some (evm', received)))
      (hw : received.toNat < 2^128) (ha : AssetSearch v asset 0 evm' none) :
      SupplyCollateralTrace v sender dst asset amount evm .reverted
  | done {evm' received evm'' out}
      (ht : TransferInTrace asset sender amount evm (some (evm', received)))
      (hw : received.toNat < 2^128) (ha : AssetSearch v asset 0 evm' (some (evm'', out)))
      (hv : AssetValid out) : SupplyCollateralTrace v sender dst asset amount evm
        (supplyCollateralOutcome evm'' dst asset received out)

end Benchmarks.CompoundIII.Comet
