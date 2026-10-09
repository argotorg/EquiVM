import Benchmarks.CompoundIII.Comet.CollateralStorage
import Benchmarks.CompoundIII.Comet.AssetMembershipSource
import Benchmarks.CompoundIII.Comet.CollateralCheckSource
import Benchmarks.CompoundIII.Comet.AssetSearch
import Benchmarks.CompoundIII.Comet.TransferOutSource

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Benchmarks.CompoundIII.Comet.Immutables

namespace Benchmarks.CompoundIII.Comet

def withdrawCollateralBalance (evm : EVM.State) (src asset : AccountAddress) : UInt256 :=
  low128 (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner (userCollateralSlot src asset))

def withdrawCollateralTotal (evm : EVM.State) (asset : AccountAddress) : UInt256 :=
  low128 (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner (totalsCollateralSlot asset))

def withdrawCollateralState (evm : EVM.State) (src asset : AccountAddress)
    (amount : UInt256) : EVM.State :=
  let evm' := storePackedWord evm (totalsCollateralSlot asset)
    (UInt256.sub (withdrawCollateralTotal evm asset) amount) 0 16
  storePackedWord evm' (userCollateralSlot src asset)
    (UInt256.sub (withdrawCollateralBalance evm src asset) amount) 0 16

def withdrawCollateralPrefixOutcome (evm : EVM.State) (src asset : AccountAddress)
    (amount : UInt256) : InternalOutcome :=
  if amount.toNat ≤ (withdrawCollateralBalance evm src asset).toNat then
    if amount.toNat ≤ (withdrawCollateralTotal evm asset).toNat then
      if evm.executionEnv.perm then .ok (withdrawCollateralState evm src asset amount)
      else .staticViolation
    else .reverted
  else .reverted

def withdrawCollateralBalanceExpr : Expr :=
  .storage ⟨"userCollateral", [.mindex (.var "src"), .mindex (.var "asset"), .field "balance"]⟩

def withdrawCollateralNewExpr : Expr :=
  .inRange (.uint ⟨128, by decide⟩) (.binary .sub (.var "srcCollateral") (.var "amount"))

def withdrawCollateralTotalRef : StorageRef :=
  ⟨"totalsCollateral", [.mindex (.var "asset"), .field "totalSupplyAsset"]⟩

def withdrawCollateralTotalExpr : Expr :=
  .inRange (.uint ⟨128, by decide⟩)
    (.binary .sub (.storage withdrawCollateralTotalRef) (.var "amount"))

def withdrawCollateralPrefix : List Stmt :=
  [.letDecl "srcCollateral" (some (.elem (.int (.uint ⟨128, by decide⟩))))
      withdrawCollateralBalanceExpr,
    .letDecl "srcCollateralNew" (some (.elem (.int (.uint ⟨128, by decide⟩))))
      withdrawCollateralNewExpr,
    .assign .storage withdrawCollateralTotalRef withdrawCollateralTotalExpr,
    .assign .storage
      ⟨"userCollateral", [.mindex (.var "src"), .mindex (.var "asset"), .field "balance"]⟩
      (.var "srcCollateralNew")]

def withdrawCollateralTail : List Stmt :=
  [.internalCall "getAssetInfoByAddress_body" [.var "asset"] "assetInfo",
    .internalCall "updateAssetsIn"
      [.var "src", .var "assetInfo", .var "srcCollateral", .var "srcCollateralNew"] "__c1",
    .internalCall "isBorrowCollateralized_body" [.var "src"] "__c2",
    .require (.var "__c2"),
    .internalCall "doTransferOut" [.var "asset", .var "to", .var "amount"] "__c3",
    .emit "WithdrawCollateral" [.var "src", .var "to", .var "asset", .var "amount"]]

def withdrawCollateralCallable : CallableDecl :=
  { params := [⟨"src", .elem .address⟩, ⟨"to", .elem .address⟩, ⟨"asset", .elem .address⟩,
      ⟨"amount", .elem (.int (.uint ⟨128, by decide⟩))⟩]
    returnType := []
    body := withdrawCollateralPrefix ++ withdrawCollateralTail }

theorem withdrawCollateralCallable_lookup : lookupCallable? contract "withdrawCollateral" =
    some withdrawCollateralCallable := rfl

def withdrawCollateralEntry (imms : Store) (src recipient asset : AccountAddress)
    (amount : UInt256) : Frame :=
  { contract := contract, immutables := imms,
    locals := (∅ : Store) |>.insert "amount" (.int amount.toNat)
      |>.insert "asset" (.address asset) |>.insert "to" (.address recipient)
      |>.insert "src" (.address src) }

def withdrawCollateralReadFrame (frame : Frame) (balance : UInt256) : Frame :=
  { frame with locals := frame.locals.insert "srcCollateral" (.int balance.toNat) }

def withdrawCollateralReadyFrame (frame : Frame) (balance amount : UInt256) : Frame :=
  let frame := withdrawCollateralReadFrame frame balance
  { frame with
    locals := frame.locals.insert "srcCollateralNew" (.int (UInt256.sub balance amount).toNat) }

def withdrawCollateralPrefixResult (frame : Frame) (evm : EVM.State)
    (src asset : AccountAddress) (amount : UInt256) : ExecResult :=
  match withdrawCollateralPrefixOutcome evm src asset amount with
  | .ok evm' => .ok
      (withdrawCollateralReadyFrame frame (withdrawCollateralBalance evm src asset) amount) evm'
  | .reverted => .reverted
  | .staticViolation => .staticViolation

end Benchmarks.CompoundIII.Comet
