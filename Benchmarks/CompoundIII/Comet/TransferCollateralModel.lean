import Benchmarks.CompoundIII.Comet.WithdrawCollateralModel

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Benchmarks.CompoundIII.Comet.Immutables

namespace Benchmarks.CompoundIII.Comet

def transferCollateralSrcNext (evm : EVM.State) (src asset : AccountAddress)
    (amount : UInt256) : UInt256 := UInt256.sub (withdrawCollateralBalance evm src asset) amount

def transferCollateralDstNext (evm : EVM.State) (dst asset : AccountAddress)
    (amount : UInt256) : UInt256 := withdrawCollateralBalance evm dst asset + amount

def transferCollateralState (evm : EVM.State) (src dst asset : AccountAddress)
    (amount : UInt256) : EVM.State :=
  storePackedWord
    (storePackedWord evm (userCollateralSlot src asset)
      (transferCollateralSrcNext evm src asset amount) 0 16)
    (userCollateralSlot dst asset) (transferCollateralDstNext evm dst asset amount) 0 16

def transferCollateralPrefixOutcome (evm : EVM.State) (src dst asset : AccountAddress)
    (amount : UInt256) : InternalOutcome :=
  if amount.toNat ≤ (withdrawCollateralBalance evm src asset).toNat then
    if (withdrawCollateralBalance evm dst asset).toNat + amount.toNat < 2^128 then
      if evm.executionEnv.perm then .ok (transferCollateralState evm src dst asset amount)
      else .staticViolation
    else .reverted
  else .reverted

def transferCollateralReadExpr (name : Ident) : Expr :=
  .storage ⟨"userCollateral", [.mindex (.var name), .mindex (.var "asset"), .field "balance"]⟩

def transferCollateralPrefix : List Stmt :=
  [.letDecl "srcCollateral" (some (.elem (.int (.uint ⟨128, by decide⟩))))
      (transferCollateralReadExpr "src"),
    .letDecl "dstCollateral" (some (.elem (.int (.uint ⟨128, by decide⟩))))
      (transferCollateralReadExpr "dst"),
    .letDecl "srcCollateralNew" (some (.elem (.int (.uint ⟨128, by decide⟩))))
      (.inRange (.uint ⟨128, by decide⟩) (.binary .sub (.var "srcCollateral") (.var "amount"))),
    .letDecl "dstCollateralNew" (some (.elem (.int (.uint ⟨128, by decide⟩))))
      (.inRange (.uint ⟨128, by decide⟩) (.binary .add (.var "dstCollateral") (.var "amount"))),
    .assign .storage
      ⟨"userCollateral", [.mindex (.var "src"), .mindex (.var "asset"), .field "balance"]⟩
      (.var "srcCollateralNew"),
    .assign .storage
      ⟨"userCollateral", [.mindex (.var "dst"), .mindex (.var "asset"), .field "balance"]⟩
      (.var "dstCollateralNew")]

def transferCollateralTail : List Stmt :=
  [.internalCall "getAssetInfoByAddress_body" [.var "asset"] "assetInfo",
    .internalCall "updateAssetsIn"
      [.var "src", .var "assetInfo", .var "srcCollateral", .var "srcCollateralNew"] "__c1",
    .internalCall "updateAssetsIn"
      [.var "dst", .var "assetInfo", .var "dstCollateral", .var "dstCollateralNew"] "__c2",
    .internalCall "isBorrowCollateralized_body" [.var "src"] "__c3",
    .require (.var "__c3"),
    .emit "TransferCollateral" [.var "src", .var "dst", .var "asset", .var "amount"]]

def transferCollateralCallable : CallableDecl :=
  { params := [⟨"src", .elem .address⟩, ⟨"dst", .elem .address⟩, ⟨"asset", .elem .address⟩,
      ⟨"amount", .elem (.int (.uint ⟨128, by decide⟩))⟩]
    returnType := []
    body := transferCollateralPrefix ++ transferCollateralTail }

theorem transferCollateralCallable_lookup : lookupCallable? contract "transferCollateral" =
    some transferCollateralCallable := rfl

def transferCollateralEntry (imms : Store) (src dst asset : AccountAddress)
    (amount : UInt256) : Frame :=
  { contract := contract, immutables := imms,
    locals := (∅ : Store) |>.insert "amount" (.int amount.toNat)
      |>.insert "asset" (.address asset) |>.insert "dst" (.address dst)
      |>.insert "src" (.address src) }

def transferCollateralReadyFrame (frame : Frame) (evm : EVM.State)
    (src dst asset : AccountAddress) (amount : UInt256) : Frame :=
  { frame with locals := frame.locals
      |>.insert "srcCollateral" (.int (withdrawCollateralBalance evm src asset).toNat)
      |>.insert "dstCollateral" (.int (withdrawCollateralBalance evm dst asset).toNat)
      |>.insert "srcCollateralNew" (.int (transferCollateralSrcNext evm src asset amount).toNat)
      |>.insert "dstCollateralNew" (.int (transferCollateralDstNext evm dst asset amount).toNat) }

def transferCollateralPrefixResult (frame : Frame) (evm : EVM.State)
    (src dst asset : AccountAddress) (amount : UInt256) : ExecResult :=
  match transferCollateralPrefixOutcome evm src dst asset amount with
  | .ok evm' => .ok (transferCollateralReadyFrame frame evm src dst asset amount) evm'
  | .reverted => .reverted
  | .staticViolation => .staticViolation

end Benchmarks.CompoundIII.Comet
