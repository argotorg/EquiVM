import Benchmarks.CompoundIII.Comet.SupplyBaseModel
import Benchmarks.CompoundIII.Comet.SupplyCollateralModel
import Benchmarks.CompoundIII.Comet.BorrowBalanceSource

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Benchmarks.CompoundIII.Comet.Immutables

namespace Benchmarks.CompoundIII.Comet

def supplyBorrowValid (v : CometWithExtendedAssetListImmutables) (evm : EVM.State)
    (dst : AccountAddress) : Prop :=
  BorrowBalanceValid v
    (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨0⟩)
    (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨1⟩) (timestampWord evm.executionEnv)
    (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner (userBasicSlot dst))

instance (v : CometWithExtendedAssetListImmutables) (evm : EVM.State) (dst : AccountAddress) :
    Decidable (supplyBorrowValid v evm dst) := by unfold supplyBorrowValid; infer_instance

def supplyBorrowWord (v : CometWithExtendedAssetListImmutables) (evm : EVM.State)
    (dst : AccountAddress) : UInt256 :=
  borrowBalanceWord v (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨0⟩)
    (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨1⟩) (timestampWord evm.executionEnv)
    (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner (userBasicSlot dst))

inductive SupplyAssetTrace (v : CometWithExtendedAssetListImmutables)
    (sender dst asset : AccountAddress) (amount : UInt256) (evm : EVM.State) :
    InternalOutcome → Prop where
  | base {result} (hb : asset = v.baseToken) (hm : amount ≠ UInt256.lnot ⟨0⟩)
      (ht : SupplyBaseTrace v sender dst amount evm result) :
      SupplyAssetTrace v sender dst asset amount evm result
  | balanceFailed (hb : asset = v.baseToken) (hm : amount = UInt256.lnot ⟨0⟩)
      (hv : ¬ supplyBorrowValid v evm dst) :
      SupplyAssetTrace v sender dst asset amount evm .reverted
  | allBase {result} (hb : asset = v.baseToken) (hm : amount = UInt256.lnot ⟨0⟩)
      (hv : supplyBorrowValid v evm dst)
      (ht : SupplyBaseTrace v sender dst (supplyBorrowWord v evm dst) evm result) :
      SupplyAssetTrace v sender dst asset amount evm result
  | tooLarge (hb : asset ≠ v.baseToken) (hw : ¬ amount.toNat < 2^128) :
      SupplyAssetTrace v sender dst asset amount evm .reverted
  | collateral {result} (hb : asset ≠ v.baseToken) (hw : amount.toNat < 2^128)
      (ht : SupplyCollateralTrace v sender dst asset amount evm result) :
      SupplyAssetTrace v sender dst asset amount evm result

def supplyBaseAmountStmt : Stmt :=
  .ite (.binary .eq (.var "amount") (.intLit (2^256-1)))
    [.internalCall "borrowBalanceOf_body" [.var "dst"] "__c3",
      .assign .localVar ⟨"amount", []⟩ (.var "__c3")] []

def supplyAssetStmt : Stmt :=
  .ite (.binary .eq (.var "asset") (.immutable "baseToken"))
    [supplyBaseAmountStmt, .internalCall "supplyBase" [.var "from", .var "dst", .var "amount"] "__c4"]
    [.internalCall "safe128" [.var "amount"] "__c5",
      .internalCall "supplyCollateral" [.var "from", .var "dst", .var "asset", .var "__c5"] "__c6"]

structure SupplyAssetArgs (frame : Frame) (v : CometWithExtendedAssetListImmutables)
    (sender dst asset : AccountAddress) (amount : UInt256) : Prop where
  contract : frame.contract = Comet.contract
  immutables : frame.immutables = immStore v
  sender : frame.locals.get? "from" = some (.address sender)
  dst : frame.locals.get? "dst" = some (.address dst)
  asset : frame.locals.get? "asset" = some (.address asset)
  amount : frame.locals.get? "amount" = some (.int amount.toNat)

def supplyAssetReady (frame : Frame) (v : CometWithExtendedAssetListImmutables)
    (evm : EVM.State) (dst asset : AccountAddress) (amount : UInt256) : Frame :=
  if asset = v.baseToken then
    if amount = UInt256.lnot ⟨0⟩ then
      { frame with
        locals := (frame.locals.insert "__c3" (.int (supplyBorrowWord v evm dst).toNat)).insert
          "amount" (.int (supplyBorrowWord v evm dst).toNat) }
    else frame
  else { frame with locals := frame.locals.insert "__c5" (.int amount.toNat) }

def supplyAssetReturn (v : CometWithExtendedAssetListImmutables) (asset : AccountAddress) : Ident :=
  if asset = v.baseToken then "__c4" else "__c6"

theorem supplyAssetReady_contract (frame v evm dst asset amount) :
    (supplyAssetReady frame v evm dst asset amount).contract = frame.contract := by
  unfold supplyAssetReady
  split_ifs <;> rfl

end Benchmarks.CompoundIII.Comet
