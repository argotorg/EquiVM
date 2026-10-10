import Benchmarks.CompoundIII.Comet.TransferBaseModel
import Benchmarks.CompoundIII.Comet.TransferCollateralTrace
import Benchmarks.CompoundIII.Comet.WithdrawAssetModel

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Benchmarks.CompoundIII.Comet.Immutables

namespace Benchmarks.CompoundIII.Comet

inductive TransferAssetTrace (v : CometWithExtendedAssetListImmutables)
    (src dst asset : AccountAddress) (amount : UInt256) (evm : EVM.State) :
    InternalOutcome → Prop where
  | base {result} (hb : asset = v.baseToken) (hm : amount ≠ UInt256.lnot ⟨0⟩)
      (ht : TransferBaseTrace v src dst amount evm result) :
      TransferAssetTrace v src dst asset amount evm result
  | balanceFailed (hb : asset = v.baseToken) (hm : amount = UInt256.lnot ⟨0⟩)
      (hv : ¬ withdrawBalanceValid v evm) :
      TransferAssetTrace v src dst asset amount evm .reverted
  | allBase {result} (hb : asset = v.baseToken) (hm : amount = UInt256.lnot ⟨0⟩)
      (hv : withdrawBalanceValid v evm)
      (ht : TransferBaseTrace v src dst (withdrawBalanceWord v evm src) evm result) :
      TransferAssetTrace v src dst asset amount evm result
  | tooLarge (hb : asset ≠ v.baseToken) (hw : ¬ amount.toNat < 2^128) :
      TransferAssetTrace v src dst asset amount evm .reverted
  | collateral {result} (hb : asset ≠ v.baseToken) (hw : amount.toNat < 2^128)
      (ht : TransferCollateralTrace v src dst asset amount evm result) :
      TransferAssetTrace v src dst asset amount evm result

def transferBaseAmountStmt : Stmt :=
  .ite (.binary .eq (.var "amount") (.intLit (2^256-1)))
    [.internalCall "balanceOf_body" [.var "src"] "__c3",
      .assign .localVar ⟨"amount", []⟩ (.var "__c3")] []

def transferAssetStmt : Stmt :=
  .ite (.binary .eq (.var "asset") (.immutable "baseToken"))
    [transferBaseAmountStmt, .internalCall "transferBase" [.var "src", .var "dst", .var "amount"] "__c4"]
    [.internalCall "safe128" [.var "amount"] "__c5",
      .internalCall "transferCollateral" [.var "src", .var "dst", .var "asset", .var "__c5"] "__c6"]

structure TransferAssetArgs (frame : Frame) (v : CometWithExtendedAssetListImmutables)
    (src dst asset : AccountAddress) (amount : UInt256) : Prop where
  contract : frame.contract = Comet.contract
  immutables : frame.immutables = immStore v
  src : frame.locals.get? "src" = some (.address src)
  dst : frame.locals.get? "dst" = some (.address dst)
  asset : frame.locals.get? "asset" = some (.address asset)
  amount : frame.locals.get? "amount" = some (.int amount.toNat)

def transferAssetReady (frame : Frame) (v : CometWithExtendedAssetListImmutables)
    (evm : EVM.State) (src asset : AccountAddress) (amount : UInt256) : Frame :=
  if asset = v.baseToken then
    if amount = UInt256.lnot ⟨0⟩ then
      { frame with
        locals := (frame.locals.insert "__c3" (.int (withdrawBalanceWord v evm src).toNat)).insert
          "amount" (.int (withdrawBalanceWord v evm src).toNat) }
    else frame
  else { frame with locals := frame.locals.insert "__c5" (.int amount.toNat) }

def transferAssetReturn (v : CometWithExtendedAssetListImmutables) (asset : AccountAddress) : Ident :=
  if asset = v.baseToken then "__c4" else "__c6"

theorem transferAssetReady_contract (frame v evm src asset amount) :
    (transferAssetReady frame v evm src asset amount).contract = frame.contract := by
  unfold transferAssetReady
  split_ifs <;> rfl

end Benchmarks.CompoundIII.Comet
