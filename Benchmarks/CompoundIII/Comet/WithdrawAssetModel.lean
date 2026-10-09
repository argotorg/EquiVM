import Benchmarks.CompoundIII.Comet.WithdrawBaseModel
import Benchmarks.CompoundIII.Comet.WithdrawCollateralTrace
import Benchmarks.CompoundIII.Comet.BalanceSource

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Benchmarks.CompoundIII.Comet.Immutables

namespace Benchmarks.CompoundIII.Comet

def withdrawBalanceValid (v : CometWithExtendedAssetListImmutables) (evm : EVM.State) : Prop :=
  CurrentIndicesValid v
    (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨0⟩)
    (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨1⟩) (timestampWord evm.executionEnv)

instance (v : CometWithExtendedAssetListImmutables) (evm : EVM.State) :
    Decidable (withdrawBalanceValid v evm) := by unfold withdrawBalanceValid; infer_instance

def withdrawBalanceWord (v : CometWithExtendedAssetListImmutables) (evm : EVM.State)
    (src : AccountAddress) : UInt256 :=
  balanceWord v (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨0⟩)
    (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨1⟩) (timestampWord evm.executionEnv)
    (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner (userBasicSlot src))

inductive WithdrawAssetTrace (v : CometWithExtendedAssetListImmutables)
    (src recipient asset : AccountAddress) (amount : UInt256) (evm : EVM.State) :
    InternalOutcome → Prop where
  | base {result} (hb : asset = v.baseToken) (hm : amount ≠ UInt256.lnot ⟨0⟩)
      (ht : WithdrawBaseTrace v src recipient amount evm result) :
      WithdrawAssetTrace v src recipient asset amount evm result
  | balanceFailed (hb : asset = v.baseToken) (hm : amount = UInt256.lnot ⟨0⟩)
      (hv : ¬ withdrawBalanceValid v evm) :
      WithdrawAssetTrace v src recipient asset amount evm .reverted
  | allBase {result} (hb : asset = v.baseToken) (hm : amount = UInt256.lnot ⟨0⟩)
      (hv : withdrawBalanceValid v evm)
      (ht : WithdrawBaseTrace v src recipient (withdrawBalanceWord v evm src) evm result) :
      WithdrawAssetTrace v src recipient asset amount evm result
  | tooLarge (hb : asset ≠ v.baseToken) (hw : ¬ amount.toNat < 2^128) :
      WithdrawAssetTrace v src recipient asset amount evm .reverted
  | collateral {result} (hb : asset ≠ v.baseToken) (hw : amount.toNat < 2^128)
      (ht : WithdrawCollateralTrace v src recipient asset amount evm result) :
      WithdrawAssetTrace v src recipient asset amount evm result

def withdrawBaseAmountStmt : Stmt :=
  .ite (.binary .eq (.var "amount") (.intLit (2^256-1)))
    [.internalCall "balanceOf_body" [.var "src"] "__c3",
      .assign .localVar ⟨"amount", []⟩ (.var "__c3")] []

def withdrawAssetStmt : Stmt :=
  .ite (.binary .eq (.var "asset") (.immutable "baseToken"))
    [withdrawBaseAmountStmt, .internalCall "withdrawBase" [.var "src", .var "to", .var "amount"] "__c4"]
    [.internalCall "safe128" [.var "amount"] "__c5",
      .internalCall "withdrawCollateral" [.var "src", .var "to", .var "asset", .var "__c5"] "__c6"]

structure WithdrawAssetArgs (frame : Frame) (v : CometWithExtendedAssetListImmutables)
    (src recipient asset : AccountAddress) (amount : UInt256) : Prop where
  contract : frame.contract = Comet.contract
  immutables : frame.immutables = immStore v
  src : frame.locals.get? "src" = some (.address src)
  recipient : frame.locals.get? "to" = some (.address recipient)
  asset : frame.locals.get? "asset" = some (.address asset)
  amount : frame.locals.get? "amount" = some (.int amount.toNat)

def withdrawAssetReady (frame : Frame) (v : CometWithExtendedAssetListImmutables)
    (evm : EVM.State) (src asset : AccountAddress) (amount : UInt256) : Frame :=
  if asset = v.baseToken then
    if amount = UInt256.lnot ⟨0⟩ then
      { frame with
        locals := (frame.locals.insert "__c3" (.int (withdrawBalanceWord v evm src).toNat)).insert
          "amount" (.int (withdrawBalanceWord v evm src).toNat) }
    else frame
  else { frame with locals := frame.locals.insert "__c5" (.int amount.toNat) }

def withdrawAssetReturn (v : CometWithExtendedAssetListImmutables) (asset : AccountAddress) : Ident :=
  if asset = v.baseToken then "__c4" else "__c6"

theorem withdrawAssetReady_contract (frame v evm src asset amount) :
    (withdrawAssetReady frame v evm src asset amount).contract = frame.contract := by
  unfold withdrawAssetReady
  split_ifs <;> rfl

end Benchmarks.CompoundIII.Comet
