import Benchmarks.CompoundIII.Comet.ApproveCallSource
import Benchmarks.CompoundIII.Comet.GetterSource

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Benchmarks.CompoundIII.Comet.Immutables

namespace Benchmarks.CompoundIII.Comet

def approveThisArgs (manager asset : AccountAddress) (amount : UInt256) : Store :=
  (((∅ : Store).insert "manager" (.address manager)).insert "asset" (.address asset)).insert
    "amount" (.int amount.toNat)

def approveThisEntry (v : CometWithExtendedAssetListImmutables) (evm : EVM.State)
    (manager asset : AccountAddress) (amount : UInt256) : Frame :=
  calldataLocalFrame
    { contract := contract, immutables := immStore v,
      locals := approveThisArgs manager asset amount } evm

def approveThisAuth : Expr := .binary .eq (.env .caller) (.immutable "governor")

def approveThisCode : Expr := .binary .gt (.extCodeSize (.var "asset")) (.intLit 0)

def approveThisBody : List Stmt :=
  [.require approveThisAuth, .require approveThisCode,
    .externalCall (.var "asset") "approve" (.intLit 0)
      [.var "manager", .var "amount"] "__c0"]

theorem approveThisTransition_body : approveThisTransition.body =
    calldataPrologue approveThisBody := rfl

inductive ApproveThisTrace (v : CometWithExtendedAssetListImmutables)
    (manager asset : AccountAddress) (amount : UInt256) (evm : EVM.State) :
    Option EVM.State → Prop where
  | unauthorized (ha : evm.executionEnv.source ≠ v.governor) :
      ApproveThisTrace v manager asset amount evm none
  | codeMissing (ha : evm.executionEnv.source = v.governor)
      (hc : extCodeSizeWord evm.accountMap (EVM.word asset.val) = ⟨0⟩) :
      ApproveThisTrace v manager asset amount evm none
  | callResult {evm' : EVM.State} {z : Bool} {out : ByteArray}
      (ha : evm.executionEnv.source = v.governor)
      (hne : extCodeSizeWord evm.accountMap (EVM.word asset.val) ≠ ⟨0⟩)
      (hc : callViaEVM evm asset 0 (approvePayload manager amount) (z, evm', out)) :
      ApproveThisTrace v manager asset amount evm (if z then some evm' else none)

def ApproveThisSourceResult (v : CometWithExtendedAssetListImmutables)
    (manager asset : AccountAddress) (amount : UInt256) (evm : EVM.State)
    (result : Option EVM.State) : Prop :=
  match result with
  | none => ExecTransitionBody config contract evm (approveThisArgs manager asset amount)
      approveThisTransition.body .reverted (immStore v)
  | some evm' => ∃ final,
      ExecTransitionBody config contract evm (approveThisArgs manager asset amount)
        approveThisTransition.body (.returned final evm' none) (immStore v)

def ApproveThisRun (v : CometWithExtendedAssetListImmutables)
    (g : Sat256) (s0 : EVM.State) (result : Option EVM.State) : Prop :=
  match result with
  | none => RDrev (deployedRuntime v) g s0
  | some evm' => RDret (deployedRuntime v) g s0 evm'.accountMap ByteArray.empty

end Benchmarks.CompoundIII.Comet
