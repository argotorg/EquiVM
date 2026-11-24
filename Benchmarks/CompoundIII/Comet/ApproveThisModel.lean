import Benchmarks.CompoundIII.Comet.ApproveCallSource
import Benchmarks.CompoundIII.Comet.GetterSource

variable {fork : Ethereum.Fork}

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
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

inductive ApproveThisTrace (fork : Ethereum.Fork) (v : CometWithExtendedAssetListImmutables)
    (manager asset : AccountAddress) (amount : UInt256) (evm : EVM.State) :
    Option EVM.State → Prop where
  | unauthorized (ha : evm.executionEnv.source ≠ v.governor) :
      ApproveThisTrace fork v manager asset amount evm none
  | codeMissing (ha : evm.executionEnv.source = v.governor)
      (hc : extCodeSizeWord evm.accountMap (EVM.word asset.val) = ⟨0⟩) :
      ApproveThisTrace fork v manager asset amount evm none
  | callResult {evm' : EVM.State} {z : Bool} {out : ByteArray}
      (ha : evm.executionEnv.source = v.governor)
      (hne : extCodeSizeWord evm.accountMap (EVM.word asset.val) ≠ ⟨0⟩)
      (hc : callViaEVM fork evm asset 0 (approvePayload manager amount) (z, evm', out)) :
      ApproveThisTrace fork v manager asset amount evm (if z then some evm' else none)

def ApproveThisSourceResult (fork : Ethereum.Fork) (v : CometWithExtendedAssetListImmutables)
    (manager asset : AccountAddress) (amount : UInt256) (evm : EVM.State)
    (result : Option EVM.State) : Prop :=
  match result with
  | none => ExecTransitionBody fork config contract evm (approveThisArgs manager asset amount)
      approveThisTransition.body .reverted (immStore v)
  | some evm' => ∃ final,
      ExecTransitionBody fork config contract evm (approveThisArgs manager asset amount)
        approveThisTransition.body (.returned final evm' none) (immStore v)

def ApproveThisRun (fork : Ethereum.Fork) (v : CometWithExtendedAssetListImmutables)
    (g : Sat256) (s0 : EVM.State) (result : Option EVM.State) : Prop :=
  match result with
  | none => RDrev fork (deployedRuntime v) g s0
  | some evm' => RDret fork (deployedRuntime v) g s0 evm'.accountMap ByteArray.empty

end Benchmarks.CompoundIII.Comet
