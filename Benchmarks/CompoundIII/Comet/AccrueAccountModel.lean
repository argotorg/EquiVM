import Benchmarks.CompoundIII.Comet.AccrueInternalModel
import Benchmarks.CompoundIII.Comet.UpdateBaseModel
import Benchmarks.CompoundIII.Comet.GetterSource

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Benchmarks.CompoundIII.Comet.Immutables

namespace Benchmarks.CompoundIII.Comet

def accrueAccountBasic (evm : EVM.State) (addr : AccountAddress) : UserBasicData :=
  userBasicData (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner (userBasicSlot addr))

def accrueAccountUpdate (v : CometWithExtendedAssetListImmutables) (evm : EVM.State)
    (addr : AccountAddress) : InternalOutcome :=
  let basic := accrueAccountBasic evm addr
  updateBaseOutcome v evm addr basic (UInt256.signextend (UInt256.ofNat 12) basic.principal)

def accrueAccountOutcome (v : CometWithExtendedAssetListImmutables) (evm : EVM.State)
    (addr : AccountAddress) : InternalOutcome :=
  match accrueOutcome v evm with
  | .ok evm' => accrueAccountUpdate v evm' addr
  | .reverted => .reverted
  | .staticViolation => .staticViolation

def accrueAccountArgs (addr : AccountAddress) : Store :=
  (∅ : Store).insert "account" (.address addr)

def accrueAccountEntry (v : CometWithExtendedAssetListImmutables) (evm : EVM.State)
    (addr : AccountAddress) : Frame :=
  calldataLocalFrame
    { contract := contract, immutables := immStore v, locals := accrueAccountArgs addr } evm

def accrueAccountTail : List Stmt :=
  [.letDecl "basic" (some (.tuple [.elem (.int (.sint ⟨104, by decide⟩)),
      .elem (.int (.uint ⟨64, by decide⟩)), .elem (.int (.uint ⟨64, by decide⟩)),
      .elem (.int (.uint ⟨16, by decide⟩)), .elem (.int (.uint ⟨8, by decide⟩))]))
    (.storage ⟨"userBasic", [.mindex (.var "account")]⟩),
    .internalCall "updateBasePrincipal"
      [.var "account", .var "basic", .field (.var "basic") "principal"] "__c1"]

theorem accrueAccountTransition_body : accrueAccountTransition.body =
    calldataPrologue (.internalCall "accrueInternal" [] "__c0" :: accrueAccountTail) := rfl

end Benchmarks.CompoundIII.Comet
