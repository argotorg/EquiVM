import Benchmarks.CompoundIII.Comet.TransferAssetModel
import Benchmarks.CompoundIII.Comet.AuthorizationSource
import Benchmarks.CompoundIII.Comet.ReentrancyModel

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Benchmarks.CompoundIII.Comet.Immutables

namespace Benchmarks.CompoundIII.Comet

inductive TransferInternalAfter (v : CometWithExtendedAssetListImmutables)
    (operator src dst asset : AccountAddress) (amount : UInt256) (evm : EVM.State) :
    InternalOutcome → Prop where
  | unauthorized (ha : ¬ AuthorizationValid evm ⟨1, by decide⟩ operator src) :
      TransferInternalAfter v operator src dst asset amount evm .reverted
  | selfTransfer (ha : AuthorizationValid evm ⟨1, by decide⟩ operator src) (he : src = dst) :
      TransferInternalAfter v operator src dst asset amount evm .reverted
  | reverted (ha : AuthorizationValid evm ⟨1, by decide⟩ operator src)
      (hne : src ≠ dst)
      (ht : TransferAssetTrace v src dst asset amount evm .reverted) :
      TransferInternalAfter v operator src dst asset amount evm .reverted
  | staticViolation (ha : AuthorizationValid evm ⟨1, by decide⟩ operator src)
      (hne : src ≠ dst)
      (ht : TransferAssetTrace v src dst asset amount evm .staticViolation) :
      TransferInternalAfter v operator src dst asset amount evm .staticViolation
  | done {evm'} (ha : AuthorizationValid evm ⟨1, by decide⟩ operator src)
      (hne : src ≠ dst)
      (ht : TransferAssetTrace v src dst asset amount evm (.ok evm'))
      (hp : evm'.executionEnv.perm = true) :
      TransferInternalAfter v operator src dst asset amount evm (.ok (reentrancyState evm' false))

inductive TransferInternalTrace (v : CometWithExtendedAssetListImmutables)
    (operator src dst asset : AccountAddress) (amount : UInt256) (evm : EVM.State) :
    InternalOutcome → Prop where
  | reverted (he : reentrancyOutcome evm true = .reverted) :
      TransferInternalTrace v operator src dst asset amount evm .reverted
  | staticViolation (he : reentrancyOutcome evm true = .staticViolation) :
      TransferInternalTrace v operator src dst asset amount evm .staticViolation
  | done {evm' result} (he : reentrancyOutcome evm true = .ok evm')
      (ht : TransferInternalAfter v operator src dst asset amount evm' result) :
      TransferInternalTrace v operator src dst asset amount evm result

def transferInternalTail : List Stmt :=
  authorizationBlock ⟨1, by decide⟩ "src" ++
    [.require (.binary .ne (.var "src") (.var "dst")), transferAssetStmt,
      .internalCall "nonReentrantAfter" [] "__c7"]

def transferInternalCallable : CallableDecl :=
  { params := [⟨"operator", .elem .address⟩, ⟨"src", .elem .address⟩, ⟨"dst", .elem .address⟩,
      ⟨"asset", .elem .address⟩, ⟨"amount", abiUInt256⟩]
    returnType := []
    body := .internalCall "nonReentrantBefore" [] "__c0" :: transferInternalTail }

theorem transferInternalCallable_lookup :
    lookupCallable? contract "transferInternal" = some transferInternalCallable := rfl

def transferInternalEntry (imms : Store) (operator src dst asset : AccountAddress)
    (amount : UInt256) : Frame :=
  { contract := contract, immutables := imms
    locals := (((((∅ : Store).insert "amount" (.int amount.toNat)).insert "asset" (.address asset)).insert
      "dst" (.address dst)).insert "src" (.address src)).insert "operator" (.address operator) }

end Benchmarks.CompoundIII.Comet
