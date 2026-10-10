import Benchmarks.CompoundIII.Comet.SupplyAssetModel
import Benchmarks.CompoundIII.Comet.AuthorizationSource
import Benchmarks.CompoundIII.Comet.ReentrancyModel

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Benchmarks.CompoundIII.Comet.Immutables

namespace Benchmarks.CompoundIII.Comet

inductive SupplyInternalAfter (v : CometWithExtendedAssetListImmutables)
    (operator sender dst asset : AccountAddress) (amount : UInt256) (evm : EVM.State) :
    InternalOutcome → Prop where
  | unauthorized (ha : ¬ AuthorizationValid evm ⟨0, by decide⟩ operator sender) :
      SupplyInternalAfter v operator sender dst asset amount evm .reverted
  | reverted (ha : AuthorizationValid evm ⟨0, by decide⟩ operator sender)
      (ht : SupplyAssetTrace v sender dst asset amount evm .reverted) :
      SupplyInternalAfter v operator sender dst asset amount evm .reverted
  | staticViolation (ha : AuthorizationValid evm ⟨0, by decide⟩ operator sender)
      (ht : SupplyAssetTrace v sender dst asset amount evm .staticViolation) :
      SupplyInternalAfter v operator sender dst asset amount evm .staticViolation
  | done {evm'} (ha : AuthorizationValid evm ⟨0, by decide⟩ operator sender)
      (ht : SupplyAssetTrace v sender dst asset amount evm (.ok evm'))
      (hp : evm'.executionEnv.perm = true) :
      SupplyInternalAfter v operator sender dst asset amount evm (.ok (reentrancyState evm' false))

inductive SupplyInternalTrace (v : CometWithExtendedAssetListImmutables)
    (operator sender dst asset : AccountAddress) (amount : UInt256) (evm : EVM.State) :
    InternalOutcome → Prop where
  | reverted (he : reentrancyOutcome evm true = .reverted) :
      SupplyInternalTrace v operator sender dst asset amount evm .reverted
  | staticViolation (he : reentrancyOutcome evm true = .staticViolation) :
      SupplyInternalTrace v operator sender dst asset amount evm .staticViolation
  | done {evm' result} (he : reentrancyOutcome evm true = .ok evm')
      (ht : SupplyInternalAfter v operator sender dst asset amount evm' result) :
      SupplyInternalTrace v operator sender dst asset amount evm result

def supplyInternalTail : List Stmt :=
  authorizationBlock ⟨0, by decide⟩ "from" ++ [supplyAssetStmt, .internalCall "nonReentrantAfter" [] "__c7"]

def supplyInternalCallable : CallableDecl :=
  { params := [⟨"operator", .elem .address⟩, ⟨"from", .elem .address⟩, ⟨"dst", .elem .address⟩,
      ⟨"asset", .elem .address⟩, ⟨"amount", abiUInt256⟩]
    returnType := []
    body := .internalCall "nonReentrantBefore" [] "__c0" :: supplyInternalTail }

theorem supplyInternalCallable_lookup :
    lookupCallable? contract "supplyInternal" = some supplyInternalCallable := rfl

def supplyInternalEntry (imms : Store) (operator sender dst asset : AccountAddress)
    (amount : UInt256) : Frame :=
  { contract := contract, immutables := imms
    locals := (((((∅ : Store).insert "amount" (.int amount.toNat)).insert "asset" (.address asset)).insert
      "dst" (.address dst)).insert "from" (.address sender)).insert "operator" (.address operator) }

end Benchmarks.CompoundIII.Comet
