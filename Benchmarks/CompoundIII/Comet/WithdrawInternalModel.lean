import Benchmarks.CompoundIII.Comet.WithdrawAssetModel
import Benchmarks.CompoundIII.Comet.WithdrawAuthModel
import Benchmarks.CompoundIII.Comet.ReentrancyModel

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Benchmarks.CompoundIII.Comet.Immutables

namespace Benchmarks.CompoundIII.Comet

inductive WithdrawInternalAfter (v : CometWithExtendedAssetListImmutables)
    (operator src recipient asset : AccountAddress) (amount : UInt256) (evm : EVM.State) :
    InternalOutcome → Prop where
  | unauthorized (ha : ¬ WithdrawAuthValid evm operator src) :
      WithdrawInternalAfter v operator src recipient asset amount evm .reverted
  | reverted (ha : WithdrawAuthValid evm operator src)
      (ht : WithdrawAssetTrace v src recipient asset amount evm .reverted) :
      WithdrawInternalAfter v operator src recipient asset amount evm .reverted
  | staticViolation (ha : WithdrawAuthValid evm operator src)
      (ht : WithdrawAssetTrace v src recipient asset amount evm .staticViolation) :
      WithdrawInternalAfter v operator src recipient asset amount evm .staticViolation
  | done {evm'} (ha : WithdrawAuthValid evm operator src)
      (ht : WithdrawAssetTrace v src recipient asset amount evm (.ok evm'))
      (hp : evm'.executionEnv.perm = true) :
      WithdrawInternalAfter v operator src recipient asset amount evm (.ok (reentrancyState evm' false))

inductive WithdrawInternalTrace (v : CometWithExtendedAssetListImmutables)
    (operator src recipient asset : AccountAddress) (amount : UInt256) (evm : EVM.State) :
    InternalOutcome → Prop where
  | reverted (he : reentrancyOutcome evm true = .reverted) :
      WithdrawInternalTrace v operator src recipient asset amount evm .reverted
  | staticViolation (he : reentrancyOutcome evm true = .staticViolation) :
      WithdrawInternalTrace v operator src recipient asset amount evm .staticViolation
  | done {evm' result} (he : reentrancyOutcome evm true = .ok evm')
      (ht : WithdrawInternalAfter v operator src recipient asset amount evm' result) :
      WithdrawInternalTrace v operator src recipient asset amount evm result

def withdrawInternalTail : List Stmt :=
  withdrawAuthBlock ++ [withdrawAssetStmt, .internalCall "nonReentrantAfter" [] "__c7"]

def withdrawInternalCallable : CallableDecl :=
  { params := [⟨"operator", .elem .address⟩, ⟨"src", .elem .address⟩, ⟨"to", .elem .address⟩,
      ⟨"asset", .elem .address⟩, ⟨"amount", abiUInt256⟩]
    returnType := []
    body := .internalCall "nonReentrantBefore" [] "__c0" :: withdrawInternalTail }

theorem withdrawInternalCallable_lookup :
    lookupCallable? contract "withdrawInternal" = some withdrawInternalCallable := rfl

def withdrawInternalEntry (imms : Store) (operator src recipient asset : AccountAddress)
    (amount : UInt256) : Frame :=
  { contract := contract, immutables := imms
    locals := (((((∅ : Store).insert "amount" (.int amount.toNat)).insert "asset" (.address asset)).insert
      "to" (.address recipient)).insert "src" (.address src)).insert "operator" (.address operator) }

end Benchmarks.CompoundIII.Comet
