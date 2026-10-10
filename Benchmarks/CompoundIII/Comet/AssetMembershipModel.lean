import Benchmarks.CompoundIII.Comet.TypedBitUpdates
import Benchmarks.CompoundIII.Comet.AssetSource
import Benchmarks.CompoundIII.Comet.UserBasicState
import Benchmarks.CompoundIII.Comet.InternalMemoryOutcome

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.CompoundIII.Comet

def assetMembershipChange (initial final : UInt256) : Option Bool :=
  if initial = ⟨0⟩ then if final = ⟨0⟩ then none else some true
  else if final = ⟨0⟩ then some false else none

def assetMembershipState (evm : EVM.State) (account : AccountAddress)
    (offset : UInt256) (add : Bool) : EVM.State :=
  let basic := Solm.EVM.storageLoad evm evm.executionEnv.codeOwner (userBasicSlot account)
  if offset.toNat < 16 then
    storePackedWord evm (userBasicSlot account)
      (typedBitUpdateWord add ⟨16, by decide⟩ (userBasicFieldWord basic 2) offset.toNat) 29 2
  else storePackedWord evm (userBasicSlot account)
    (typedBitUpdateWord add ⟨8, by decide⟩ (userBasicFieldWord basic 3) (offset.toNat - 16)) 31 1

def assetMembershipWriteResult (evm : EVM.State) (account : AccountAddress)
    (offset : UInt256) (add : Bool) : InternalOutcome :=
  if offset.toNat < 24 then
    if evm.executionEnv.perm then .ok (assetMembershipState evm account offset add)
    else .staticViolation
  else .ok evm

def assetMembershipResult (evm : EVM.State) (account : AccountAddress)
    (offset initial final : UInt256) : InternalOutcome :=
  match assetMembershipChange initial final with
  | none => .ok evm
  | some add => assetMembershipWriteResult evm account offset add

def assetMembershipRef (reserved : Bool) : StorageRef :=
  ⟨"userBasic", [.mindex (.var "account"), .field (if reserved then "_reserved" else "assetsIn")]⟩

def assetMembershipOffset : Expr := .field (.var "assetInfo") "offset"

def assetMembershipBitExpr (reserved : Bool) : Expr :=
  if reserved then .inRange (.uint ⟨8, by decide⟩)
    (.binary .sub assetMembershipOffset (.intLit 16)) else assetMembershipOffset

def assetMembershipExpr (add reserved : Bool) : Expr :=
  let width : BitWidth := if reserved then ⟨8, by decide⟩ else ⟨16, by decide⟩
  typedBitUpdateExpr add width (.storage (assetMembershipRef reserved))
    (assetMembershipBitExpr reserved)

def assetMembershipWriteBlock (add : Bool) : List Stmt :=
  [.ite (.binary .lt assetMembershipOffset (.intLit 16))
    [.assign .storage (assetMembershipRef false) (assetMembershipExpr add false)]
    [.ite (.binary .lt assetMembershipOffset (.intLit 24))
      [.assign .storage (assetMembershipRef true) (assetMembershipExpr add true)] []]]

def assetMembershipCond (add : Bool) : Expr :=
  .binary .and
    (.binary (if add then .eq else .ne) (.var "initialUserBalance") (.intLit 0))
    (.binary (if add then .ne else .eq) (.var "finalUserBalance") (.intLit 0))

def assetMembershipCallable : CallableDecl :=
  { params := [⟨"account", .elem .address⟩, ⟨"assetInfo", assetInfoType⟩,
      ⟨"initialUserBalance", .elem (.int (.uint ⟨128, by decide⟩))⟩,
      ⟨"finalUserBalance", .elem (.int (.uint ⟨128, by decide⟩))⟩]
    returnType := []
    body := [.ite (assetMembershipCond true) (assetMembershipWriteBlock true)
      [.ite (assetMembershipCond false) (assetMembershipWriteBlock false) []]] }

theorem assetMembershipCallable_lookup : lookupCallable? contract "updateAssetsIn" =
    some assetMembershipCallable := rfl

def assetMembershipEntry (imms : Store) (account : AccountAddress) (out : ByteArray)
    (initial final : UInt256) : Frame :=
  { contract := contract, immutables := imms,
    locals := (∅ : Store) |>.insert "finalUserBalance" (.int final.toNat)
      |>.insert "initialUserBalance" (.int initial.toNat)
      |>.insert "assetInfo" (assetValue out) |>.insert "account" (.address account) }

end Benchmarks.CompoundIII.Comet
