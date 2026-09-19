import Solm.Semantics
import Solm.SolidityLayout

/-!
# OpenZeppelin Ownable2Step benchmark spec

Solm specification for the concrete `Ownable2StepBench` wrapper.  The deployed runtime has the
OpenZeppelin `Ownable2Step` storage shape: `_owner` in slot 0 and `_pendingOwner` in slot 1.
-/

open Solm ABI

namespace OpenZeppelinBench.Ownable2Step

def addr : ABIType := .elem .address
def addrSt : StorageType := .elem .address

def sender : Expr := .env .caller
def zeroAddr : Expr := .cast (.intLit 0) addrSt

def ownerRef : StorageRef := { base := "_owner" }
def pendingOwnerRef : StorageRef := { base := "_pendingOwner" }

def storageDecls : List StorageDecl :=
  [ { name := "_owner", ty := addrSt },
    { name := "_pendingOwner", ty := addrSt } ]

def addrLoc (slot : Ethereum.UInt256) : StorageLoc :=
  { slot := slot, offset := 0, size := 20, hbound := by decide, type := .address }

def storageLayout : StorageLayout where
  layout ref _ :=
    match ref.base, ref.steps with
    | "_owner", [] => some (addrLoc ⟨0⟩)
    | "_pendingOwner", [] => some (addrLoc ⟨1⟩)
    | _, _ => none

def ownerTransition : TransitionDecl :=
  { name := "owner"
    params := []
    returnType := [addr]
    body :=
      [ .require (.binary .eq (.env .callvalue) (.intLit 0)),
        .return [(.storage ownerRef)] ] }

def pendingOwnerTransition : TransitionDecl :=
  { name := "pendingOwner"
    params := []
    returnType := [addr]
    body :=
      [ .require (.binary .eq (.env .callvalue) (.intLit 0)),
        .return [(.storage pendingOwnerRef)] ] }

def transferOwnershipTransition : TransitionDecl :=
  { name := "transferOwnership"
    params := [{ name := "newOwner", ty := addr }]
    returnType := []
    body :=
      [ .require (.binary .eq (.env .callvalue) (.intLit 0)),
        .require (.binary .eq (.storage ownerRef) sender),
        .assign .storage pendingOwnerRef (.var "newOwner") ] }

def acceptOwnershipTransition : TransitionDecl :=
  { name := "acceptOwnership"
    params := []
    returnType := []
    body :=
      [ .require (.binary .eq (.env .callvalue) (.intLit 0)),
        .require (.binary .eq (.storage pendingOwnerRef) sender),
        .assign .storage pendingOwnerRef zeroAddr,
        .assign .storage ownerRef sender ] }

def renounceOwnershipTransition : TransitionDecl :=
  { name := "renounceOwnership"
    params := []
    returnType := []
    body :=
      [ .require (.binary .eq (.env .callvalue) (.intLit 0)),
        .require (.binary .eq (.storage ownerRef) sender),
        .assign .storage pendingOwnerRef zeroAddr,
        .assign .storage ownerRef zeroAddr ] }

def constructorDecl : ConstructorDecl :=
  { params := [{ name := "initialOwner", ty := addr }]
    body :=
      [ .require (.binary .ne (.var "initialOwner") zeroAddr),
        .assign .storage ownerRef (.var "initialOwner") ] }

def contract : ContractDecl :=
  { name := "Ownable2StepBench"
    storage := storageDecls
    ctor := constructorDecl
    transitions :=
      [ acceptOwnershipTransition,
        ownerTransition,
        pendingOwnerTransition,
        renounceOwnershipTransition,
        transferOwnershipTransition ] }

def config : Config :=
  { storage := storageLayout
    externalABI := defaultExternalCallABI
    selfDeployment := genSolidityConstructorDeployment contract.ctor.params }

end OpenZeppelinBench.Ownable2Step
