import Solm.Semantics
import Solm.SolidityLayout

/-!
# Ownable2Step — Solm specification for `Ownable2Step.sol`

A faithful (events-aside) Solm spec of the flattened OpenZeppelin-style **Ownable2Step** — the
recommended two-step ownership-transfer pattern.  Self-contained: two `address` slots, caller
checks, no external calls / loops / structs.  solc emits a **linear** selector dispatcher (5
functions), so the proof reuses the existing `Reasoning` linear-dispatch machinery exactly as
`Examples/ERC20`.

Storage: `_owner` at slot 0, `_pendingOwner` at slot 1 (each a full-slot `address`).
Layout is hand-written to match the deployed bytecode.
-/

open Solm ABI

namespace Ownable2Step

def addr : ABIType := .elem .address
def addrSt : StorageType := .elem .address

def sender : Expr := .env .caller
/-- `address(0)`. -/
def zeroAddr : Expr := .cast (.intLit 0) addrSt

def ownerRef : StorageRef := { base := "_owner" }
def pendingRef : StorageRef := { base := "_pendingOwner" }

def storageDecls : List StorageDecl :=
  [ { name := "_owner", ty := addrSt },
    { name := "_pendingOwner", ty := addrSt } ]

/-- A full-slot `address` storage location (low 20 bytes). -/
def addrLoc (s : Ethereum.UInt256) : StorageLoc :=
  { slot := s, offset := 0, size := 20, hbound := by decide, type := .address }

def ownableStorageLayout : StorageLayout where
  layout ref _ :=
    match ref.base, ref.steps with
    | "_owner", [] => some (addrLoc ⟨0⟩)
    | "_pendingOwner", [] => some (addrLoc ⟨1⟩)
    | _, _ => none

/-! ## Transitions -/

/-- `owner() view returns (address)`. -/
def ownerTransition : TransitionDecl :=
  { name := "owner"
    params := []
    returnType := some addr
    body :=
      [ .require (.binary .eq (.env .callvalue) (.intLit 0)),
        .return (.storage ownerRef) ] }

/-- `pendingOwner() view returns (address)`. -/
def pendingOwnerTransition : TransitionDecl :=
  { name := "pendingOwner"
    params := []
    returnType := some addr
    body :=
      [ .require (.binary .eq (.env .callvalue) (.intLit 0)),
        .return (.storage pendingRef) ] }

/-- `transferOwnership(address newOwner)` — owner sets the pending owner. -/
def transferOwnershipTransition : TransitionDecl :=
  { name := "transferOwnership"
    params := [{ name := "newOwner", ty := addr }]
    returnType := none
    body :=
      [ .require (.binary .eq (.env .callvalue) (.intLit 0)),
        .require (.binary .eq (.storage ownerRef) sender),
        .assign .storage pendingRef (.var "newOwner") ] }

/-- `acceptOwnership()` — pending owner accepts, becoming owner. -/
def acceptOwnershipTransition : TransitionDecl :=
  { name := "acceptOwnership"
    params := []
    returnType := none
    body :=
      [ .require (.binary .eq (.env .callvalue) (.intLit 0)),
        .require (.binary .eq (.storage pendingRef) sender),
        .assign .storage pendingRef zeroAddr,
        .assign .storage ownerRef sender ] }

/-- `renounceOwnership()` — owner relinquishes ownership. -/
def renounceOwnershipTransition : TransitionDecl :=
  { name := "renounceOwnership"
    params := []
    returnType := none
    body :=
      [ .require (.binary .eq (.env .callvalue) (.intLit 0)),
        .require (.binary .eq (.storage ownerRef) sender),
        .assign .storage pendingRef zeroAddr,
        .assign .storage ownerRef zeroAddr ] }

/-- Constructor `_owner = msg.sender` (modelled for completeness; not covered by runtime equivalence). -/
def constructorDecl : ConstructorDecl :=
  { params := []
    body := [ .assign .storage ownerRef sender ] }

def ownableContract : ContractDecl :=
  { name := "Ownable2Step"
    storage := storageDecls
    ctor := constructorDecl
    transitions :=
      [ ownerTransition,             -- 8da5cb5b
        pendingOwnerTransition,      -- e30c3978
        transferOwnershipTransition, -- f2fde38b
        acceptOwnershipTransition,   -- 79ba5097
        renounceOwnershipTransition ] } -- 715018a6

end Ownable2Step

def ownableConfig : Config :=
  { storage := Ownable2Step.ownableStorageLayout
    externalABI := defaultExternalCallABI
    selfDeployment := genSolidityConstructorDeployment Ownable2Step.ownableContract.ctor.params }
