import Solm.Semantics
import Solm.SolidityLayout

/-!
# OpenZeppelin Pausable benchmark spec

Solm specification for `PausableBench`, a concrete wrapper around the abstract OpenZeppelin
`Pausable` utility.  Events are intentionally omitted; storage, guards, and return values are
modelled.
-/

open Solm ABI

namespace OpenZeppelinBench.Pausable

def boolTy : ABIType := .elem .bool
def boolSt : StorageType := .elem .bool

def pausedRef : StorageRef := { base := "_paused" }

def storageDecls : List StorageDecl :=
  [ { name := "_paused", ty := boolSt } ]

def boolLoc (slot : Ethereum.UInt256) : StorageLoc :=
  { slot := slot, offset := 0, size := 1, hbound := by decide, type := .bool }

def storageLayout : StorageLayout where
  layout ref _ :=
    match ref.base, ref.steps with
    | "_paused", [] => some (boolLoc ⟨0⟩)
    | _, _ => none

def pausedTransition : TransitionDecl :=
  { name := "paused"
    params := []
    returnType := some boolTy
    body :=
      [ .require (.binary .eq (.env .callvalue) (.intLit 0)),
        .return (.storage pausedRef) ] }

def pauseTransition : TransitionDecl :=
  { name := "pause"
    params := []
    returnType := none
    body :=
      [ .require (.binary .eq (.env .callvalue) (.intLit 0)),
        .require (.unary .not (.storage pausedRef)),
        .assign .storage pausedRef (.boolLit true) ] }

def unpauseTransition : TransitionDecl :=
  { name := "unpause"
    params := []
    returnType := none
    body :=
      [ .require (.binary .eq (.env .callvalue) (.intLit 0)),
        .require (.storage pausedRef),
        .assign .storage pausedRef (.boolLit false) ] }

def guardedWhenNotPausedTransition : TransitionDecl :=
  { name := "guardedWhenNotPaused"
    params := []
    returnType := some boolTy
    body :=
      [ .require (.binary .eq (.env .callvalue) (.intLit 0)),
        .require (.unary .not (.storage pausedRef)),
        .return (.boolLit true) ] }

def guardedWhenPausedTransition : TransitionDecl :=
  { name := "guardedWhenPaused"
    params := []
    returnType := some boolTy
    body :=
      [ .require (.binary .eq (.env .callvalue) (.intLit 0)),
        .require (.storage pausedRef),
        .return (.boolLit true) ] }

def constructorDecl : ConstructorDecl :=
  { params := []
    body := [ .assign .storage pausedRef (.boolLit false) ] }

def contract : ContractDecl :=
  { name := "PausableBench"
    storage := storageDecls
    ctor := constructorDecl
    transitions :=
      [ guardedWhenNotPausedTransition,
        guardedWhenPausedTransition,
        pauseTransition,
        pausedTransition,
        unpauseTransition ] }

def config : Config :=
  { storage := storageLayout
    externalABI := defaultExternalCallABI
    selfDeployment := genSolidityConstructorDeployment contract.ctor.params }

end OpenZeppelinBench.Pausable
