import Solm.Semantics
import Solm.MetaSolidityLayout

/-!
# TransientFlag — Solm specification

`uint256 transient flag` at transient slot 0, the slot Solidity assigns to the only
transient state variable. `setFlag` writes that word; `getFlag` reads it back.
-/

open Solm ABI

namespace TransientFlag

def uint256Int : IntType := .uint ⟨256, by decide⟩
def uint256 : ABIType := .elem (.int uint256Int)

/-- Transient slot 0, a whole `uint256` word. -/
def flagLoc : StorageLoc :=
  { slot := ⟨0⟩, offset := 0, size := 32, hbound := by decide, type := .int uint256Int }

def flagRef : StorageRef := { base := "flag" }

/-- `setFlag(uint256 v)` stores `v` in the transient flag. -/
def setFlagTransition : TransitionDecl :=
  { name := "setFlag"
    params := [{ name := "v", ty := uint256 }]
    returnType := []
    body :=
      [ .require (.binary .eq (.env .callvalue) (.intLit 0)),
        .assign .transient flagRef (.var "v") ] }

/-- `getFlag()` returns the transient flag. -/
def getFlagTransition : TransitionDecl :=
  { name := "getFlag"
    params := []
    returnType := [uint256]
    body :=
      [ .require (.binary .eq (.env .callvalue) (.intLit 0)),
        .return [.transient flagRef] ] }

def flagContract : ContractDecl :=
  { name := "TransientFlag"
    storage := []
    transient := [{ name := "flag", ty := .elem (.int uint256Int) }]
    ctor := { params := [], body := [] }
    transitions := [setFlagTransition, getFlagTransition] }

end TransientFlag

/-- Generate the transient slot independently of persistent storage. -/
def flagLayout : StorageLayout :=
  solidityLayout! [TransientFlag.flagContract.structs] [TransientFlag.flagContract.transient]

theorem flagLayout_flag :
    flagLayout { base := "flag" } = some (.leaf TransientFlag.flagLoc) := rfl

/-- `flag` lives in the transient map at slot 0. Persistent storage is empty. -/
def flagConfig : Config :=
  { storageBackend := StorageBackend.empty
    transientBackend := solidityTransientStorageBackend flagLayout
    externalABI := defaultExternalCallABI
    selfDeployment := genSolidityConstructorDeployment TransientFlag.flagContract.ctor.params }
