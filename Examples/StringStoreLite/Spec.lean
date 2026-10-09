import Solm.Semantics
import Solm.MetaSolidityLayout

/-!
# StringStoreLite — focused string storage example

This is the first-line string infrastructure test. It intentionally avoids nested dynamic storage
such as `string[]` and keeps the default proof target on one Solidity single-slot dynamic string:

* `set(string)` decodes dynamic ABI string calldata, copies it to memory, and writes a string slot;
* `clearCurrent` checks whole-value storage-to-memory copy followed by clear;
* `currentLength` checks the storage length read.

The heavier `Examples.StringStore` directory remains the stress test for dynamic arrays of strings.
-/

open Solm ABI Ethereum

namespace StringStoreLite

/-! ## Types -/

def uint8Int : IntType := .uint ⟨8, by decide⟩
def uint256Int : IntType := .uint ⟨256, by decide⟩

def uint256 : ABIType := .elem (.int uint256Int)
def stringTy : ABIType := .string
def bytesTy : ABIType := .bytes

def uint8St : StorageType := .elem (.int uint8Int)
def uint256St : StorageType := .elem (.int uint256Int)
def stringSt : StorageType := .string
def bytesSt : StorageType := .bytes

/-! ## Storage refs -/

def currentRef : StorageRef := { base := "current" }

def currentByteRef (i : Expr) : StorageRef := { base := "current", steps := [.aindex i] }

def storageDecls : List StorageDecl :=
  [ { name := "current", ty := stringSt } ]

/-! ## Transitions -/

def setTransition : TransitionDecl :=
  { name := "set"
    params := [{ name := "value", ty := stringTy }]
    returnType := [uint256]
    body :=
      [ .require (.binary .eq (.env .callvalue) (.intLit 0)),
        .letDecl "copy" (some stringTy) (.var "value"),
        .assign .storage currentRef (.var "copy"),
        .return [(.arrayLength .localVar { base := "copy" })] ] }

def clearCurrentTransition : TransitionDecl :=
  { name := "clearCurrent"
    params := []
    returnType := [uint256]
    body :=
      [ .require (.binary .eq (.env .callvalue) (.intLit 0)),
        .letDecl "copy" (some stringTy) (.storage currentRef),
        .delete currentRef,
        .return [(.arrayLength .localVar { base := "copy" })] ] }

def currentLengthGetter : TransitionDecl :=
  { name := "currentLength"
    params := []
    returnType := [uint256]
    body :=
      [ .require (.binary .eq (.env .callvalue) (.intLit 0)),
        .return [(.arrayLength .storage currentRef)] ] }

def stringStoreLiteContract : ContractDecl :=
  { name := "StringStoreLite"
    storage := storageDecls
    ctor := { params := [], body := [] }
    transitions := [setTransition, clearCurrentTransition, currentLengthGetter] }

/-! ## Solidity string/bytes storage layout -/

def uint8Loc (slot : Ethereum.UInt256) (offset : Fin 32) : StorageLoc :=
  { slot := slot, offset := offset, size := 1, hbound := by omega, type := .int uint8Int }

def bytesLikeDataBase (baseSlot : Ethereum.UInt256) : Ethereum.UInt256 :=
  Ethereum.uInt256OfByteArray (KEC baseSlot.toByteArray)

/-- The Solidity schema determines the actual storage locations. The `.length` path is retained
    as a locator-only spelling for proofs about the length header. -/
def stringStoreLiteGeneratedLayout : StorageLayout :=
  solidityLayout! [[]] [storageDecls]

def stringStoreLiteLayout : StorageLayout
  | { base := "current", steps := [.length] } =>
      stringStoreLiteGeneratedLayout { base := "current" }
  | ref => stringStoreLiteGeneratedLayout ref

/-- Convenient names for the backend operations used throughout the string proofs. -/
@[simp] def stringLength? (cfg : Config) (evm : EVM.State) (ref : EvaledStorageRef) :
    EvalResult Nat :=
  cfg.storageBackend.length ref .string evm

@[simp] def stringWrite? (cfg : Config) (evm : EVM.State) (ref : EvaledStorageRef)
    (ty : StorageType) (value : Value) : EvalResult EVM.State :=
  cfg.storageBackend.write ref ty value evm

@[simp] theorem stringStoreLiteLayout_current :
    stringStoreLiteLayout { base := "current" } =
      some (.anchor ⟨0⟩) := by
  rfl

@[simp] theorem stringStoreLiteLayout_current_length :
    stringStoreLiteLayout { base := "current", steps := [.length] } =
      some (.anchor ⟨0⟩) := by
  rfl

end StringStoreLite

def stringStoreLiteConfig : Config :=
  { storageBackend := solidityStorageBackend StringStoreLite.stringStoreLiteLayout
    externalABI := defaultExternalCallABI
    selfDeployment :=
      genSolidityConstructorDeployment StringStoreLite.stringStoreLiteContract.ctor.params }

@[simp] theorem stringStoreLiteConfig_storage_current_length :
    stringStoreLiteConfig.storageBackend.locate? { base := "current", steps := [.length] } =
      some (.anchor ⟨0⟩) := by
  rfl
