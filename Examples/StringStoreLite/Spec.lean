import Solm.Semantics
import Solm.SolidityLayout

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
    returnType := some uint256
    body :=
      [ .require (.binary .eq (.env .callvalue) (.intLit 0)),
        .letDecl "copy" (some stringTy) (.var "value"),
        .assign .storage currentRef (.var "copy"),
        .return (.arrayLength .localVar { base := "copy" }) ] }

def clearCurrentTransition : TransitionDecl :=
  { name := "clearCurrent"
    params := []
    returnType := some uint256
    body :=
      [ .require (.binary .eq (.env .callvalue) (.intLit 0)),
        .letDecl "copy" (some stringTy) (.storage currentRef),
        .delete currentRef,
        .return (.arrayLength .localVar { base := "copy" }) ] }

def currentLengthGetter : TransitionDecl :=
  { name := "currentLength"
    params := []
    returnType := some uint256
    body :=
      [ .require (.binary .eq (.env .callvalue) (.intLit 0)),
        .return (.arrayLength .storage currentRef) ] }

def stringStoreLiteContract : ContractDecl :=
  { name := "StringStoreLite"
    storage := storageDecls
    ctor := { params := [], body := [] }
    transitions := [setTransition, clearCurrentTransition, currentLengthGetter] }

/-! ## Solidity string/bytes storage layout -/

def uint8Loc (slot : Ethereum.UInt256) (offset : Fin 32) : StorageLoc :=
  { slot := slot, offset := offset, size := 1, hbound := by omega, type := .int uint8Int }

def bytesLikeDataBase (baseSlot : Ethereum.UInt256) : Ethereum.UInt256 :=
  Ethereum.uInt256OfByteArray (ffi.KEC baseSlot.toByteArray)

def bytesLikeLengthLoc (baseSlot : Ethereum.UInt256) (evm : EVM.State) : StorageLoc :=
  if checkBytesPacked baseSlot evm then
    { slot := baseSlot, offset := 0, size := 1, hbound := by decide,
      bitOffset := some 1, type := .int uint256Int }
  else
    { slot := baseSlot, offset := 0, size := 32, hbound := by decide,
      bitOffset := some 1, type := .int uint256Int }

def bytesLikeByteLoc? (baseSlot : Ethereum.UInt256) (index : KeyValue)
    (evm : EVM.State) : Option StorageLoc :=
  match index with
  | .int i =>
      if i < 0 then
        none
      else
        let idx := i.toNat
        if checkBytesPacked baseSlot evm then
          if hidx : idx < 31 then
            some (uint8Loc baseSlot ⟨31 - idx, by omega⟩)
          else
            none
        else
          some (uint8Loc
            (bytesLikeDataBase baseSlot + Ethereum.UInt256.ofNat (idx / 32))
            ⟨31 - (idx % 32), by
              have hmod : idx % 32 < 32 := Nat.mod_lt idx (by decide)
              omega⟩)
  | _ => none

def stringStoreLiteLayout : EvaledStorageRef -> EVM.State -> Option StorageLoc
  | { base := "current", steps := [.length] }, evm => some (bytesLikeLengthLoc ⟨0⟩ evm)
  | { base := "current", steps := [.aindex i] }, evm => bytesLikeByteLoc? ⟨0⟩ i evm
  | _, _ => none

def stringStoreLiteStorageLayout : StorageLayout where
  layout := stringStoreLiteLayout
  readBytesLength := solidityReadBytesLength? stringStoreLiteLayout
  prepareBytesWrite := solidityPrepareBytesWrite? stringStoreLiteLayout
  writeBytes := solidityWriteBytes? stringStoreLiteLayout

end StringStoreLite

def stringStoreLiteConfig : Config :=
  { storage := StringStoreLite.stringStoreLiteStorageLayout
    externalABI := defaultExternalCallABI
    selfDeployment :=
      genSolidityConstructorDeployment StringStoreLite.stringStoreLiteContract.ctor.params }

@[simp] theorem stringStoreLiteConfig_storage_current_length :
    stringStoreLiteConfig.storage.layout { base := "current", steps := [.length] } =
      fun evm => some (StringStoreLite.bytesLikeLengthLoc ⟨0⟩ evm) :=
  rfl
