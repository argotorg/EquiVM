import Solm.Semantics
import Solm.SolidityLayout

/-!
# StringStore — Solm specification for `StringStore.sol`

This example is intentionally a stress test for Solidity dynamic `string`/`bytes` storage:

* `set(string)` decodes a dynamic ABI string, copies it through memory, stores it, pushes it into a
  `string[]`, and copies it to `bytes`;
* `dropLast` exercises `string[]` pop;
* `clearCurrent`/`clearAll` exercise `delete` on dynamic bytes/string storage;
* `storeRaw(bytes)` exercises dynamic bytes calldata and Solidity `bytes.push`/`bytes.pop`.

Solm models dynamic `string` values as `Value.bytes`, matching dynamic `bytes` at the byte-payload
level.  Whole-value storage read/write/delete for `.string` and `.bytes` is handled by the
conditional compact Solidity layout in `Solm.Semantics`; the hand-written layout below supplies the
length and element refs needed by that support.
-/

open Solm ABI Ethereum

namespace StringStore

/-! ## Types -/

def uint8Int : IntType := .uint ⟨8, by decide⟩
def uint256Int : IntType := .uint ⟨256, by decide⟩

def uint256 : ABIType := .elem (.int uint256Int)
def stringTy : ABIType := .string
def bytesTy : ABIType := .bytes
def bytes32 : ABIType := .elem (.bytes ⟨31, by decide⟩)

def uint8St : StorageType := .elem (.int uint8Int)
def uint256St : StorageType := .elem (.int uint256Int)
def stringSt : StorageType := .string
def bytesSt : StorageType := .bytes

/-! ## Storage refs -/

def currentRef : StorageRef := { base := "current" }
def historyRef : StorageRef := { base := "history" }
def rawRef : StorageRef := { base := "raw" }

def currentByteRef (i : Expr) : StorageRef := { base := "current", steps := [.aindex i] }
def historyElemRef (i : Expr) : StorageRef := { base := "history", steps := [.aindex i] }
def historyByteRef (i j : Expr) : StorageRef :=
  { base := "history", steps := [.aindex i, .aindex j] }
def rawByteRef (i : Expr) : StorageRef := { base := "raw", steps := [.aindex i] }

def storageDecls : List StorageDecl :=
  [ { name := "current", ty := stringSt },
    { name := "history", ty := .dynamicArray stringSt },
    { name := "raw", ty := bytesSt } ]

/-! ## Transitions

These declarations mirror the public Solidity surface closely enough to pin selectors and intended
storage behavior.  Dynamic `string` and `bytes` values are represented as byte payloads (`Value.bytes`)
inside Solm.
-/

def setTransition : TransitionDecl :=
  { name := "set"
    params := [{ name := "value", ty := stringTy }]
    returnType := some uint256
    body :=
      [ .require (.binary .eq (.env .callvalue) (.intLit 0)),
        .letDecl "copy" (some stringTy) (.var "value"),
        .assign .storage currentRef (.var "copy"),
        .push historyRef (some (.var "copy")),
        .assign .storage rawRef (.var "copy"),
        .return (.arrayLength .localVar { base := "copy" }) ] }

def appendToHistoryTransition : TransitionDecl :=
  { name := "appendToHistory"
    params := [{ name := "suffix", ty := stringTy }]
    returnType := some uint256
    body :=
      [ .require (.binary .eq (.env .callvalue) (.intLit 0)),
        .push historyRef (some (.var "suffix")),
        .return (.arrayLength .storage historyRef) ] }

def replaceFromHistoryTransition : TransitionDecl :=
  { name := "replaceFromHistory"
    params := [{ name := "index", ty := uint256 }]
    returnType := some uint256
    body :=
      [ .require (.binary .eq (.env .callvalue) (.intLit 0)),
        .letDecl "copy" (some stringTy) (.storage (historyElemRef (.var "index"))),
        .assign .storage currentRef (.var "copy"),
        .assign .storage rawRef (.var "copy"),
        .return (.arrayLength .localVar { base := "copy" }) ] }

def dropLastTransition : TransitionDecl :=
  { name := "dropLast"
    params := []
    returnType := some stringTy
    body :=
      [ .require (.binary .eq (.env .callvalue) (.intLit 0)),
        .letDecl "length" (some uint256) (.arrayLength .storage historyRef),
        .require (.binary .gt (.var "length") (.intLit 0)),
        .letDecl "removed" (some stringTy)
          (.storage (historyElemRef (.binary .sub (.var "length") (.intLit 1)))),
        .pop historyRef,
        .return (.var "removed") ] }

def clearCurrentTransition : TransitionDecl :=
  { name := "clearCurrent"
    params := []
    returnType := some bytes32
    body :=
      [ .require (.binary .eq (.env .callvalue) (.intLit 0)),
        .delete currentRef,
        .return (.keccak256 (.newBytes (.intLit 0))) ] }

def clearAllTransition : TransitionDecl :=
  { name := "clearAll"
    params := []
    returnType := none
    body :=
      [ .require (.binary .eq (.env .callvalue) (.intLit 0)),
        .delete currentRef,
        .delete rawRef,
        .delete historyRef ] }

def storeRawTransition : TransitionDecl :=
  { name := "storeRaw"
    params := [{ name := "value", ty := bytesTy }]
    returnType := some bytes32
    body :=
      [ .require (.binary .eq (.env .callvalue) (.intLit 0)),
        .assign .storage rawRef (.var "value"),
        .return (.keccak256 (.newBytes (.intLit 0))) ] }

def currentLengthGetter : TransitionDecl :=
  { name := "currentLength"
    params := []
    returnType := some uint256
    body :=
      [ .require (.binary .eq (.env .callvalue) (.intLit 0)),
        .return (.arrayLength .storage currentRef) ] }

def historyLengthGetter : TransitionDecl :=
  { name := "historyLength"
    params := []
    returnType := some uint256
    body :=
      [ .require (.binary .eq (.env .callvalue) (.intLit 0)),
        .return (.arrayLength .storage historyRef) ] }

def rawLengthGetter : TransitionDecl :=
  { name := "rawLength"
    params := []
    returnType := some uint256
    body :=
      [ .require (.binary .eq (.env .callvalue) (.intLit 0)),
        .return (.arrayLength .storage rawRef) ] }

def stringStoreContract : ContractDecl :=
  { name := "StringStore"
    storage := storageDecls
    ctor := { params := [], body := [] }
    transitions :=
      [ setTransition, appendToHistoryTransition, replaceFromHistoryTransition, dropLastTransition,
        clearCurrentTransition, clearAllTransition, storeRawTransition, currentLengthGetter,
        historyLengthGetter, rawLengthGetter ] }

/-! ## Hand-written Solidity storage layout

Solidity dynamic `bytes`/`string` values use one base slot.  Short values (`length < 32`) store
`length * 2` in the low byte and pack bytes into the high-order bytes of that same word.  Long
values store `length * 2 + 1` in the base slot and put data at `keccak256(baseSlot)`.

This layout exposes the base-slot length and byte-element refs used by the parametric
`.string`/`.bytes` storage operations in `Solm.Semantics`; the Solidity-specific representation
transition is delegated to `solidityPrepareBytesWrite?`.
-/

def uint256Loc (slot : Ethereum.UInt256) : StorageLoc :=
  { slot := slot, offset := 0, size := 32, hbound := by decide, type := .int uint256Int }

def uint8Loc (slot : Ethereum.UInt256) (offset : Fin 32) : StorageLoc :=
  { slot := slot, offset := offset, size := 1, hbound := by omega, type := .int uint8Int }

def bytesLikeDataBase (baseSlot : Ethereum.UInt256) : Ethereum.UInt256 :=
  Ethereum.uInt256OfByteArray (ffi.KEC baseSlot.toByteArray)

def historyElemBase (index : KeyValue) : Ethereum.UInt256 :=
  bytesLikeDataBase ⟨1⟩ + Ethereum.UInt256.ofNat (keyValueToWord index).toNat

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
            (Fin.ofNat 32 (idx % 32)))
  | _ => none

def stringStoreLayout : EvaledStorageRef -> EVM.State -> Option StorageLoc
  | { base := "current", steps := [.length] }, evm => some (bytesLikeLengthLoc ⟨0⟩ evm)
  | { base := "current", steps := [.aindex i] }, evm => bytesLikeByteLoc? ⟨0⟩ i evm
  | { base := "history", steps := [.length] }, _ => some (uint256Loc ⟨1⟩)
  | { base := "history", steps := [.aindex i, .length] }, evm =>
      some (bytesLikeLengthLoc (historyElemBase i) evm)
  | { base := "history", steps := [.aindex i, .aindex j] }, evm =>
      bytesLikeByteLoc? (historyElemBase i) j evm
  | { base := "raw", steps := [.length] }, evm => some (bytesLikeLengthLoc ⟨2⟩ evm)
  | { base := "raw", steps := [.aindex i] }, evm => bytesLikeByteLoc? ⟨2⟩ i evm
  | _, _ => none

def stringStoreStorageLayout : StorageLayout where
  layout := stringStoreLayout
  readBytesLength := solidityReadBytesLength? stringStoreLayout
  prepareBytesWrite := solidityPrepareBytesWrite? stringStoreLayout
  writeBytes := solidityWriteBytes? stringStoreLayout

end StringStore

def stringStoreConfig : Config :=
  { storage := StringStore.stringStoreStorageLayout
    externalABI := defaultExternalCallABI
    selfDeployment :=
      genSolidityConstructorDeployment StringStore.stringStoreContract.ctor.params }

@[simp] theorem stringStoreConfig_storage_current_length :
    stringStoreConfig.storage.layout { base := "current", steps := [.length] } =
      fun evm => some (StringStore.bytesLikeLengthLoc ⟨0⟩ evm) :=
  rfl

@[simp] theorem stringStoreConfig_storage_history_length :
    stringStoreConfig.storage.layout { base := "history", steps := [.length] } =
      fun _ => some (StringStore.uint256Loc ⟨1⟩) :=
  rfl

@[simp] theorem stringStoreConfig_storage_raw_length :
    stringStoreConfig.storage.layout { base := "raw", steps := [.length] } =
      fun evm => some (StringStore.bytesLikeLengthLoc ⟨2⟩ evm) :=
  rfl
