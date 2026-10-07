import Solm.SolidityLayout
import Solm.Semantics.ValueOps

/-!
# Solidity storage backend

The generic Solm semantics only knows `StorageBackend`.  This module implements that interface for
Solidity, given a storage locator such as one produced by `solidityLayout!`.

The recursive behavior is driven by the supplied `StorageType`: elementary leaves use the locator,
structs and arrays recurse over their components, mappings are non-enumerable, and bytes/string use
Solidity's short/long representation in this module.

The locator is state-independent. The only state-dependent addressing in Solidity — where the
`i`-th byte of a bytes/string lives, which depends on its short/long encoding — is resolved here,
from the symbolic `StorageAddr.byte` the locator returns.
-/

namespace Solm
open ABI

inductive StorageReadResult (α : Type) where
  | ok : α -> StorageReadResult α
  | revert : StorageReadResult α
  | error : StorageReadResult α
  deriving Repr

def clearSolidityBytesDataWords (evm : EVM.State) (baseSlot : EVM.Word) :
    Nat -> EVM.State
  | 0 => evm
  | n+1 =>
      let evm1 := EVM.storageStore evm evm.executionEnv.codeOwner
        (solidityBytesDataSlot baseSlot n) ⟨0⟩
      clearSolidityBytesDataWords evm1 baseSlot n

def clearSolidityBytesDataWordsFrom (evm : EVM.State) (baseSlot : EVM.Word)
    (idx : Nat) : Nat -> EVM.State
  | 0 => evm
  | n+1 =>
      let evm1 := EVM.storageStore evm evm.executionEnv.codeOwner
        (solidityBytesDataSlot baseSlot idx) ⟨0⟩
      clearSolidityBytesDataWordsFrom evm1 baseSlot (idx + 1) n

/-- The whole-word location of a header slot, read as the length of a dynamic array. -/
def solidityAnchorWordLoc (slot : EVM.Word) : StorageLoc :=
  { slot := slot, offset := 0, size := 32, bitOffset := none,
    type := .int (.uint ⟨256, by decide⟩), hbound := by decide }

/-- The location of the `index`-th byte of the bytes/string whose header is at `header`.
    Short values are stored left-aligned in the header slot; long values left-aligned in the data
    words starting at `keccak256(header)`. A short value has at most 31 bytes. -/
def solidityByteLoc? (evm : EVM.State) (header : EVM.Word) (index : Nat) : Option StorageLoc :=
  if checkBytesPacked header evm then
    if index < 31 then
      some { slot := header, offset := Fin.ofNat 32 (31 - index), size := 1, bitOffset := none,
             type := .int (.uint ⟨8, by decide⟩), hbound := by simp only [Fin.val_ofNat]; omega }
    else none
  else
    some { slot := solidityBytesDataSlot header (index / 32), offset := Fin.ofNat 32 (31 - index % 32),
           size := 1, bitOffset := none, type := .int (.uint ⟨8, by decide⟩),
           hbound := by simp only [Fin.val_ofNat]; omega }

/-- Resolve the physical location of a primitive value. -/
def solidityLeafLoc? (layout : StorageLayout) (er : EvaledStorageRef) (evm : EVM.State) :
    Option StorageLoc :=
  match layout er with
  | some (.leaf loc) => some loc
  | some (.byte header index) => solidityByteLoc? evm header index
  | _ => none

/-- The header slot of a dynamically-sized value. -/
def solidityAnchor? (layout : StorageLayout) (er : EvaledStorageRef) : Option EVM.Word :=
  match layout er with
  | some (.anchor slot) => some slot
  | _ => none

/-- The length location of a dynamic array. -/
def solidityLengthLoc? (layout : StorageLayout) (er : EvaledStorageRef) : Option StorageLoc :=
  (solidityAnchor? layout er).map solidityAnchorWordLoc

def solidityDecodeBytesLengthHeader (header : EVM.Word) : StorageReadResult Nat :=
  let flag := Ethereum.UInt256.land header ⟨1⟩
  let rawLen := Ethereum.UInt256.div header ⟨2⟩
  let lenWord := if flag = ⟨0⟩ then Ethereum.UInt256.land rawLen ⟨127⟩ else rawLen
  if Ethereum.UInt256.sub flag (Ethereum.UInt256.lt lenWord ⟨32⟩) = ⟨0⟩ then
    .revert
  else
    .ok lenWord.toNat

def solidityBytesBaseSlotAndLength?
    (layout : StorageLayout)
    (er : EvaledStorageRef) (evm : EVM.State) : StorageReadResult (EVM.Word × Nat) :=
  match solidityAnchor? layout er with
  | some baseSlot =>
      match solidityDecodeBytesLengthHeader (EVM.storageLoad evm evm.executionEnv.codeOwner baseSlot) with
      | .ok len => .ok (baseSlot, len)
      | .revert => .revert
      | .error => .error
  | none => .error

def solidityReadBytesLength?
    (layout : StorageLayout)
    (er : EvaledStorageRef) (evm : EVM.State) : Option (StorageReadResult Nat) := do
  let baseSlot <- solidityAnchor? layout er
  let header := EVM.storageLoad evm evm.executionEnv.codeOwner baseSlot
  some (solidityDecodeBytesLengthHeader header)

def solidityBytesHeaderWord (len : Nat) : EVM.Word :=
  if len < 32 then
    Ethereum.UInt256.ofNat (len * 2)
  else
    Ethereum.UInt256.ofNat (len * 2 + 1)

def solidityBytesDataWordCount (len : Nat) : Nat :=
  (len + 31) / 32

def solidityShortBytesWord (bytes : ByteArray) : EVM.Word :=
  Ethereum.UInt256.lor
    (Ethereum.uInt256OfByteArray (bytes.readWithPadding 0 32))
    (Ethereum.UInt256.ofNat (bytes.size * 2))

def writeSolidityBytesDataWordsFrom (evm : EVM.State) (baseSlot : EVM.Word)
    (bytes : ByteArray) (idx : Nat) : Nat -> EVM.State
  | 0 => evm
  | n+1 =>
      let word := Ethereum.uInt256OfByteArray (bytes.readWithPadding (idx * 32) 32)
      let evm1 := EVM.storageStore evm evm.executionEnv.codeOwner
        (solidityBytesDataSlot baseSlot idx) word
      writeSolidityBytesDataWordsFrom evm1 baseSlot bytes (idx + 1) n

def readSolidityBytesDataWordsFrom (evm : EVM.State) (baseSlot : EVM.Word)
    (idx : Nat) : Nat -> ByteArray
  | 0 => ByteArray.empty
  | n+1 =>
      let wordBytes :=
        (EVM.storageLoad evm evm.executionEnv.codeOwner
          (solidityBytesDataSlot baseSlot idx)).toByteArray
      wordBytes ++ readSolidityBytesDataWordsFrom evm baseSlot (idx + 1) n

@[simp] theorem solidityWord_toByteArray_size (word : EVM.Word) :
    word.toByteArray.size = 32 := by
  simpa [Ethereum.UInt256.toByteArray, Ethereum.UInt256.toByteArrayWithSizeProof] using
    (Ethereum.UInt256.toByteArrayWithSizeProof word).2

@[simp] theorem readSolidityBytesDataWordsFrom_size
    (evm : EVM.State) (baseSlot : EVM.Word) (idx n : Nat) :
    (readSolidityBytesDataWordsFrom evm baseSlot idx n).size = 32 * n := by
  induction n generalizing idx with
  | zero => simp [readSolidityBytesDataWordsFrom]
  | succ n ih =>
      simp [readSolidityBytesDataWordsFrom, ih, ByteArray.size_append,
        Nat.mul_succ, Nat.add_comm]

def solidityReadBytesValue?
    (layout : StorageLayout)
    (er : EvaledStorageRef) (evm : EVM.State) : StorageReadResult Value :=
  match solidityBytesBaseSlotAndLength? layout er evm with
  | .ok (baseSlot, len) =>
      if len < 32 then
        let header := EVM.storageLoad evm evm.executionEnv.codeOwner baseSlot
        .ok (.bytes (header.toByteArray.extract 0 len))
      else
        let bytes := readSolidityBytesDataWordsFrom evm baseSlot 0
          (solidityBytesDataWordCount len)
        .ok (.bytes (bytes.extract 0 len))
  | .revert => .revert
  | .error => .error

def solidityPrepareBytesWrite?
    (layout : StorageLayout)
    (er : EvaledStorageRef) (newLen : Nat) (evm : EVM.State) : StorageReadResult EVM.State :=
  match solidityBytesBaseSlotAndLength? layout er evm with
  | .ok (baseSlot, oldLen) =>
      let oldPacked := checkBytesPacked baseSlot evm
      let evmLen := EVM.storageStore evm evm.executionEnv.codeOwner baseSlot
        (solidityBytesHeaderWord newLen)
      .ok <|
        let evmOldClear :=
          if oldPacked then
            evmLen
          else
            clearSolidityBytesDataWordsFrom evmLen baseSlot 0 ((oldLen + 31) / 32)
        if newLen < 32 then
          evmOldClear
        else
          clearSolidityBytesDataWordsFrom evmOldClear baseSlot 0 ((newLen + 31) / 32)
  | .revert => .revert
  | .error => .error

def solidityWriteBytesValue?
    (layout : StorageLayout)
    (er : EvaledStorageRef) (bytes : ByteArray) (evm : EVM.State) :
    StorageReadResult EVM.State :=
  match solidityBytesBaseSlotAndLength? layout er evm with
  | .ok (baseSlot, oldLen) =>
      if bytes.size < 32 then
        let oldPacked := checkBytesPacked baseSlot evm
        let evmClean :=
          if oldPacked then
            evm
          else
            clearSolidityBytesDataWordsFrom evm baseSlot 0
              (solidityBytesDataWordCount oldLen)
        .ok <|
          EVM.storageStore evmClean evmClean.executionEnv.codeOwner baseSlot
            (solidityShortBytesWord bytes)
      else
        let oldPacked := checkBytesPacked baseSlot evm
        let newWords := solidityBytesDataWordCount bytes.size
        let oldWords := solidityBytesDataWordCount oldLen
        let evmClean :=
          if oldPacked then
            evm
          else
            clearSolidityBytesDataWordsFrom evm baseSlot newWords (oldWords - newWords)
        let evmData := writeSolidityBytesDataWordsFrom evmClean baseSlot bytes 0 newWords
        .ok <|
          EVM.storageStore evmData evmData.executionEnv.codeOwner baseSlot
            (solidityBytesHeaderWord bytes.size)
  | .revert => .revert
  | .error => .error

def solidityNatResultToEval : StorageReadResult Nat -> EvalResult Nat
  | .ok n => .ok n
  | .revert => .revert
  | .error => .error .storageError

def solidityStateResultToEval : StorageReadResult EVM.State -> EvalResult EVM.State
  | .ok evm => .ok evm
  | .revert => .revert
  | .error => .error .storageError

def solidityValueResultToEval : StorageReadResult Value -> EvalResult Value
  | .ok value => .ok value
  | .revert => .revert
  | .error => .error .storageError

def solidityDynamicLength? (layout : StorageLayout) (evm : EVM.State)
    (er : EvaledStorageRef) : EvalResult Nat := do
  let lenLoc <- EvalResult.ofOption .storageError (solidityLengthLoc? layout er)
  match storageLocLoad evm lenLoc with
  | .int len =>
      if len < 0 then .error .storageError else .ok len.toNat
  | _ => .error .storageError

mutual

/-- Solidity `delete`: recursively clear all enumerable storage occupied by `ty` at `er`.
Mappings are deliberately skipped because their keys cannot be enumerated. -/
def solidityClearStorage? (layout : StorageLayout) (evm : EVM.State)
    (er : EvaledStorageRef) : StorageType -> EvalResult EVM.State
  | .elem _ | .contract _ => do
      let loc <- EvalResult.ofOption .storageError (solidityLeafLoc? layout er evm)
      EvalResult.ofOption .storageError (storageLocStore evm loc (.int 0))
  | .mapping _ _ => .ok evm
  | .struct _ fields => solidityClearFields? layout evm er fields
  | .tuple types => solidityClearTuple? layout evm er 0 types
  | .array elem count => solidityClearArray? layout evm er elem count
  | .dynamicArray elem => do
      let length <- solidityDynamicLength? layout evm er
      let evm' <- solidityClearArray? layout evm er elem length
      let lenLoc <- EvalResult.ofOption .storageError (solidityLengthLoc? layout er)
      EvalResult.ofOption .storageError (storageLocStore evm' lenLoc (.int 0))
  | .bytes | .string =>
      solidityStateResultToEval (solidityPrepareBytesWrite? layout er 0 evm)
  termination_by ty => (sizeOf ty, 0)

def solidityClearFields? (layout : StorageLayout) (evm : EVM.State)
    (er : EvaledStorageRef) : List (Ident × StorageType) -> EvalResult EVM.State
  | [] => .ok evm
  | (name, ty) :: rest => do
      let evm' <- solidityClearStorage? layout evm
        { er with steps := er.steps ++ [.field name] } ty
      solidityClearFields? layout evm' er rest
  termination_by fields => (sizeOf fields, 0)

def solidityClearTuple? (layout : StorageLayout) (evm : EVM.State)
    (er : EvaledStorageRef) (index : Nat) : List StorageType -> EvalResult EVM.State
  | [] => .ok evm
  | ty :: rest => do
      let evm' <- solidityClearStorage? layout evm
        { er with steps := er.steps ++ [.tupleElem index] } ty
      solidityClearTuple? layout evm' er (index + 1) rest
  termination_by types => (sizeOf types, 0)

def solidityClearArray? (layout : StorageLayout) (evm : EVM.State)
    (er : EvaledStorageRef) (elem : StorageType) : Nat -> EvalResult EVM.State
  | 0 => .ok evm
  | count + 1 => do
      let evm' <- solidityClearStorage? layout evm
        { er with steps := er.steps ++ [.aindex (.int count)] } elem
      solidityClearArray? layout evm' er elem count
  termination_by count => (sizeOf elem, count)

end

mutual

/-- Write a typed Solidity storage value, recursively handling aggregate values. -/
def solidityWriteStorage? (layout : StorageLayout) (evm : EVM.State)
    (er : EvaledStorageRef) : StorageType -> Value -> EvalResult EVM.State
  | .elem _, value
  | .contract _, value => do
      let loc <- EvalResult.ofOption .storageError (solidityLeafLoc? layout er evm)
      EvalResult.ofOption .storageError (storageLocStore evm loc value)
  | .struct expected fields, .struct actual values =>
      if expected = actual then solidityWriteFields? layout evm er fields values
      else .error .typeError
  | .tuple types, .tuple values => solidityWriteTuple? layout evm er 0 types values
  | .array elem count, .array values =>
      if values.length = count then solidityWriteArray? layout evm er elem 0 values
      else .error .typeError
  | .dynamicArray elem, .array values => do
      -- Clear first so assigning a shorter array cannot leave reachable stale elements.
      let evm' <- solidityClearStorage? layout evm er (.dynamicArray elem)
      let evm'' <- solidityWriteArray? layout evm' er elem 0 values
      let lenLoc <- EvalResult.ofOption .storageError (solidityLengthLoc? layout er)
      EvalResult.ofOption .storageError (storageLocStore evm'' lenLoc (.int values.length))
  | .bytes, .bytes bytes
  | .string, .bytes bytes =>
      solidityStateResultToEval (solidityWriteBytesValue? layout er bytes evm)
  | _, _ => .error .typeError
  termination_by ty => (sizeOf ty, 0)

def solidityWriteFields? (layout : StorageLayout) (evm : EVM.State)
    (er : EvaledStorageRef) :
    List (Ident × StorageType) -> List (Ident × Value) -> EvalResult EVM.State
  | [], [] => .ok evm
  | (name, ty) :: typeRest, (actual, value) :: valueRest =>
      if name = actual then do
        let evm' <- solidityWriteStorage? layout evm
          { er with steps := er.steps ++ [.field name] } ty value
        solidityWriteFields? layout evm' er typeRest valueRest
      else .error .typeError
  | _, _ => .error .typeError
  termination_by types => (sizeOf types, 0)

def solidityWriteTuple? (layout : StorageLayout) (evm : EVM.State)
    (er : EvaledStorageRef) (index : Nat) :
    List StorageType -> List Value -> EvalResult EVM.State
  | [], [] => .ok evm
  | ty :: typeRest, value :: valueRest => do
      let evm' <- solidityWriteStorage? layout evm
        { er with steps := er.steps ++ [.tupleElem index] } ty value
      solidityWriteTuple? layout evm' er (index + 1) typeRest valueRest
  | _, _ => .error .typeError
  termination_by types => (sizeOf types, 0)

def solidityWriteArray? (layout : StorageLayout) (evm : EVM.State)
    (er : EvaledStorageRef) (elem : StorageType) (index : Nat) :
    List Value -> EvalResult EVM.State
  | [] => .ok evm
  | value :: rest => do
      let evm' <- solidityWriteStorage? layout evm
        { er with steps := er.steps ++ [.aindex (.int index)] } elem value
      solidityWriteArray? layout evm' er elem (index + 1) rest
  termination_by values => (sizeOf elem, sizeOf values)

end

mutual

/-- Read a typed Solidity storage value, recursively reconstructing aggregate values. -/
def solidityReadStorage? (layout : StorageLayout) (evm : EVM.State)
    (er : EvaledStorageRef) : StorageType -> EvalResult Value
  | .elem _ | .contract _ => do
      let loc <- EvalResult.ofOption .storageError (solidityLeafLoc? layout er evm)
      pure (storageLocLoad evm loc)
  | .mapping _ _ => .error .typeError
  | .struct name fields => do
      let values <- solidityReadFields? layout evm er fields
      pure (.struct name values)
  | .tuple types => do
      let values <- solidityReadTuple? layout evm er 0 types
      pure (.tuple values)
  | .array elem count => do
      let values <- solidityReadArray? layout evm er elem 0 count
      pure (.array values)
  | .dynamicArray elem => do
      let length <- solidityDynamicLength? layout evm er
      let values <- solidityReadArray? layout evm er elem 0 length
      pure (.array values)
  | .bytes | .string =>
      solidityValueResultToEval (solidityReadBytesValue? layout er evm)
  termination_by ty => (sizeOf ty, 0)

def solidityReadFields? (layout : StorageLayout) (evm : EVM.State)
    (er : EvaledStorageRef) :
    List (Ident × StorageType) -> EvalResult (List (Ident × Value))
  | [] => .ok []
  | (name, ty) :: rest => do
      let value <- solidityReadStorage? layout evm
        { er with steps := er.steps ++ [.field name] } ty
      let values <- solidityReadFields? layout evm er rest
      pure ((name, value) :: values)
  termination_by fields => (sizeOf fields, 0)

def solidityReadTuple? (layout : StorageLayout) (evm : EVM.State)
    (er : EvaledStorageRef) (index : Nat) :
    List StorageType -> EvalResult (List Value)
  | [] => .ok []
  | ty :: rest => do
      let value <- solidityReadStorage? layout evm
        { er with steps := er.steps ++ [.tupleElem index] } ty
      let values <- solidityReadTuple? layout evm er (index + 1) rest
      pure (value :: values)
  termination_by types => (sizeOf types, 0)

def solidityReadArray? (layout : StorageLayout) (evm : EVM.State)
    (er : EvaledStorageRef) (elem : StorageType) (index : Nat) :
    Nat -> EvalResult (List Value)
  | 0 => .ok []
  | count + 1 => do
      let value <- solidityReadStorage? layout evm
        { er with steps := er.steps ++ [.aindex (.int index)] } elem
      let values <- solidityReadArray? layout evm er elem (index + 1) count
      pure (value :: values)
  termination_by count => (sizeOf elem, count)

end

/-- Solidity length operation for fixed/dynamic arrays, fixed/dynamic bytes, and strings. -/
def solidityStorageLength? (layout : StorageLayout) (er : EvaledStorageRef)
    (ty : StorageType) (evm : EVM.State) : EvalResult Nat :=
  match ty with
  | .array _ count => .ok count
  | .elem (.bytes width) => .ok (fixedBytesSize width)
  | .dynamicArray _ => solidityDynamicLength? layout evm er
  | .bytes | .string =>
      match solidityReadBytesLength? layout er evm with
      | some result => solidityNatResultToEval result
      | none => .error .storageError
  | _ => .error .typeError

/-- Solidity `push`, including valueless dynamic-array growth and one-byte bytes/string pushes. -/
def solidityPushStorage? (layout : StorageLayout) (er : EvaledStorageRef)
    (ty : StorageType) (value : Option Value) (evm : EVM.State) : EvalResult EVM.State :=
  match ty with
  | .dynamicArray elem => do
      let length <- solidityDynamicLength? layout evm er
      let lenLoc <- EvalResult.ofOption .storageError (solidityLengthLoc? layout er)
      let evm' <- EvalResult.ofOption .storageError
        (storageLocStore evm lenLoc (.int (length + 1)))
      match value with
      | some element =>
          solidityWriteStorage? layout evm'
            { er with steps := er.steps ++ [.aindex (.int length)] } elem element
      | none => .ok evm'
  | .bytes | .string => do
      let stored <- solidityReadStorage? layout evm er ty
      match stored, value with
      | .bytes bytes, none =>
          solidityWriteStorage? layout evm er ty (.bytes (bytes.push 0))
      | .bytes bytes, some (.fixedBytes width byte) =>
          if width.val = 0 && byte.length = 1 then
            solidityWriteStorage? layout evm er ty
              (.bytes (bytes ++ ByteArray.mk byte.toArray))
          else .error .typeError
      | .bytes _, some _ => .error .typeError
      | _, _ => .error .storageError
  | _ => .error .storageError

/-- Solidity `pop`: revert on empty values and clear the removed dynamic-array element. -/
def solidityPopStorage? (layout : StorageLayout) (er : EvaledStorageRef)
    (ty : StorageType) (evm : EVM.State) : EvalResult EVM.State :=
  match ty with
  | .dynamicArray elem => do
      let length <- solidityDynamicLength? layout evm er
      if length = 0 then .revert
      else do
        let newLength := length - 1
        let evm' <- solidityClearStorage? layout evm
          { er with steps := er.steps ++ [.aindex (.int newLength)] } elem
        let lenLoc <- EvalResult.ofOption .storageError (solidityLengthLoc? layout er)
        EvalResult.ofOption .storageError (storageLocStore evm' lenLoc (.int newLength))
  | .bytes | .string => do
      let stored <- solidityReadStorage? layout evm er ty
      match stored with
      | .bytes bytes =>
          if bytes.size = 0 then .revert
          else
            (solidityWriteStorage? layout evm er ty
              (Value.bytes (bytes.extract 0 (bytes.size - 1))))
      | _ => .error .storageError
  | _ => .error .storageError

/-- Construct a complete Solidity storage backend from a storage locator. -/
def solidityStorageBackend (layout : StorageLayout) : StorageBackend :=
  { read := fun er ty evm => solidityReadStorage? layout evm er ty
    write := fun er ty value evm => solidityWriteStorage? layout evm er ty value
    clear := fun er ty evm => solidityClearStorage? layout evm er ty
    length := fun er ty evm => solidityStorageLength? layout er ty evm
    push := fun er ty value evm => solidityPushStorage? layout er ty value evm
    pop := fun er ty evm => solidityPopStorage? layout er ty evm
    locate? := layout }

@[simp] theorem solidityStorageBackend_locate (layout : StorageLayout) :
    (solidityStorageBackend layout).locate? = layout := rfl

@[simp] theorem solidityLeafLoc?_of_leaf {layout : StorageLayout} {er : EvaledStorageRef}
    {loc : StorageLoc} (hloc : layout er = some (.leaf loc)) (evm : EVM.State) :
    solidityLeafLoc? layout er evm = some loc := by
  simp [solidityLeafLoc?, hloc]

@[simp] theorem solidityAnchor?_of_anchor {layout : StorageLayout} {er : EvaledStorageRef}
    {slot : EVM.Word} (hloc : layout er = some (.anchor slot)) :
    solidityAnchor? layout er = some slot := by
  simp [solidityAnchor?, hloc]

@[simp] theorem solidityStorageBackend_read_elem (layout : StorageLayout)
    (er : EvaledStorageRef) (ty : ElemType) (evm : EVM.State) (loc : StorageLoc)
    (hloc : layout er = some (.leaf loc)) :
    (solidityStorageBackend layout).read er (.elem ty) evm = .ok (storageLocLoad evm loc) := by
  simp only [solidityStorageBackend, solidityReadStorage?, solidityLeafLoc?_of_leaf hloc]
  rfl

@[simp] theorem solidityStorageBackend_write_elem (layout : StorageLayout)
    (er : EvaledStorageRef) (ty : ElemType) (value : Value) (evm evm' : EVM.State)
    (loc : StorageLoc) (hloc : layout er = some (.leaf loc))
    (hstore : storageLocStore evm loc value = some evm') :
    (solidityStorageBackend layout).write er (.elem ty) value evm = .ok evm' := by
  simp [solidityStorageBackend, solidityWriteStorage?, solidityLeafLoc?_of_leaf hloc, hstore,
    EvalResult.ofOption, EvalResult.bind, bind]

end Solm
