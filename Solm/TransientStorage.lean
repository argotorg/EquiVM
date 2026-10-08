import Solm.SolidityStorage

/-!
# Solidity transient storage

Transient storage uses the same layout and encoding as persistent storage, but its backend
reads and writes the executing account's `tstorage` directly. Keep the stateful operations
here until the backend interface can operate on a storage map instead of an EVM state.
-/

namespace Solm
open ABI

/-- Whether a transient bytes/string header uses Solidity's short encoding. -/
def transientCheckBytesPacked (slot : EVM.Word) (state : EVM.State) : Bool :=
  let header := EVM.transientLoad state state.executionEnv.codeOwner slot
  (header.val % 2) == 0

def clearTransientBytesDataWordsFrom (evm : EVM.State) (baseSlot : EVM.Word)
    (idx : Nat) : Nat -> EVM.State
  | 0 => evm
  | n+1 =>
      let evm1 := EVM.transientStore evm evm.executionEnv.codeOwner
        (solidityBytesDataSlot baseSlot idx) ⟨0⟩
      clearTransientBytesDataWordsFrom evm1 baseSlot (idx + 1) n


/-- The location of the `index`-th byte of the bytes/string whose header is at `header`.
    Short values are stored left-aligned in the header slot; long values left-aligned in the data
    words starting at `keccak256(header)`. A short value has at most 31 bytes. -/
def transientSolidityByteLoc? (evm : EVM.State) (header : EVM.Word) (index : Nat) : Option StorageLoc :=
  if transientCheckBytesPacked header evm then
    if index < 31 then
      some { slot := header, offset := Fin.ofNat 32 (31 - index), size := 1, bitOffset := none,
             type := .int (.uint ⟨8, by decide⟩), hbound := by simp only [Fin.val_ofNat]; omega }
    else none
  else
    some { slot := solidityBytesDataSlot header (index / 32), offset := Fin.ofNat 32 (31 - index % 32),
           size := 1, bitOffset := none, type := .int (.uint ⟨8, by decide⟩),
           hbound := by simp only [Fin.val_ofNat]; omega }

/-- Resolve the physical location of a primitive value. -/
def transientSolidityLeafLoc? (layout : StorageLayout) (er : EvaledStorageRef) (evm : EVM.State) :
    Option StorageLoc :=
  match layout er with
  | some (.leaf loc) => some loc
  | some (.byte header index) => transientSolidityByteLoc? evm header index
  | _ => none


def transientSolidityBytesBaseSlotAndLength?
    (layout : StorageLayout)
    (er : EvaledStorageRef) (evm : EVM.State) : StorageReadResult (EVM.Word × Nat) :=
  match solidityAnchor? layout er with
  | some baseSlot =>
      match solidityDecodeBytesLengthHeader (EVM.transientLoad evm evm.executionEnv.codeOwner baseSlot) with
      | .ok len => .ok (baseSlot, len)
      | .revert => .revert
      | .error => .error
  | none => .error

def transientSolidityReadBytesLength?
    (layout : StorageLayout)
    (er : EvaledStorageRef) (evm : EVM.State) : Option (StorageReadResult Nat) := do
  let baseSlot <- solidityAnchor? layout er
  let header := EVM.transientLoad evm evm.executionEnv.codeOwner baseSlot
  some (solidityDecodeBytesLengthHeader header)


def writeTransientBytesDataWordsFrom (evm : EVM.State) (baseSlot : EVM.Word)
    (bytes : ByteArray) (idx : Nat) : Nat -> EVM.State
  | 0 => evm
  | n+1 =>
      let word := Ethereum.uInt256OfByteArray (bytes.readWithPadding (idx * 32) 32)
      let evm1 := EVM.transientStore evm evm.executionEnv.codeOwner
        (solidityBytesDataSlot baseSlot idx) word
      writeTransientBytesDataWordsFrom evm1 baseSlot bytes (idx + 1) n

def readTransientBytesDataWordsFrom (evm : EVM.State) (baseSlot : EVM.Word)
    (idx : Nat) : Nat -> ByteArray
  | 0 => ByteArray.empty
  | n+1 =>
      let wordBytes :=
        (EVM.transientLoad evm evm.executionEnv.codeOwner
          (solidityBytesDataSlot baseSlot idx)).toByteArray
      wordBytes ++ readTransientBytesDataWordsFrom evm baseSlot (idx + 1) n


def transientSolidityReadBytesValue?
    (layout : StorageLayout)
    (er : EvaledStorageRef) (evm : EVM.State) : StorageReadResult Value :=
  match transientSolidityBytesBaseSlotAndLength? layout er evm with
  | .ok (baseSlot, len) =>
      if len < 32 then
        let header := EVM.transientLoad evm evm.executionEnv.codeOwner baseSlot
        .ok (.bytes (header.toByteArray.extract 0 len))
      else
        let bytes := readTransientBytesDataWordsFrom evm baseSlot 0
          (solidityBytesDataWordCount len)
        .ok (.bytes (bytes.extract 0 len))
  | .revert => .revert
  | .error => .error

def transientSolidityPrepareBytesWrite?
    (layout : StorageLayout)
    (er : EvaledStorageRef) (newLen : Nat) (evm : EVM.State) : StorageReadResult EVM.State :=
  match transientSolidityBytesBaseSlotAndLength? layout er evm with
  | .ok (baseSlot, oldLen) =>
      let oldPacked := transientCheckBytesPacked baseSlot evm
      let evmLen := EVM.transientStore evm evm.executionEnv.codeOwner baseSlot
        (solidityBytesHeaderWord newLen)
      .ok <|
        let evmOldClear :=
          if oldPacked then
            evmLen
          else
            clearTransientBytesDataWordsFrom evmLen baseSlot 0 ((oldLen + 31) / 32)
        if newLen < 32 then
          evmOldClear
        else
          clearTransientBytesDataWordsFrom evmOldClear baseSlot 0 ((newLen + 31) / 32)
  | .revert => .revert
  | .error => .error

def transientSolidityWriteBytesValue?
    (layout : StorageLayout)
    (er : EvaledStorageRef) (bytes : ByteArray) (evm : EVM.State) :
    StorageReadResult EVM.State :=
  match transientSolidityBytesBaseSlotAndLength? layout er evm with
  | .ok (baseSlot, oldLen) =>
      if bytes.size < 32 then
        let oldPacked := transientCheckBytesPacked baseSlot evm
        let evmClean :=
          if oldPacked then
            evm
          else
            clearTransientBytesDataWordsFrom evm baseSlot 0
              (solidityBytesDataWordCount oldLen)
        .ok <|
          EVM.transientStore evmClean evmClean.executionEnv.codeOwner baseSlot
            (solidityShortBytesWord bytes)
      else
        let oldPacked := transientCheckBytesPacked baseSlot evm
        let newWords := solidityBytesDataWordCount bytes.size
        let oldWords := solidityBytesDataWordCount oldLen
        let evmClean :=
          if oldPacked then
            evm
          else
            clearTransientBytesDataWordsFrom evm baseSlot newWords (oldWords - newWords)
        let evmData := writeTransientBytesDataWordsFrom evmClean baseSlot bytes 0 newWords
        .ok <|
          EVM.transientStore evmData evmData.executionEnv.codeOwner baseSlot
            (solidityBytesHeaderWord bytes.size)
  | .revert => .revert
  | .error => .error


def transientSolidityDynamicLength? (layout : StorageLayout) (evm : EVM.State)
    (er : EvaledStorageRef) : EvalResult Nat := do
  let lenLoc <- EvalResult.ofOption .storageError (solidityLengthLoc? layout er)
  match transientLocLoad evm lenLoc with
  | .int len =>
      if len < 0 then .error .storageError else .ok len.toNat
  | _ => .error .storageError

mutual

/-- Solidity `delete`: recursively clear all enumerable storage occupied by `ty` at `er`.
Mappings are deliberately skipped because their keys cannot be enumerated. -/
def transientSolidityClearStorage? (layout : StorageLayout) (evm : EVM.State)
    (er : EvaledStorageRef) : StorageType -> EvalResult EVM.State
  | .elem _ | .contract _ => do
      let loc <- EvalResult.ofOption .storageError (transientSolidityLeafLoc? layout er evm)
      EvalResult.ofOption .storageError (transientLocStore evm loc (.int 0))
  | .mapping _ _ => .ok evm
  | .struct _ fields => transientSolidityClearFields? layout evm er fields
  | .tuple types => transientSolidityClearTuple? layout evm er 0 types
  | .array elem count => transientSolidityClearArray? layout evm er elem count
  | .dynamicArray elem => do
      let length <- transientSolidityDynamicLength? layout evm er
      let evm' <- transientSolidityClearArray? layout evm er elem length
      let lenLoc <- EvalResult.ofOption .storageError (solidityLengthLoc? layout er)
      EvalResult.ofOption .storageError (transientLocStore evm' lenLoc (.int 0))
  | .bytes | .string =>
      solidityStateResultToEval (transientSolidityPrepareBytesWrite? layout er 0 evm)
  termination_by ty => (sizeOf ty, 0)

def transientSolidityClearFields? (layout : StorageLayout) (evm : EVM.State)
    (er : EvaledStorageRef) : List (Ident × StorageType) -> EvalResult EVM.State
  | [] => .ok evm
  | (name, ty) :: rest => do
      let evm' <- transientSolidityClearStorage? layout evm
        { er with steps := er.steps ++ [.field name] } ty
      transientSolidityClearFields? layout evm' er rest
  termination_by fields => (sizeOf fields, 0)

def transientSolidityClearTuple? (layout : StorageLayout) (evm : EVM.State)
    (er : EvaledStorageRef) (index : Nat) : List StorageType -> EvalResult EVM.State
  | [] => .ok evm
  | ty :: rest => do
      let evm' <- transientSolidityClearStorage? layout evm
        { er with steps := er.steps ++ [.tupleElem index] } ty
      transientSolidityClearTuple? layout evm' er (index + 1) rest
  termination_by types => (sizeOf types, 0)

def transientSolidityClearArray? (layout : StorageLayout) (evm : EVM.State)
    (er : EvaledStorageRef) (elem : StorageType) : Nat -> EvalResult EVM.State
  | 0 => .ok evm
  | count + 1 => do
      let evm' <- transientSolidityClearStorage? layout evm
        { er with steps := er.steps ++ [.aindex (.int count)] } elem
      transientSolidityClearArray? layout evm' er elem count
  termination_by count => (sizeOf elem, count)

end

mutual

/-- Write a typed Solidity storage value, recursively handling aggregate values. -/
def transientSolidityWriteStorage? (layout : StorageLayout) (evm : EVM.State)
    (er : EvaledStorageRef) : StorageType -> Value -> EvalResult EVM.State
  | .elem _, value
  | .contract _, value => do
      let loc <- EvalResult.ofOption .storageError (transientSolidityLeafLoc? layout er evm)
      EvalResult.ofOption .storageError (transientLocStore evm loc value)
  | .struct expected fields, .struct actual values =>
      if expected = actual then transientSolidityWriteFields? layout evm er fields values
      else .error .typeError
  | .tuple types, .tuple values => transientSolidityWriteTuple? layout evm er 0 types values
  | .array elem count, .array values =>
      if values.length = count then transientSolidityWriteArray? layout evm er elem 0 values
      else .error .typeError
  | .dynamicArray elem, .array values => do
      -- Clear first so assigning a shorter array cannot leave reachable stale elements.
      let evm' <- transientSolidityClearStorage? layout evm er (.dynamicArray elem)
      let evm'' <- transientSolidityWriteArray? layout evm' er elem 0 values
      let lenLoc <- EvalResult.ofOption .storageError (solidityLengthLoc? layout er)
      EvalResult.ofOption .storageError (transientLocStore evm'' lenLoc (.int values.length))
  | .bytes, .bytes bytes
  | .string, .bytes bytes =>
      solidityStateResultToEval (transientSolidityWriteBytesValue? layout er bytes evm)
  | _, _ => .error .typeError
  termination_by ty => (sizeOf ty, 0)

def transientSolidityWriteFields? (layout : StorageLayout) (evm : EVM.State)
    (er : EvaledStorageRef) :
    List (Ident × StorageType) -> List (Ident × Value) -> EvalResult EVM.State
  | [], [] => .ok evm
  | (name, ty) :: typeRest, (actual, value) :: valueRest =>
      if name = actual then do
        let evm' <- transientSolidityWriteStorage? layout evm
          { er with steps := er.steps ++ [.field name] } ty value
        transientSolidityWriteFields? layout evm' er typeRest valueRest
      else .error .typeError
  | _, _ => .error .typeError
  termination_by types => (sizeOf types, 0)

def transientSolidityWriteTuple? (layout : StorageLayout) (evm : EVM.State)
    (er : EvaledStorageRef) (index : Nat) :
    List StorageType -> List Value -> EvalResult EVM.State
  | [], [] => .ok evm
  | ty :: typeRest, value :: valueRest => do
      let evm' <- transientSolidityWriteStorage? layout evm
        { er with steps := er.steps ++ [.tupleElem index] } ty value
      transientSolidityWriteTuple? layout evm' er (index + 1) typeRest valueRest
  | _, _ => .error .typeError
  termination_by types => (sizeOf types, 0)

def transientSolidityWriteArray? (layout : StorageLayout) (evm : EVM.State)
    (er : EvaledStorageRef) (elem : StorageType) (index : Nat) :
    List Value -> EvalResult EVM.State
  | [] => .ok evm
  | value :: rest => do
      let evm' <- transientSolidityWriteStorage? layout evm
        { er with steps := er.steps ++ [.aindex (.int index)] } elem value
      transientSolidityWriteArray? layout evm' er elem (index + 1) rest
  termination_by values => (sizeOf elem, sizeOf values)

end

mutual

/-- Read a typed Solidity storage value, recursively reconstructing aggregate values. -/
def transientSolidityReadStorage? (layout : StorageLayout) (evm : EVM.State)
    (er : EvaledStorageRef) : StorageType -> EvalResult Value
  | .elem _ | .contract _ => do
      let loc <- EvalResult.ofOption .storageError (transientSolidityLeafLoc? layout er evm)
      pure (transientLocLoad evm loc)
  | .mapping _ _ => .error .typeError
  | .struct name fields => do
      let values <- transientSolidityReadFields? layout evm er fields
      pure (.struct name values)
  | .tuple types => do
      let values <- transientSolidityReadTuple? layout evm er 0 types
      pure (.tuple values)
  | .array elem count => do
      let values <- transientSolidityReadArray? layout evm er elem 0 count
      pure (.array values)
  | .dynamicArray elem => do
      let length <- transientSolidityDynamicLength? layout evm er
      let values <- transientSolidityReadArray? layout evm er elem 0 length
      pure (.array values)
  | .bytes | .string =>
      solidityValueResultToEval (transientSolidityReadBytesValue? layout er evm)
  termination_by ty => (sizeOf ty, 0)

def transientSolidityReadFields? (layout : StorageLayout) (evm : EVM.State)
    (er : EvaledStorageRef) :
    List (Ident × StorageType) -> EvalResult (List (Ident × Value))
  | [] => .ok []
  | (name, ty) :: rest => do
      let value <- transientSolidityReadStorage? layout evm
        { er with steps := er.steps ++ [.field name] } ty
      let values <- transientSolidityReadFields? layout evm er rest
      pure ((name, value) :: values)
  termination_by fields => (sizeOf fields, 0)

def transientSolidityReadTuple? (layout : StorageLayout) (evm : EVM.State)
    (er : EvaledStorageRef) (index : Nat) :
    List StorageType -> EvalResult (List Value)
  | [] => .ok []
  | ty :: rest => do
      let value <- transientSolidityReadStorage? layout evm
        { er with steps := er.steps ++ [.tupleElem index] } ty
      let values <- transientSolidityReadTuple? layout evm er (index + 1) rest
      pure (value :: values)
  termination_by types => (sizeOf types, 0)

def transientSolidityReadArray? (layout : StorageLayout) (evm : EVM.State)
    (er : EvaledStorageRef) (elem : StorageType) (index : Nat) :
    Nat -> EvalResult (List Value)
  | 0 => .ok []
  | count + 1 => do
      let value <- transientSolidityReadStorage? layout evm
        { er with steps := er.steps ++ [.aindex (.int index)] } elem
      let values <- transientSolidityReadArray? layout evm er elem (index + 1) count
      pure (value :: values)
  termination_by count => (sizeOf elem, count)

end

/-- Solidity length operation for fixed/dynamic arrays, fixed/dynamic bytes, and strings. -/
def transientSolidityStorageLength? (layout : StorageLayout) (er : EvaledStorageRef)
    (ty : StorageType) (evm : EVM.State) : EvalResult Nat :=
  match ty with
  | .array _ count => .ok count
  | .elem (.bytes width) => .ok (fixedBytesSize width)
  | .dynamicArray _ => transientSolidityDynamicLength? layout evm er
  | .bytes | .string =>
      match transientSolidityReadBytesLength? layout er evm with
      | some result => solidityNatResultToEval result
      | none => .error .storageError
  | _ => .error .typeError

/-- Solidity `push`, including valueless dynamic-array growth and one-byte bytes/string pushes. -/
def transientSolidityPushStorage? (layout : StorageLayout) (er : EvaledStorageRef)
    (ty : StorageType) (value : Option Value) (evm : EVM.State) : EvalResult EVM.State :=
  match ty with
  | .dynamicArray elem => do
      let length <- transientSolidityDynamicLength? layout evm er
      let lenLoc <- EvalResult.ofOption .storageError (solidityLengthLoc? layout er)
      let evm' <- EvalResult.ofOption .storageError
        (transientLocStore evm lenLoc (.int (length + 1)))
      match value with
      | some element =>
          transientSolidityWriteStorage? layout evm'
            { er with steps := er.steps ++ [.aindex (.int length)] } elem element
      | none => .ok evm'
  | .bytes | .string => do
      let stored <- transientSolidityReadStorage? layout evm er ty
      match stored, value with
      | .bytes bytes, none =>
          transientSolidityWriteStorage? layout evm er ty (.bytes (bytes.push 0))
      | .bytes bytes, some (.fixedBytes width byte) =>
          if width.val = 0 && byte.length = 1 then
            transientSolidityWriteStorage? layout evm er ty
              (.bytes (bytes ++ ByteArray.mk byte.toArray))
          else .error .typeError
      | .bytes _, some _ => .error .typeError
      | _, _ => .error .storageError
  | _ => .error .storageError

/-- Solidity `pop`: revert on empty values and clear the removed dynamic-array element. -/
def transientSolidityPopStorage? (layout : StorageLayout) (er : EvaledStorageRef)
    (ty : StorageType) (evm : EVM.State) : EvalResult EVM.State :=
  match ty with
  | .dynamicArray elem => do
      let length <- transientSolidityDynamicLength? layout evm er
      if length = 0 then .revert
      else do
        let newLength := length - 1
        let evm' <- transientSolidityClearStorage? layout evm
          { er with steps := er.steps ++ [.aindex (.int newLength)] } elem
        let lenLoc <- EvalResult.ofOption .storageError (solidityLengthLoc? layout er)
        EvalResult.ofOption .storageError (transientLocStore evm' lenLoc (.int newLength))
  | .bytes | .string => do
      let stored <- transientSolidityReadStorage? layout evm er ty
      match stored with
      | .bytes bytes =>
          if bytes.size = 0 then .revert
          else
            (transientSolidityWriteStorage? layout evm er ty
              (Value.bytes (bytes.extract 0 (bytes.size - 1))))
      | _ => .error .storageError
  | _ => .error .storageError

/-- Construct a complete Solidity storage backend from a storage locator. -/
def solidityTransientStorageBackend (layout : StorageLayout) : StorageBackend :=
  { read := fun er ty evm => transientSolidityReadStorage? layout evm er ty
    write := fun er ty value evm => transientSolidityWriteStorage? layout evm er ty value
    clear := fun er ty evm => transientSolidityClearStorage? layout evm er ty
    length := fun er ty evm => transientSolidityStorageLength? layout er ty evm
    push := fun er ty value evm => transientSolidityPushStorage? layout er ty value evm
    pop := fun er ty evm => transientSolidityPopStorage? layout er ty evm
    locate? := layout }

@[simp] theorem solidityTransientStorageBackend_locate (layout : StorageLayout) :
    (solidityTransientStorageBackend layout).locate? = layout := rfl

@[simp] theorem solidityTransientStorageBackend_read_elem (layout : StorageLayout)
    (er : EvaledStorageRef) (ty : ABI.ElemType) (evm : EVM.State) (loc : StorageLoc)
    (hloc : layout er = some (.leaf loc)) :
    (solidityTransientStorageBackend layout).read er (.elem ty) evm =
      .ok (transientLocLoad evm loc) := by
  simp only [solidityTransientStorageBackend, transientSolidityReadStorage?,
    transientSolidityLeafLoc?, hloc]
  rfl

@[simp] theorem solidityTransientStorageBackend_write_elem (layout : StorageLayout)
    (er : EvaledStorageRef) (ty : ABI.ElemType) (value : Value) (evm evm' : EVM.State)
    (loc : StorageLoc) (hloc : layout er = some (.leaf loc))
    (hstore : transientLocStore evm loc value = some evm') :
    (solidityTransientStorageBackend layout).write er (.elem ty) value evm = .ok evm' := by
  simp [solidityTransientStorageBackend, transientSolidityWriteStorage?,
    transientSolidityLeafLoc?, hloc, hstore, EvalResult.ofOption, EvalResult.bind, bind]

end Solm
