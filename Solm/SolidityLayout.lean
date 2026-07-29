import EVM.Types
import ABI.Types
import ABI.Encode
import Solm.Value
import Solm.Storage

namespace Solm
open ABI

/-
 -
 - Solidity Layout Generation,  WIP
 -
 -/

/-
 - This is an attempt to mechanize the Solidity storage layout generation.
 - It is currently work in progress and known to be incomplete and not fully correct.
-/

-- Difference with `StorageLoc` is that size can be larger than a slot, so we can deal with broad intermediate locs
structure IntermediateStorageLoc where
  slot    : EVM.Word      -- storage slot in which item is stored
  offset  : Fin 32        -- offset within that slot in bytes
  size    : Nat           -- size (may cross into other slots)
  bitOffset : Option (Fin 8) -- offset within byte in bits; Needed for packed bytes

-- Schema of a particular instance of a solidity layout
inductive StorageNode where
  | atomic : ElemType -> StorageNode
  | indexed : (EVM.Word -> KeyValue -> EVM.State /- for packed reprs -/ -> IntermediateStorageLoc)
              -> Option (EVM.Word -> EVM.State -> StorageLoc) /- length storage location -/
              -> StorageNode
              -> StorageNode
  | fields : (Ident -> Option (IntermediateStorageLoc × StorageNode))
             -> StorageNode
  | tuples : (Nat -> Option (IntermediateStorageLoc × StorageNode))
             -> StorageNode

def elemTypeSoliditySize (t : ElemType) : Fin 33 :=
  match t with
  | .bool => 1
  | .address => 20
  | .int it => intTypeSize it
  | .fixed ft => fixedTypeSize ft
  | .bytes n => ⟨n+1, by omega⟩
  | .function => 24

def checkBytesPacked (slot : EVM.Word) (state : EVM.State) : Bool :=
  let slot := EVM.storageLoad state state.executionEnv.codeOwner slot
  (slot.val % 2) == 0

def bytesLikeLengthLoc (baseSlot : EVM.Word) (evm : EVM.State) : StorageLoc :=
  if checkBytesPacked baseSlot evm then
    { slot := baseSlot, offset := 0, size := 1, hbound := by decide,
      bitOffset := some 1, type := .int (.uint ⟨256, by decide⟩) }
  else
    { slot := baseSlot, offset := 0, size := 32, hbound := by decide,
      bitOffset := some 1, type := .int (.uint ⟨256, by decide⟩) }

def solidityBytesDataBaseSlot (baseSlot : EVM.Word) : EVM.Word :=
  Ethereum.uInt256OfByteArray (ffi.KEC baseSlot.toByteArray)

def solidityBytesDataSlot (baseSlot : EVM.Word) (wordIndex : Nat) : EVM.Word :=
  solidityBytesDataBaseSlot baseSlot + Ethereum.UInt256.ofNat wordIndex

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

def solidityDecodeBytesLengthHeader (header : EVM.Word) : StorageReadResult Nat :=
  let flag := Ethereum.UInt256.land header ⟨1⟩
  let rawLen := Ethereum.UInt256.div header ⟨2⟩
  let lenWord := if flag = ⟨0⟩ then Ethereum.UInt256.land rawLen ⟨127⟩ else rawLen
  if Ethereum.UInt256.sub flag (Ethereum.UInt256.lt lenWord ⟨32⟩) = ⟨0⟩ then
    .revert
  else
    .ok lenWord.toNat

def solidityBytesBaseSlotAndLength?
    (layout : EvaledStorageRef -> EVM.State -> Option StorageLoc)
    (er : EvaledStorageRef) (evm : EVM.State) : StorageReadResult (EVM.Word × Nat) :=
  match layout { er with steps := er.steps ++ [.length] } evm with
  | some lenLoc =>
      match solidityDecodeBytesLengthHeader (EVM.storageLoad evm evm.executionEnv.codeOwner lenLoc.slot) with
      | .ok len => .ok (lenLoc.slot, len)
      | .revert => .revert
      | .error => .error
  | none => .error

def solidityReadBytesLength?
    (layout : EvaledStorageRef -> EVM.State -> Option StorageLoc)
    (er : EvaledStorageRef) (evm : EVM.State) : Option (StorageReadResult Nat) := do
  let lenLoc <- layout { er with steps := er.steps ++ [.length] } evm
  let header := EVM.storageLoad evm evm.executionEnv.codeOwner lenLoc.slot
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
    (layout : EvaledStorageRef -> EVM.State -> Option StorageLoc)
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
    (layout : EvaledStorageRef -> EVM.State -> Option StorageLoc)
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
    (layout : EvaledStorageRef -> EVM.State -> Option StorageLoc)
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

def solidityWriteValue?
    (layout : EvaledStorageRef -> EVM.State -> Option StorageLoc)
    (er : EvaledStorageRef) (ty : StorageType) (value : Value) (evm : EVM.State) :
    Option (StorageReadResult EVM.State) :=
  match ty, value with
  | .bytes, .bytes bytes => some (solidityWriteBytesValue? layout er bytes evm)
  | .string, .bytes bytes => some (solidityWriteBytesValue? layout er bytes evm)
  | _, _ => none

def solidityReadValue?
    (layout : EvaledStorageRef -> EVM.State -> Option StorageLoc)
    (er : EvaledStorageRef) (ty : StorageType) (evm : EVM.State) :
    Option (StorageReadResult Value) :=
  match ty with
  | .bytes | .string => some (solidityReadBytesValue? layout er evm)
  | _ => none

def solidityClearValue?
    (layout : EvaledStorageRef -> EVM.State -> Option StorageLoc)
    (er : EvaledStorageRef) (ty : StorageType) (evm : EVM.State) :
    Option (StorageReadResult EVM.State) :=
  match ty with
  | .bytes | .string => some (solidityPrepareBytesWrite? layout er 0 evm)
  | _ => none

def solidityStorageLayout
    (layout : EvaledStorageRef -> EVM.State -> Option StorageLoc) : StorageLayout where
  layout := layout
  readValue? := solidityReadValue? layout
  writeValue? := solidityWriteValue? layout
  clearValue? := solidityClearValue? layout
  readBytesLength := solidityReadBytesLength? layout

mutual

-- Returns the node corresponding to the type, plus its size
def slotTypeSolidityStorageNode (structs : List StructDecl)
                                (st : StorageType)
                                : Option (Nat × StorageNode) :=
    match st with
    | .elem t => pure (elemTypeSoliditySize t, .atomic t)
    | .contract _ => pure (elemTypeSoliditySize .address, .atomic .address)
    | .array t n => do
      let (elemSize, node) <- slotTypeSolidityStorageNode structs t
      if elemSize <= 32 then
        let elemsPerWord := 32 / elemSize
        let arrayWords := (n + elemsPerWord - 1)/elemsPerWord
        let size := arrayWords*32
        pure (size,
          .indexed
            (λ word idxVal _ ↦
                let idxWord := keyValueToWord idxVal
                -- TODO: maybe go directly to nat?
                let idxNat := idxWord.toNat
                { slot := word + Ethereum.UInt256.ofNat (idxNat/elemsPerWord)
                  offset := .ofNat 32 (idxNat%elemsPerWord * elemSize)
                  size := elemSize
                  bitOffset := .none
                }) .none node)
      else
        let wordsPerElem := (elemSize + 32 - 1) / 32
        let arrayWords := n * wordsPerElem
        let size := arrayWords*32
        pure (size,
          .indexed
            (λ word idxVal _ ↦
              let idxWord := keyValueToWord idxVal
              -- TODO: maybe go directly to nat?
              let idxNat := idxWord.toNat
              { slot := word + Ethereum.UInt256.ofNat (idxNat*wordsPerElem)
                offset := 0 -- am I sure?
                size := elemSize
                bitOffset := .none
              }) .none node)
    | .mapping _ t => do
      let (size, node) <- slotTypeSolidityStorageNode structs t
      pure (32, .indexed (λ word idxVal _ ↦
        { slot := Ethereum.uInt256OfByteArray (ffi.KEC ((keyValueToWord idxVal).toByteArray ++ word.toByteArray))
          offset := 0
          size := size
          bitOffset := .none
        }) .none node)
    | .dynamicArray t => do
      let (elemSize, node) <- slotTypeSolidityStorageNode structs t
      if elemSize <= 32 then
        let elemsPerWord := 32 / elemSize
        pure (32,
          .indexed
            (λ word idxVal _ ↦
              let idxWord := keyValueToWord idxVal
              -- TODO: maybe go directly to nat?
              let idxNat := idxWord.toNat
              { slot := Ethereum.uInt256OfByteArray (ffi.KEC word.toByteArray) + Ethereum.UInt256.ofNat (idxNat/elemsPerWord)
                offset := .ofNat 32 (idxNat%elemsPerWord * elemSize)
                size := elemSize
                bitOffset := .none
              })
            (.some (λ word _ ↦
              { slot := word
                offset := 0
                size := 32
                bitOffset := .none
                type := .int (.uint ⟨256, (by simp), (by simp)⟩)
                hbound := (by simp)
                : StorageLoc
              }))
            node)
      else
        let wordsPerElem := (elemSize + 32 - 1) / 32
        pure (32,
          .indexed
            (λ word idxVal _ ↦
              let idxWord := keyValueToWord idxVal
              -- TODO: maybe go directly to nat?
              let idxNat := idxWord.toNat
              { slot := Ethereum.uInt256OfByteArray (ffi.KEC word.toByteArray) + Ethereum.UInt256.ofNat (idxNat*wordsPerElem)
                offset := 0 -- am I sure?
                size := elemSize
                bitOffset := .none
              })
            (.some (λ word _ ↦
              { slot := word
                offset := 0
                size := 32
                bitOffset := .none
                type := .int (.uint ⟨256, (by simp), (by simp)⟩)
                hbound := (by simp)
                : StorageLoc
              }))
            node)
    | .bytes | .string => do
      let (elemSize, node) := (1, StorageNode.atomic (.int (.uint ⟨8, (by simp), (by simp)⟩)))
      let elemsPerWord := 32
      pure (32, .indexed
        (λ word idxVal evm ↦
          let packed := checkBytesPacked word evm
          if packed then
            let idxWord := keyValueToWord idxVal
            -- TODO: maybe go directly to nat?
            let idxNat := idxWord.toNat
            if hidx : idxNat < 31 then
              { slot := word
                offset := ⟨31 - idxNat, by omega⟩
                size := elemSize
                bitOffset := .none
              }
            else
              { slot := word
                offset := 0
                size := 33
                bitOffset := .none
              }
          else
            let idxWord := keyValueToWord idxVal
            -- TODO: maybe go directly to nat?
            let idxNat := idxWord.toNat
            { slot := Ethereum.uInt256OfByteArray (ffi.KEC word.toByteArray) + Ethereum.UInt256.ofNat (idxNat/elemsPerWord)
              offset := .ofNat 32 (idxNat%elemsPerWord * elemSize)
              size := elemSize
              bitOffset := .none
            }
        )
        (.some (λ word evm ↦
          if checkBytesPacked word evm then
            { slot := word
              offset := 0
              size := 1
              bitOffset := .some 1
              type := .int (.uint ⟨256, (by simp), (by simp)⟩)
              hbound := (by simp)
              : StorageLoc
            }
          else
            { slot := word
              offset := 0
              size := 32
              bitOffset := .some 1
              type := .int (.uint ⟨256, (by simp), (by simp)⟩)
              hbound := (by simp)
              : StorageLoc
            }))
        node)
    | .tuple sts => do
      -- Solidity does not have tuples in storage, so this assumes same layout as structs
      let (size, indirector) <- solidityTupleLayout structs sts 0 ⟨0⟩ 0
      pure (size, .tuples indirector)
    | .struct _ fields => do
      let (size, indirector) <- solidityStructLayout structs fields ⟨0⟩ 0
      pure (size, .fields indirector)

def solidityStructLayout (structs : List StructDecl)
                                 --(decls : List StorageDecl)
                                 (decls : List (Ident × StorageType))
                                 (slot : EVM.Word) (offset : Fin 32)
                                 : Option (Nat × (Ident -> Option (IntermediateStorageLoc × StorageNode))) :=
  match decls with
  | decl :: decls' => do
    let (size, node) <- slotTypeSolidityStorageNode structs decl.2
    let slot' := if offset + size >= 32 then slot + ⟨1⟩ else slot
    let offset' := if offset + size >= 32 then 0 else offset
    let nextStorageRef := if offset' + size >= 32 then slot' + ⟨1⟩ else slot'
    let nextOffset := if h : offset' + size >= 32 then 0 else ⟨offset' + size, by omega⟩
    let (structSize, rest) <- solidityStructLayout structs decls' nextStorageRef nextOffset
    pure (structSize, λ name ↦ if name == decl.1 then .some ⟨{slot := slot', offset := offset', size, bitOffset := .none}, node⟩ else rest name)
  | [] =>
    let size := if offset == 0 then slot else slot+⟨1⟩
    pure (size.toNat, λ _ ↦ .none)

def solidityTupleLayout (structs : List StructDecl)
                                (elems : List StorageType)
                                (currElem : Nat)
                                (slot : EVM.Word)
                                (offset : Fin 32)
                                : Option (Nat × (Nat -> Option (IntermediateStorageLoc × StorageNode))) :=
  match elems with
  | elem :: elems' => do
    let (size, node) <- slotTypeSolidityStorageNode structs elem
    let slot' := if offset + size >= 32 then slot + ⟨1⟩ else slot
    let offset' := if offset + size >= 32 then 0 else offset
    let nextStorageRef := if offset' + size >= 32 then slot' + ⟨1⟩ else slot'
    let nextOffset := if h : offset' + size >= 32 then 0 else ⟨offset' + size, by omega⟩
    let (structSize, rest) <- solidityTupleLayout structs elems' (currElem + 1) nextStorageRef nextOffset
    pure (structSize, λ n ↦ if n == currElem then .some ⟨{slot := slot', offset := offset', size, bitOffset := .none}, node⟩ else rest n)
  | [] =>
    let size := if offset == 0 then slot else slot+⟨1⟩
    pure (size.toNat, λ _ ↦ .none)

end

def interToLoc (iloc : IntermediateStorageLoc) (t : ElemType) (h : iloc.offset.val + iloc.size - 1 < 32) : StorageLoc :=
  { slot := iloc.slot, offset := iloc.offset,
    size := { val := iloc.size,
              isLt := by
                have : iloc.size < 32 - iloc.offset.val + 1 := by omega
                apply lt_of_lt_of_le this --(b := iloc.size < 32 - iloc.offset.val + 1)
                suffices hnneg : 0 ≤ iloc.offset from by omega
                simp
            }
    bitOffset := iloc.bitOffset
    type := t
    hbound := h }

def followSteps (evm : EVM.State) (loc : IntermediateStorageLoc) (steps : List EvaledStorageRefStep) (node : StorageNode) : Option StorageLoc :=
  match steps with
  | step :: steps' =>
    match node, step with
    | .atomic _, _ => .none
    | .indexed indirector _ node' , .mindex v => do
      let iloc <- indirector loc.slot v evm
      followSteps evm iloc steps' node'
    | .indexed _ (.some length) _ , .length => length loc.slot evm
    | .indexed indirector _ node' , .aindex v => do
      let iloc <- indirector loc.slot v evm
      followSteps evm iloc steps' node'
    | .tuples indirector, .tupleElem n => do
      let (iloc', node') <- indirector n
      let iloc := { slot := iloc'.slot  + loc.slot, offset := iloc'.offset, size := iloc'.size, bitOffset := iloc'.bitOffset }
      followSteps evm iloc steps' node'
    | .fields indirector, .field name => do
      let (iloc', node') <- indirector name
      let iloc := { slot := iloc'.slot  + loc.slot, offset := iloc'.offset, size := iloc'.size, bitOffset := iloc'.bitOffset }
      followSteps evm iloc steps' node'
    | _, _ => none
  | [] =>
    match node with
    | .atomic t => if h : loc.offset.val + loc.size - 1 < 32 then pure (interToLoc loc t h) else .none
    | _ => .none


-- can we avoid either Option?
def genSolidityLayout (structs : List StructDecl) (decls : List StorageDecl) : Option (EvaledStorageRef → EVM.State → Option StorageLoc) :=
  do
  let (_, indirector) <- solidityStructLayout structs (decls.map (λ f ↦ (f.1, f.2))) ⟨0⟩ 0
  pure $ λ evaledStorageRef evm ↦ do
    let (iloc, node') <- indirector evaledStorageRef.base
    followSteps evm iloc evaledStorageRef.steps node'

def genSolidityStorageLayout (structs : List StructDecl) (decls : List StorageDecl) :
    Option StorageLayout := do
  let layout <- genSolidityLayout structs decls
  pure (solidityStorageLayout layout)

-- TODO Maybe move this, or make the file be for general solidity specific components
def genSolidityConstructorDeployment (params : List Param) (pureInit : EVM.Bytes) (values : List Value) : Option EVM.Bytes := do
  let args ← ABI.encodeABIValues? (params.map Param.ty) values
  pureInit ++ args.toByteArray
