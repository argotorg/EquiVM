import EVM.Types
import ABI.Types
import ABI.Encode
import Solm.Value
import Storage.Basic

/-!
# solc storage representation of `bytes` and `string`

Short (≤ 31 bytes, inline) and long (length slot + keccak data slots) forms, the read/write/clear
hooks built on them, and `solidityStorageLayout`, which wires them into a `StorageLayout`.
-/

namespace Storage
open ABI Solm

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

end Storage
