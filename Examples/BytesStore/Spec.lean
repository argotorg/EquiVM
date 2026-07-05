import Solm.Semantics
import Solm.SolidityLayout

/-!
# BytesStore — focused bytes storage example

This mirrors `StringStoreLite`, but exercises Solidity's dynamic `bytes` type directly:

* whole-value `bytes` assignment and clearing;
* assigning one byte through `bytes[index]`;
* `bytes` nested inside a dynamic array, struct, and mapping.

Solidity indexes dynamic `bytes` as `bytes1`; the Solm storage model represents the same one-byte
leaf as `uint8`, so the `set*Byte` transitions use `uint8` parameters and returns.
-/

open Solm ABI Ethereum

namespace BytesStore

/-! ## Types -/

def uint8Int : IntType := .uint ⟨8, by decide⟩
def uint256Int : IntType := .uint ⟨256, by decide⟩

def uint8 : ABIType := .elem (.int uint8Int)
def uint256 : ABIType := .elem (.int uint256Int)
def bytesTy : ABIType := .bytes

def uint8St : StorageType := .elem (.int uint8Int)
def uint256St : StorageType := .elem (.int uint256Int)
def bytesSt : StorageType := .bytes

/-! ## Storage refs -/

def currentRef : StorageRef := { base := "current" }
def chunksRef : StorageRef := { base := "chunks" }
def packetRef : StorageRef := { base := "packet" }
def mappedBaseRef : StorageRef := { base := "mapped" }

def currentByteRef (i : Expr) : StorageRef :=
  { base := "current", steps := [.aindex i] }

def chunkRef (chunkIndex : Expr) : StorageRef :=
  { base := "chunks", steps := [.aindex chunkIndex] }

def chunkByteRef (chunkIndex byteIndex : Expr) : StorageRef :=
  { base := "chunks", steps := [.aindex chunkIndex, .aindex byteIndex] }

def packetDataRef : StorageRef :=
  { base := "packet", steps := [.field "data"] }

def packetDataByteRef (byteIndex : Expr) : StorageRef :=
  { base := "packet", steps := [.field "data", .aindex byteIndex] }

def packetTagRef : StorageRef :=
  { base := "packet", steps := [.field "tag"] }

def mappedRef (key : Expr) : StorageRef :=
  { base := "mapped", steps := [.mindex key] }

def mappedByteRef (key byteIndex : Expr) : StorageRef :=
  { base := "mapped", steps := [.mindex key, .aindex byteIndex] }

/-! ## Storage declarations + struct schema -/

def packetStructTy : StorageType :=
  .struct "Packet" [("data", bytesSt), ("tag", uint256St)]

def packetStructDecl : StructDecl :=
  { name := "Packet"
    fields := [{ name := "data", ty := bytesSt }, { name := "tag", ty := uint256St }] }

def storageDecls : List StorageDecl :=
  [ { name := "current", ty := bytesSt },
    { name := "chunks", ty := .dynamicArray bytesSt },
    { name := "packet", ty := packetStructTy },
    { name := "mapped", ty := .mapping (.int uint256Int) bytesSt } ]

/-! ## Transitions -/

def setTransition : TransitionDecl :=
  { name := "set"
    params := [{ name := "value", ty := bytesTy }]
    returnType := some uint256
    body :=
      [ .require (.binary .eq (.env .callvalue) (.intLit 0)),
        .letDecl "copy" (some bytesTy) (.var "value"),
        .assign .storage currentRef (.var "copy"),
        .return (.arrayLength .localVar { base := "copy" }) ] }

def setByteTransition : TransitionDecl :=
  { name := "setByte"
    params := [{ name := "index", ty := uint256 }, { name := "value", ty := uint8 }]
    returnType := some uint8
    body :=
      [ .require (.binary .eq (.env .callvalue) (.intLit 0)),
        .assign .storage (currentByteRef (.var "index")) (.var "value"),
        .return (.storage (currentByteRef (.var "index"))) ] }

def clearCurrentTransition : TransitionDecl :=
  { name := "clearCurrent"
    params := []
    returnType := some uint256
    body :=
      [ .require (.binary .eq (.env .callvalue) (.intLit 0)),
        .letDecl "copy" (some bytesTy) (.storage currentRef),
        .delete currentRef,
        .return (.arrayLength .localVar { base := "copy" }) ] }

def currentLengthGetter : TransitionDecl :=
  { name := "currentLength"
    params := []
    returnType := some uint256
    body :=
      [ .require (.binary .eq (.env .callvalue) (.intLit 0)),
        .return (.arrayLength .storage currentRef) ] }

def pushChunkTransition : TransitionDecl :=
  { name := "pushChunk"
    params := [{ name := "value", ty := bytesTy }]
    returnType := some uint256
    body :=
      [ .require (.binary .eq (.env .callvalue) (.intLit 0)),
        .push chunksRef (some (.var "value")),
        .return (.arrayLength .storage chunksRef) ] }

def setChunkTransition : TransitionDecl :=
  { name := "setChunk"
    params := [{ name := "chunkIndex", ty := uint256 }, { name := "value", ty := bytesTy }]
    returnType := some uint256
    body :=
      [ .require (.binary .eq (.env .callvalue) (.intLit 0)),
        .assign .storage (chunkRef (.var "chunkIndex")) (.var "value"),
        .return (.arrayLength .storage (chunkRef (.var "chunkIndex"))) ] }

def setChunkByteTransition : TransitionDecl :=
  { name := "setChunkByte"
    params :=
      [ { name := "chunkIndex", ty := uint256 },
        { name := "byteIndex", ty := uint256 },
        { name := "value", ty := uint8 } ]
    returnType := some uint8
    body :=
      [ .require (.binary .eq (.env .callvalue) (.intLit 0)),
        .assign .storage (chunkByteRef (.var "chunkIndex") (.var "byteIndex")) (.var "value"),
        .return (.storage (chunkByteRef (.var "chunkIndex") (.var "byteIndex"))) ] }

def chunkLengthGetter : TransitionDecl :=
  { name := "chunkLength"
    params := [{ name := "chunkIndex", ty := uint256 }]
    returnType := some uint256
    body :=
      [ .require (.binary .eq (.env .callvalue) (.intLit 0)),
        .return (.arrayLength .storage (chunkRef (.var "chunkIndex"))) ] }

def setPacketTransition : TransitionDecl :=
  { name := "setPacket"
    params := [{ name := "value", ty := bytesTy }, { name := "tag", ty := uint256 }]
    returnType := some uint256
    body :=
      [ .require (.binary .eq (.env .callvalue) (.intLit 0)),
        .assign .storage packetDataRef (.var "value"),
        .assign .storage packetTagRef (.var "tag"),
        .return (.arrayLength .storage packetDataRef) ] }

def setPacketByteTransition : TransitionDecl :=
  { name := "setPacketByte"
    params := [{ name := "byteIndex", ty := uint256 }, { name := "value", ty := uint8 }]
    returnType := some uint8
    body :=
      [ .require (.binary .eq (.env .callvalue) (.intLit 0)),
        .assign .storage (packetDataByteRef (.var "byteIndex")) (.var "value"),
        .return (.storage (packetDataByteRef (.var "byteIndex"))) ] }

def packetLengthGetter : TransitionDecl :=
  { name := "packetLength"
    params := []
    returnType := some uint256
    body :=
      [ .require (.binary .eq (.env .callvalue) (.intLit 0)),
        .return (.arrayLength .storage packetDataRef) ] }

def packetTagGetter : TransitionDecl :=
  { name := "packetTag"
    params := []
    returnType := some uint256
    body :=
      [ .require (.binary .eq (.env .callvalue) (.intLit 0)),
        .return (.storage packetTagRef) ] }

def setMappedTransition : TransitionDecl :=
  { name := "setMapped"
    params := [{ name := "key", ty := uint256 }, { name := "value", ty := bytesTy }]
    returnType := some uint256
    body :=
      [ .require (.binary .eq (.env .callvalue) (.intLit 0)),
        .assign .storage (mappedRef (.var "key")) (.var "value"),
        .return (.arrayLength .storage (mappedRef (.var "key"))) ] }

def setMappedByteTransition : TransitionDecl :=
  { name := "setMappedByte"
    params :=
      [ { name := "key", ty := uint256 },
        { name := "byteIndex", ty := uint256 },
        { name := "value", ty := uint8 } ]
    returnType := some uint8
    body :=
      [ .require (.binary .eq (.env .callvalue) (.intLit 0)),
        .assign .storage (mappedByteRef (.var "key") (.var "byteIndex")) (.var "value"),
        .return (.storage (mappedByteRef (.var "key") (.var "byteIndex"))) ] }

def mappedLengthGetter : TransitionDecl :=
  { name := "mappedLength"
    params := [{ name := "key", ty := uint256 }]
    returnType := some uint256
    body :=
      [ .require (.binary .eq (.env .callvalue) (.intLit 0)),
        .return (.arrayLength .storage (mappedRef (.var "key"))) ] }

def bytesStoreContract : ContractDecl :=
  { name := "BytesStore"
    storage := storageDecls
    ctor :=
      { params := []
        body := [.require (.binary .eq (.env .callvalue) (.intLit 0))] }
    structs := [packetStructDecl]
    transitions :=
      [ setTransition, setByteTransition, clearCurrentTransition, currentLengthGetter,
        pushChunkTransition, setChunkTransition, setChunkByteTransition, chunkLengthGetter,
        setPacketTransition, setPacketByteTransition, packetLengthGetter, packetTagGetter,
        setMappedTransition, setMappedByteTransition, mappedLengthGetter ] }

/-! ## Solidity storage layout -/

def uint8Loc (slot : Ethereum.UInt256) (offset : Fin 32) : StorageLoc :=
  { slot := slot, offset := offset, size := 1, hbound := by omega, type := .int uint8Int }

def uint256Loc (slot : Ethereum.UInt256) : StorageLoc :=
  { slot := slot, offset := 0, size := 32, hbound := by decide, type := .int uint256Int }

def bytesLikeDataBase (baseSlot : Ethereum.UInt256) : Ethereum.UInt256 :=
  Ethereum.uInt256OfByteArray (ffi.KEC baseSlot.toByteArray)

abbrev bytesLikeLengthLoc := Solm.bytesLikeLengthLoc

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

def nonnegativeIndexSlot? (baseSlot : Ethereum.UInt256) (index : KeyValue) :
    Option Ethereum.UInt256 :=
  match index with
  | .int i =>
      if i < 0 then none
      else some (baseSlot + Ethereum.UInt256.ofNat i.toNat)
  | _ => none

def chunksDataBase : Ethereum.UInt256 :=
  bytesLikeDataBase ⟨1⟩

def chunksElemSlot? (index : KeyValue) : Option Ethereum.UInt256 :=
  nonnegativeIndexSlot? chunksDataBase index

def mappedValueSlot (key : KeyValue) : Ethereum.UInt256 :=
  Ethereum.uInt256OfByteArray
    (ffi.KEC ((keyValueToWord key).toByteArray ++ (⟨4⟩ : Ethereum.UInt256).toByteArray))

def bytesStoreLayout : EvaledStorageRef -> EVM.State -> Option StorageLoc
  | { base := "current", steps := [.length] }, evm => some (bytesLikeLengthLoc ⟨0⟩ evm)
  | { base := "current", steps := [.aindex i] }, evm => bytesLikeByteLoc? ⟨0⟩ i evm
  | { base := "chunks", steps := [.length] }, _ => some (uint256Loc ⟨1⟩)
  | { base := "chunks", steps := [.aindex i, .length] }, evm => do
      let slot <- chunksElemSlot? i
      some (bytesLikeLengthLoc slot evm)
  | { base := "chunks", steps := [.aindex i, .aindex j] }, evm => do
      let slot <- chunksElemSlot? i
      bytesLikeByteLoc? slot j evm
  | { base := "packet", steps := [.field "data", .length] }, evm =>
      some (bytesLikeLengthLoc ⟨2⟩ evm)
  | { base := "packet", steps := [.field "data", .aindex i] }, evm =>
      bytesLikeByteLoc? ⟨2⟩ i evm
  | { base := "packet", steps := [.field "tag"] }, _ => some (uint256Loc ⟨3⟩)
  | { base := "mapped", steps := [.mindex key, .length] }, evm =>
      some (bytesLikeLengthLoc (mappedValueSlot key) evm)
  | { base := "mapped", steps := [.mindex key, .aindex i] }, evm =>
      bytesLikeByteLoc? (mappedValueSlot key) i evm
  | _, _ => none

def bytesStoreStorageLayout : StorageLayout :=
  solidityStorageLayout bytesStoreLayout

end BytesStore

def bytesStoreConfig : Config :=
  { storage := BytesStore.bytesStoreStorageLayout
    externalABI := defaultExternalCallABI
    selfDeployment :=
      genSolidityConstructorDeployment BytesStore.bytesStoreContract.ctor.params }
