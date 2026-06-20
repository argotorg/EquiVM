import EVM.Types
import ABI.Types
import Solm.Value
import Solm.Storage

namespace Solm
open ABI

/-
 -
 - Solidity Layout Generation,  WIP
 -
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
