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


-- Difference is that size can be larger than a slot, so we can deal with broad intermediate locs
structure IntermediateStorageLoc where
  slot    : EVM.Word      -- storage slot in which item is stored
  offset  : Fin 32        -- offset within that slot in bytes
  size    : Nat           -- size (may ccross into other slots)

-- Schema of a particular instance of a solidity layout
inductive StorageNode where
  | atomic : ElemType -> StorageNode
  | indexed : (EVM.Word -> KeyValue -> IntermediateStorageLoc)
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
        pure (size, .indexed (λ word idxVal ↦ 
                                let idxWord := keyValueToWord idxVal
                                -- TODO: maybe go directly to nat?
                                let idxNat := idxWord.toNat
                                { slot := word + Ethereum.UInt256.ofNat (idxNat/elemsPerWord)
                                  offset := .ofNat 32 (idxNat%elemsPerWord * elemSize)
                                  size := elemSize
                                }
                             ) node)
      else
        let wordsPerElem := (elemSize + 32 - 1) / 32
        let arrayWords := n * wordsPerElem
        let size := arrayWords*32
        pure (size, .indexed (λ word idxVal ↦ 
                                let idxWord := keyValueToWord idxVal
                                -- TODO: maybe go directly to nat?
                                let idxNat := idxWord.toNat
                                { slot := word + Ethereum.UInt256.ofNat (idxNat*wordsPerElem)
                                  offset := 0 -- am I sure?
                                  size := elemSize
                                }
                             ) node)
    | .mapping _ t => do
      let (size, node) <- slotTypeSolidityStorageNode structs t
      pure (32, .indexed (λ word idxVal ↦
        { slot := Ethereum.uInt256OfByteArray (ffi.KEC ((keyValueToWord idxVal).toByteArray ++ word.toByteArray))
          offset := 0
          size := size
        }) node)
    | .dynamicArray t => do
      let (elemSize, node) <- slotTypeSolidityStorageNode structs t
      if elemSize <= 32 then
        let elemsPerWord := 32 / elemSize
        pure (32, .indexed (λ word idxVal ↦ 
                                let idxWord := keyValueToWord idxVal
                                -- TODO: maybe go directly to nat?
                                let idxNat := idxWord.toNat
                                { slot := Ethereum.uInt256OfByteArray (ffi.KEC word.toByteArray) + Ethereum.UInt256.ofNat (idxNat/elemsPerWord)
                                  offset := .ofNat 32 (idxNat%elemsPerWord * elemSize)
                                  size := elemSize
                                }
                             ) node)
      else
        let wordsPerElem := (elemSize + 32 - 1) / 32
        pure (32, .indexed (λ word idxVal ↦ 
                                let idxWord := keyValueToWord idxVal
                                -- TODO: maybe go directly to nat?
                                let idxNat := idxWord.toNat
                                { slot := Ethereum.uInt256OfByteArray (ffi.KEC word.toByteArray) + Ethereum.UInt256.ofNat (idxNat*wordsPerElem)
                                  offset := 0 -- am I sure?
                                  size := elemSize
                                }
                             ) node)
    | .tuple sts => do
      -- Solidity does not have tuples in storage, so this assumes same layout as structs
      let (size, indirector) <- solidityTupleLayout structs sts 0 ⟨0⟩ 0
      pure (size, .tuples indirector)
    | .struct _ fields => do
      -- let struct <- structs.find? (λ s ↦ s.name == name)
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
    pure (structSize, λ name ↦ if name == decl.1 then .some ⟨{slot := slot', offset := offset', size}, node⟩ else rest name)
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
    pure (structSize, λ n ↦ if n == currElem then .some ⟨{slot := slot', offset := offset', size}, node⟩ else rest n)
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
    type := t
    hbound := h }

def followSteps (loc : IntermediateStorageLoc) (steps : List EvaledStorageRefStep) (node : StorageNode) : Option StorageLoc :=
  match steps with
  | step :: steps' =>
    match node, step with
    | .atomic _, _ => .none
    | .indexed indirector node' , .mindex v => do
      let iloc <- indirector loc.slot v
      followSteps iloc steps' node'
    | .indexed indirector node' , .aindex v => do
      let iloc <- indirector loc.slot v
      followSteps iloc steps' node'
    | .tuples indirector, .tupleElem n => do
      let (iloc', node') <- indirector n
      let iloc := { slot := iloc'.slot  + loc.slot, offset := iloc'.offset, size := iloc'.size }
      followSteps iloc steps' node'
    | .fields indirector, .field name => do
      let (iloc', node') <- indirector name
      let iloc := { slot := iloc'.slot  + loc.slot, offset := iloc'.offset, size := iloc'.size }
      followSteps iloc steps' node'
    | _, _ => none
  | [] => 
    match node with
    | .atomic t => if h : loc.offset.val + loc.size - 1 < 32 then pure (interToLoc loc t h) else .none
    | _ => .none


-- can we avoid either Option?
def genSolidityLayout (structs : List StructDecl) (decls : List StorageDecl) : Option (EvaledStorageRef → Option StorageLoc) :=
  do
  let (_, indirector) <- solidityStructLayout structs (decls.map (λ f ↦ (f.1, f.2))) ⟨0⟩ 0
  pure $ λ evaledStorageRef ↦ do
    let (iloc, node') <- indirector evaledStorageRef.base
    followSteps iloc evaledStorageRef.steps node'
