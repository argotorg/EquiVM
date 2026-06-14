import Lean
import Lean.Parser.Term
import EVM.Types
import ABI.Types
import Act.Value
import Act.Storage

namespace Act
open ABI
open Lean Elab Term Meta

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
    | .indexed indirector node' , .index v => do
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

/-!
The definitions above mirror `Act.SolidityLayout`: they compute the whole storage
schema as ordinary Lean data.  That is useful for execution, but it leaves proofs
with a layout function whose head reduction has to unfold the recursive generator.

The term elaborators below run that generation while elaborating the user's term
and emit the already-expanded layout function.  The resulting kernel term only
contains direct matching on the base name and path steps, plus the dynamic
arithmetic needed for arrays and mappings.
-/

namespace MetaSolidityLayout

private inductive GeneratedIndex where
  | staticPacked (elemSize elemsPerWord : Nat)
  | staticUnpacked (elemSize wordsPerElem : Nat)
  | mapping (size : Nat)
  | dynamicPacked (elemSize elemsPerWord : Nat)
  | dynamicUnpacked (elemSize wordsPerElem : Nat)

private inductive GeneratedNode where
  | atomic : ElemType → GeneratedNode
  | indexed : GeneratedIndex → GeneratedNode → GeneratedNode
  | fields : List (Ident × IntermediateStorageLoc × GeneratedNode) → GeneratedNode
  | tuples : List (Nat × IntermediateStorageLoc × GeneratedNode) → GeneratedNode

mutual

private def generatedStructLayout
    (structs : List StructDecl)
    (decls : List (Ident × StorageType))
    (slot : EVM.Word)
    (offset : Fin 32) :
    Option (Nat × List (Ident × IntermediateStorageLoc × GeneratedNode)) :=
  match decls with
  | decl :: decls' => do
    let (size, node) ← generatedSlotTypeStorageNode structs decl.2
    let slot' := if offset + size >= 32 then slot + ⟨1⟩ else slot
    let offset' := if offset + size >= 32 then 0 else offset
    let nextStorageRef := if offset' + size >= 32 then slot' + ⟨1⟩ else slot'
    let nextOffset := if h : offset' + size >= 32 then 0 else ⟨offset' + size, by omega⟩
    let (structSize, rest) ← generatedStructLayout structs decls' nextStorageRef nextOffset
    pure (structSize, (decl.1, { slot := slot', offset := offset', size }, node) :: rest)
  | [] =>
    let size := if offset == 0 then slot else slot + ⟨1⟩
    pure (size.toNat, [])

private def generatedTupleLayout
    (structs : List StructDecl)
    (elems : List StorageType)
    (currElem : Nat)
    (slot : EVM.Word)
    (offset : Fin 32) :
    Option (Nat × List (Nat × IntermediateStorageLoc × GeneratedNode)) :=
  match elems with
  | elem :: elems' => do
    let (size, node) ← generatedSlotTypeStorageNode structs elem
    let slot' := if offset + size >= 32 then slot + ⟨1⟩ else slot
    let offset' := if offset + size >= 32 then 0 else offset
    let nextStorageRef := if offset' + size >= 32 then slot' + ⟨1⟩ else slot'
    let nextOffset := if h : offset' + size >= 32 then 0 else ⟨offset' + size, by omega⟩
    let (tupleSize, rest) ← generatedTupleLayout structs elems' (currElem + 1) nextStorageRef nextOffset
    pure (tupleSize, (currElem, { slot := slot', offset := offset', size }, node) :: rest)
  | [] =>
    let size := if offset == 0 then slot else slot + ⟨1⟩
    pure (size.toNat, [])

private def generatedSlotTypeStorageNode
    (structs : List StructDecl)
    (st : StorageType) :
    Option (Nat × GeneratedNode) :=
  match st with
  | .elem t => pure (elemTypeSoliditySize t, .atomic t)
  | .contract _ => pure (elemTypeSoliditySize .address, .atomic .address)
  | .array t n => do
    let (elemSize, node) ← generatedSlotTypeStorageNode structs t
    if elemSize <= 32 then
      let elemsPerWord := 32 / elemSize
      let arrayWords := (n + elemsPerWord - 1) / elemsPerWord
      pure (arrayWords * 32, .indexed (.staticPacked elemSize elemsPerWord) node)
    else
      let wordsPerElem := (elemSize + 32 - 1) / 32
      pure (n * wordsPerElem * 32, .indexed (.staticUnpacked elemSize wordsPerElem) node)
  | .mapping _ t => do
    let (size, node) ← generatedSlotTypeStorageNode structs t
    pure (32, .indexed (.mapping size) node)
  | .dynamicArray t => do
    let (elemSize, node) ← generatedSlotTypeStorageNode structs t
    if elemSize <= 32 then
      let elemsPerWord := 32 / elemSize
      pure (32, .indexed (.dynamicPacked elemSize elemsPerWord) node)
    else
      let wordsPerElem := (elemSize + 32 - 1) / 32
      pure (32, .indexed (.dynamicUnpacked elemSize wordsPerElem) node)
  | .tuple sts => do
    let (size, fields) ← generatedTupleLayout structs sts 0 ⟨0⟩ 0
    pure (size, .tuples fields)
  | .struct _ fields => do
    let (size, fields) ← generatedStructLayout structs fields ⟨0⟩ 0
    pure (size, .fields fields)

end

private def natTerm (n : Nat) : Term :=
  Syntax.mkNumLit (toString n)

private def stringTerm (s : String) : Term :=
  Syntax.mkStrLit s

private def fin32Term (n : Nat) : TermElabM Term :=
  `(term| (⟨$(natTerm n), by decide⟩ : Fin 32))

private def wordTerm (w : EVM.Word) : TermElabM Term :=
  `(term| (Ethereum.UInt256.ofNat $(natTerm w.toNat)))

private def intermediateLocTerm (loc : IntermediateStorageLoc) : TermElabM Term := do
  let slot ← wordTerm loc.slot
  let offset ← fin32Term loc.offset.val
  `(term| ({ slot := $slot, offset := $offset, size := $(natTerm loc.size) } : IntermediateStorageLoc))

private structure LocExpr where
  term : Term
  slot : Term
  const? : Option IntermediateStorageLoc
  offset? : Option Nat
  size? : Option Nat

private def constLocExpr (loc : IntermediateStorageLoc) : TermElabM LocExpr := do
  let term ← intermediateLocTerm loc
  let slot ← wordTerm loc.slot
  pure { term, slot, const? := some loc, offset? := some loc.offset.val, size? := some loc.size }

private def dynamicLocExpr (loc : Term) : TermElabM LocExpr := do
  pure { term := loc, slot := (← `(term| ($loc).slot)), const? := none, offset? := none, size? := none }

private def slotOnlyLocExpr (slot : Term) (offset size : Nat) : LocExpr :=
  { term := slot, slot, const? := none, offset? := some offset, size? := some size }

private def storageLocOfKnownTerm (slot : Term) (offset size : Nat) (t : Term) : TermElabM Term := do
  let offsetStx ← fin32Term offset
  if offset + size - 1 < 32 then
    `(term|
      some
        ({ slot := $slot
           offset := $offsetStx
           size := (⟨$(natTerm size), by decide⟩ : Fin 33)
           hbound := by decide
           type := $t } : StorageLoc))
  else
    `(term| none)

private def storageLocOfConstTerm (loc : IntermediateStorageLoc) (t : Term) : TermElabM Term := do
  let slot ← wordTerm loc.slot
  storageLocOfKnownTerm slot loc.offset.val loc.size t

private def bitWidthTerm (w : BitWidth) : TermElabM Term :=
  `(term| (⟨$(natTerm w.val), by decide⟩ : ABI.BitWidth))

private def finPosTerm (n : Nat) (bound : Nat) : TermElabM Term :=
  `(term| (⟨$(natTerm n), by decide⟩ : ABI.FinPos $(natTerm bound)))

private def intTypeTerm : IntType → TermElabM Term
  | .uint w => do
      let w ← bitWidthTerm w
      `(term| ABI.IntType.uint $w)
  | .sint w => do
      let w ← bitWidthTerm w
      `(term| ABI.IntType.sint $w)

private def fixedTypeTerm : FixedType → TermElabM Term
  | .ufixed w n => do
      let w ← bitWidthTerm w
      let n ← finPosTerm n.val 80
      `(term| ABI.FixedType.ufixed $w $n)
  | .fixed w n => do
      let w ← bitWidthTerm w
      let n ← finPosTerm n.val 81
      `(term| ABI.FixedType.fixed $w $n)

private def elemTypeTerm : ElemType → TermElabM Term
  | .bool => `(term| ABI.ElemType.bool)
  | .address => `(term| ABI.ElemType.address)
  | .int t => do
      let t ← intTypeTerm t
      `(term| ABI.ElemType.int $t)
  | .fixed t => do
      let t ← fixedTypeTerm t
      `(term| ABI.ElemType.fixed $t)
  | .bytes n =>
      `(term| ABI.ElemType.bytes (⟨$(natTerm n.val), by decide⟩ : Fin 32))
  | .function => `(term| ABI.ElemType.function)

private def indexedLocTerm (index : GeneratedIndex) (baseSlot idxVal : Term) : TermElabM Term :=
  match index with
  | .staticPacked elemSize elemsPerWord =>
      `(term|
        (let idxWord := keyValueToWord $idxVal
         let idxNat := idxWord.toNat
         ({ slot := $baseSlot + Ethereum.UInt256.ofNat (idxNat / $(natTerm elemsPerWord))
            offset := Fin.ofNat 32 (idxNat % $(natTerm elemsPerWord) * $(natTerm elemSize))
            size := $(natTerm elemSize) } : IntermediateStorageLoc)))
  | .staticUnpacked elemSize wordsPerElem =>
      `(term|
        (let idxWord := keyValueToWord $idxVal
         let idxNat := idxWord.toNat
         ({ slot := $baseSlot + Ethereum.UInt256.ofNat (idxNat * $(natTerm wordsPerElem))
            offset := (0 : Fin 32)
            size := $(natTerm elemSize) } : IntermediateStorageLoc)))
  | .mapping size =>
      `(term|
        ({ slot := Ethereum.uInt256OfByteArray
            (ffi.KEC ((keyValueToWord $idxVal).toByteArray ++ ($baseSlot).toByteArray))
           offset := (0 : Fin 32)
           size := $(natTerm size) } : IntermediateStorageLoc))
  | .dynamicPacked elemSize elemsPerWord =>
      `(term|
        (let idxWord := keyValueToWord $idxVal
         let idxNat := idxWord.toNat
         ({ slot := Ethereum.uInt256OfByteArray (ffi.KEC ($baseSlot).toByteArray) +
              Ethereum.UInt256.ofNat (idxNat / $(natTerm elemsPerWord))
            offset := Fin.ofNat 32 (idxNat % $(natTerm elemsPerWord) * $(natTerm elemSize))
            size := $(natTerm elemSize) } : IntermediateStorageLoc)))
  | .dynamicUnpacked elemSize wordsPerElem =>
      `(term|
        (let idxWord := keyValueToWord $idxVal
         let idxNat := idxWord.toNat
         ({ slot := Ethereum.uInt256OfByteArray (ffi.KEC ($baseSlot).toByteArray) +
              Ethereum.UInt256.ofNat (idxNat * $(natTerm wordsPerElem))
            offset := (0 : Fin 32)
            size := $(natTerm elemSize) } : IntermediateStorageLoc)))

private def indexedSlotTerm (index : GeneratedIndex) (baseSlot idxVal : Term) : TermElabM Term :=
  match index with
  | .staticPacked _ elemsPerWord =>
      `(term|
        (let idxWord := keyValueToWord $idxVal
         let idxNat := idxWord.toNat
         $baseSlot + Ethereum.UInt256.ofNat (idxNat / $(natTerm elemsPerWord))))
  | .staticUnpacked _ wordsPerElem =>
      `(term|
        (let idxWord := keyValueToWord $idxVal
         let idxNat := idxWord.toNat
         $baseSlot + Ethereum.UInt256.ofNat (idxNat * $(natTerm wordsPerElem))))
  | .mapping _ =>
      `(term|
        Ethereum.uInt256OfByteArray
          (ffi.KEC ((keyValueToWord $idxVal).toByteArray ++ ($baseSlot).toByteArray)))
  | .dynamicPacked _ elemsPerWord =>
      `(term|
        (let idxWord := keyValueToWord $idxVal
         let idxNat := idxWord.toNat
         Ethereum.uInt256OfByteArray (ffi.KEC ($baseSlot).toByteArray) +
           Ethereum.UInt256.ofNat (idxNat / $(natTerm elemsPerWord))))
  | .dynamicUnpacked _ wordsPerElem =>
      `(term|
        (let idxWord := keyValueToWord $idxVal
         let idxNat := idxWord.toNat
         Ethereum.uInt256OfByteArray (ffi.KEC ($baseSlot).toByteArray) +
           Ethereum.UInt256.ofNat (idxNat * $(natTerm wordsPerElem))))
private def indexedLocOffsetSize? : GeneratedIndex → Option (Nat × Nat)
  | .staticPacked elemSize elemsPerWord =>
      if elemsPerWord == 1 then some (0, elemSize) else none
  | .staticUnpacked elemSize _ => some (0, elemSize)
  | .mapping size => some (0, size)
  | .dynamicPacked elemSize elemsPerWord =>
      if elemsPerWord == 1 then some (0, elemSize) else none
  | .dynamicUnpacked elemSize _ => some (0, elemSize)

private def indexedLocSize : GeneratedIndex → Nat
  | .staticPacked elemSize _ => elemSize
  | .staticUnpacked elemSize _ => elemSize
  | .mapping size => size
  | .dynamicPacked elemSize _ => elemSize
  | .dynamicUnpacked elemSize _ => elemSize

mutual

private partial def fieldCasesTerm
    (name steps : Term)
    (loc : LocExpr)
    (fields : List (Ident × IntermediateStorageLoc × GeneratedNode)) :
    TermElabM Term := do
  let mut alts : Array (TSyntax ``Parser.Term.matchAlt) := #[]
  for (fieldName, fieldLoc, node) in fields do
      match loc.const? with
      | some parentLoc =>
          let absLoc : IntermediateStorageLoc :=
            { slot := fieldLoc.slot + parentLoc.slot, offset := fieldLoc.offset, size := fieldLoc.size }
          let body ← followTerm (← constLocExpr absLoc) steps node
          alts := alts.push (← `(Parser.Term.matchAltExpr|
            | $(stringTerm fieldName) => $body))
      | none =>
          let fieldLocTerm ← intermediateLocTerm fieldLoc
          let iloc' := mkIdent (← mkFreshUserName `iloc')
          let iloc := mkIdent (← mkFreshUserName `iloc)
          let body ← followTerm (← dynamicLocExpr iloc) steps node
          alts := alts.push (← `(Parser.Term.matchAltExpr|
            | $(stringTerm fieldName) =>
              let $iloc':ident : IntermediateStorageLoc := $fieldLocTerm
              let $iloc:ident : IntermediateStorageLoc :=
                { slot := ($iloc').slot + $(loc.slot), offset := ($iloc').offset, size := ($iloc').size }
              $body))
  alts := alts.push (← `(Parser.Term.matchAltExpr| | _ => none))
  `(term| match ($name) with $alts:matchAlt*)

private partial def tupleCasesTerm
    (idx steps : Term)
    (loc : LocExpr)
    (fields : List (Nat × IntermediateStorageLoc × GeneratedNode)) :
    TermElabM Term :=
  match fields with
  | [] => `(term| none)
  | (fieldIdx, fieldLoc, node) :: rest => do
      match loc.const? with
      | some parentLoc =>
          let absLoc : IntermediateStorageLoc :=
            { slot := fieldLoc.slot + parentLoc.slot, offset := fieldLoc.offset, size := fieldLoc.size }
          let body ← followTerm (← constLocExpr absLoc) steps node
          let rest ← tupleCasesTerm idx steps loc rest
          `(term|
            if $idx == $(natTerm fieldIdx) then
              $body
            else
              $rest)
      | none =>
          let fieldLocTerm ← intermediateLocTerm fieldLoc
          let iloc' := mkIdent (← mkFreshUserName `iloc')
          let iloc := mkIdent (← mkFreshUserName `iloc)
          let body ← followTerm (← dynamicLocExpr iloc) steps node
          let rest ← tupleCasesTerm idx steps loc rest
          `(term|
            if $idx == $(natTerm fieldIdx) then
              let $iloc':ident : IntermediateStorageLoc := $fieldLocTerm
              let $iloc:ident : IntermediateStorageLoc :=
                { slot := ($iloc').slot + $(loc.slot), offset := ($iloc').offset, size := ($iloc').size }
              $body
            else
              $rest)

private partial def followTerm (loc : LocExpr) (steps : Term) (node : GeneratedNode) : TermElabM Term :=
  match node with
  | .atomic t => do
      let t ← elemTypeTerm t
      let someBody ←
        match loc.const? with
        | some constLoc => storageLocOfConstTerm constLoc t
        | none =>
          match loc.offset?, loc.size? with
          | some offset, some size => storageLocOfKnownTerm loc.slot offset size t
          | none, some 1 =>
            `(term|
              some
                ({ slot := $(loc.slot)
                   offset := ($(loc.term)).offset
                   size := (⟨1, by decide⟩ : Fin 33)
                   hbound := by
                    simp
                   type := $t } : StorageLoc))
          | _, _ =>
            `(term|
              if h : ($(loc.term)).offset.val + ($(loc.term)).size - 1 < 32 then
                some
                  ({ slot := ($(loc.term)).slot
                     offset := ($(loc.term)).offset
                     size :=
                      { val := ($(loc.term)).size
                        isLt := by
                          have : ($(loc.term)).size < 32 - ($(loc.term)).offset.val + 1 := by omega
                          apply lt_of_lt_of_le this
                          suffices hnneg : 0 ≤ ($(loc.term)).offset from by omega
                          simp }
                     type := $t
                     hbound := h } : StorageLoc)
              else
                none)
      `(term|
        match ($steps) with
        | [] => $someBody
        | _ => none)
  | .indexed index node => do
      let v := mkIdent (← mkFreshUserName `v)
      let steps' := mkIdent (← mkFreshUserName `steps')
      let baseSlot := loc.slot
      match indexedLocOffsetSize? index with
      | some (offset, size) => do
          let slot := mkIdent (← mkFreshUserName `slot)
          let slotTerm ← indexedSlotTerm index baseSlot v
          let dynamicLoc := slotOnlyLocExpr slot offset size
          let body ← followTerm dynamicLoc steps' node
          `(term|
            match ($steps) with
            | EvaledStorageRefStep.index $v:ident :: $steps':ident =>
                let $slot:ident : EVM.Word := $slotTerm
                $body
            | _ => none)
      | none => do
          let iloc := mkIdent (← mkFreshUserName `iloc)
          let locTerm ← indexedLocTerm index baseSlot v
          let dynamicLoc := { (← dynamicLocExpr iloc) with size? := some (indexedLocSize index) }
          let body ← followTerm dynamicLoc steps' node
          `(term|
            match ($steps) with
            | EvaledStorageRefStep.index $v:ident :: $steps':ident =>
                let $iloc:ident : IntermediateStorageLoc := $locTerm
                $body
            | _ => none)
  | .fields fields => do
      let name := mkIdent (← mkFreshUserName `name)
      let steps' := mkIdent (← mkFreshUserName `steps')
      let body ← fieldCasesTerm name steps' loc fields
      `(term|
        match ($steps) with
        | EvaledStorageRefStep.field $name:ident :: $steps':ident => $body
        | _ => none)
  | .tuples fields => do
      let idx := mkIdent (← mkFreshUserName `idx)
      let steps' := mkIdent (← mkFreshUserName `steps')
      let body ← tupleCasesTerm idx steps' loc fields
      `(term|
        match ($steps) with
        | EvaledStorageRefStep.tupleElem $idx:ident :: $steps':ident => $body
        | _ => none)

end

private partial def baseCasesTerm
    (evaledStorageRef : Term)
    (fields : List (Ident × IntermediateStorageLoc × GeneratedNode)) :
    TermElabM Term := do
  let mut alts : Array (TSyntax ``Parser.Term.matchAlt) := #[]
  for (baseName, loc, node) in fields do
      let body ← followTerm (← constLocExpr loc) (← `(term| ($evaledStorageRef).steps)) node
      alts := alts.push (← `(Parser.Term.matchAltExpr| | $(stringTerm baseName) => $body))
  alts := alts.push (← `(Parser.Term.matchAltExpr| | _ => none))
  `(term| match (($evaledStorageRef).base) with $alts:matchAlt*)

private def generatedLayoutFunctionExpr
    (structs : List StructDecl)
    (decls : List StorageDecl) :
    TermElabM Lean.Expr := do
  let some (_, fields) := generatedStructLayout structs (decls.map fun decl => (decl.name, decl.ty)) ⟨0⟩ 0
    | throwError "could not generate Solidity storage layout"
  let refType ← elabType (← `(term| EvaledStorageRef))
  let bodyType ← elabType (← `(term| Option StorageLoc))
  let refName ← mkFreshUserName `evaledStorageRef
  withLocalDeclD refName refType fun ref => do
    let bodyStx ← baseCasesTerm (mkIdent refName) fields
    let body ← elabTermEnsuringType bodyStx bodyType
    liftMetaM <| mkLambdaFVars #[ref] body

private unsafe def evalClosedTerm (α : Type) (typeStx valueStx : Term) : TermElabM α := do
  let type ← elabType typeStx
  let value ← elabTermEnsuringType valueStx type
  evalExpr α type value

elab "solidityLayoutFn! " "[" structs:term "]" "[" decls:term "]" : term => do
  let structs ← unsafe evalClosedTerm (List StructDecl) (← `(term| List StructDecl)) structs
  let decls ← unsafe evalClosedTerm (List StorageDecl) (← `(term| List StorageDecl)) decls
  generatedLayoutFunctionExpr structs decls

elab "genSolidityLayout! " "[" structs:term "]" "[" decls:term "]" : term => do
  let structs ← unsafe evalClosedTerm (List StructDecl) (← `(term| List StructDecl)) structs
  let decls ← unsafe evalClosedTerm (List StorageDecl) (← `(term| List StorageDecl)) decls
  let layout ← generatedLayoutFunctionExpr structs decls
  mkAppM ``Option.some #[layout]

end MetaSolidityLayout
