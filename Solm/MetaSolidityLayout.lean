import Lean
import Solm.SolidityLayout
import Solm.SolidityStorage

/-!
# Compile-time Solidity storage generation

`solidityLayout!` evaluates a closed storage schema while elaborating and emits one self-contained
locator function. Bare dynamically-sized references locate their length/header anchor, and an
index into a bytes/string locates symbolically as `.byte header index`. The generated function
does not depend on the EVM state: it contains only matching on the evaluated reference and its
slot arithmetic; it does not rebuild `StorageNode`s, traverse the declaration list, or run another
layout-generation function at runtime.
-/

namespace Solm
open ABI
open Lean Elab Term Meta

namespace MetaSolidityLayout

private structure BaseAllocation where
  name : Ident
  ty : StorageType
  slot : Nat
  offset : Nat

private inductive StepPattern where
  | field : Ident -> StepPattern
  | tupleElem : Nat -> StepPattern
  | mindex : Name -> StepPattern
  | aindex : Name -> StepPattern

private structure GeneratedCase where
  steps : List StepPattern
  body : Term

private structure GeneratedLoc where
  slot : Term
  offset : Term

private def supportedKeyType : ElemType -> Bool
  | .bool | .address | .int _ | .bytes _ => true
  | .fixed _ | .function => false

mutual
private def supportedStorageType : StorageType -> Bool
  | .elem (.fixed _) | .elem .function => false
  | .elem _ | .contract _ | .bytes | .string => true
  | .mapping key value => supportedKeyType key && supportedStorageType value
  | .struct _ fields => supportedStorageFields fields
  | .tuple _ => false
  | .array elem _ | .dynamicArray elem => supportedStorageType elem

private def supportedStorageFields : List (Ident × StorageType) -> Bool
  | [] => true
  | field :: rest => supportedStorageType field.2 && supportedStorageFields rest
end

private def typeIsPackable : StorageType -> Bool
  | .elem _ | .contract _ => true
  | _ => false

mutual
private partial def typeSize? (structs : List StructDecl) (ty : StorageType) : Option Nat := do
  match ty with
  | .elem elem => pure (elemTypeSoliditySize elem).val
  | .contract _ => pure 20
  | .mapping _ _ | .dynamicArray _ | .bytes | .string => pure 32
  | .array elem count =>
      let size <- typeSize? structs elem
      if size = 0 then none
      else if size <= 32 then
        let perWord := 32 / size
        pure (((count + perWord - 1) / perWord) * 32)
      else
        pure (count * ((size + 31) / 32) * 32)
  | .struct _ fields => structSize? structs fields 0 0
  | .tuple _ => none

private partial def structSize? (structs : List StructDecl)
    (fields : List (Ident × StorageType)) (slot offset : Nat) : Option Nat := do
  match fields with
  | [] => pure ((slot + if offset = 0 then 0 else 1) * 32)
  | (_, ty) :: rest =>
      let size <- typeSize? structs ty
      let packable := typeIsPackable ty
      let crosses := offset + size > 32
      let startSlot := if packable then (if crosses then slot + 1 else slot)
                       else (if offset = 0 then slot else slot + 1)
      let startOffset := if packable && !crosses then offset else 0
      let endOffset := startOffset + size
      let words := (size + 31) / 32
      let nextSlot := if packable then (if endOffset = 32 then startSlot + 1 else startSlot)
                      else startSlot + words
      let nextOffset := if packable && endOffset < 32 then endOffset else 0
      structSize? structs rest nextSlot nextOffset
end

private def allocateBases (structs : List StructDecl) :
    List StorageDecl -> Nat -> Nat -> Option (List BaseAllocation)
  | [], _, _ => some []
  | decl :: rest, slot, offset => do
      if !supportedStorageType decl.ty then none else pure ()
      let size <- typeSize? structs decl.ty
      let packable := typeIsPackable decl.ty
      let crosses := offset + size > 32
      let startSlot := if packable then (if crosses then slot + 1 else slot)
                       else (if offset = 0 then slot else slot + 1)
      let startOffset := if packable && !crosses then offset else 0
      let endOffset := startOffset + size
      let words := (size + 31) / 32
      let nextSlot := if packable then (if endOffset = 32 then startSlot + 1 else startSlot)
                      else startSlot + words
      let nextOffset := if packable && endOffset < 32 then endOffset else 0
      let tail <- allocateBases structs rest nextSlot nextOffset
      pure ({ name := decl.name, ty := decl.ty, slot := startSlot, offset := startOffset } :: tail)

private unsafe def evalClosedTerm (alpha : Type) (typeStx valueStx : Term) : TermElabM alpha := do
  let type <- elabType typeStx
  let value <- elabTermEnsuringType valueStx type
  evalExpr alpha type value

private def natTerm (n : Nat) : Term := Syntax.mkNumLit (toString n)
private def stringTerm (s : String) : Term := Syntax.mkStrLit s

private def finTerm (bound value : Nat) : TermElabM Term :=
  `(term| Fin.ofNat $(natTerm bound) $(natTerm value))

private def elemTypeTerm : ElemType -> TermElabM Term
  | .bool => `(term| ABI.ElemType.bool)
  | .address => `(term| ABI.ElemType.address)
  | .int (.uint width) =>
      `(term| ABI.ElemType.int (.uint ⟨$(natTerm width.val), by decide⟩))
  | .int (.sint width) =>
      `(term| ABI.ElemType.int (.sint ⟨$(natTerm width.val), by decide⟩))
  | .bytes width =>
      `(term| ABI.ElemType.bytes ⟨$(natTerm width.val), by decide⟩)
  | .fixed _ => throwError "fixed-point storage is not supported by solidityLayout!"
  | .function => throwError "function storage is not supported by solidityLayout!"

private def slotPlusNat (slot : Term) (amount : Nat) : TermElabM Term :=
  if amount = 0 then
    pure slot
  else
    `(term| $slot + (⟨$(natTerm amount)⟩ : Ethereum.UInt256))

private def storageLocBody (loc : GeneratedLoc) (size : Nat) (elem : ElemType) :
    TermElabM Term := do
  let elemStx <- elemTypeTerm elem
  let sizeStx := natTerm size
  `(term|
    some
      (StorageAddr.leaf
        ({ slot := $(loc.slot)
           offset := $(loc.offset)
           size := $sizeStx
           bitOffset := none
           type := $elemStx
           hbound := by simp only [Fin.val_ofNat] <;> omega } : StorageLoc)))

private def anchorBody (slot : Term) : TermElabM Term :=
  `(term| some (StorageAddr.anchor $slot))

private def wrapLet (name : Name) (value : Term) (body : Term) : TermElabM Term := do
  let ident := mkIdent name
  `(term| let $ident:ident := $value; $body)

private def wrapCasesLet (cases : List GeneratedCase) (name : Name) (value : Term) :
    TermElabM (List GeneratedCase) :=
  cases.mapM fun generated => do
    let body <- wrapLet name value generated.body
    pure { generated with body := body }

private def declarationsOfFields (fields : List (Ident × StorageType)) : List StorageDecl :=
  fields.map fun field => { name := field.1, ty := field.2 }

private partial def generateCases (structs : List StructDecl)
    (ty : StorageType) (loc : GeneratedLoc) (path : List StepPattern) :
    TermElabM (List GeneratedCase) := do
  match ty with
  | .elem elem =>
      let size := (elemTypeSoliditySize elem).val
      let body <- storageLocBody loc size elem
      pure [{ steps := path, body := body }]
  | .contract _ =>
      let body <- storageLocBody loc 20 .address
      pure [{ steps := path, body := body }]
  | .mapping key value =>
      unless supportedKeyType key do
        throwError "unsupported Solidity mapping key type"
      let indexName <- mkFreshUserName `key
      let slotName <- mkFreshUserName `mappedSlot
      let index := mkIdent indexName
      let mappedSlot := mkIdent slotName
      let slotValue <- `(term|
        Ethereum.uInt256OfByteArray
          (Ethereum.KEC ((keyValueToWord $index).toByteArray ++ ($(loc.slot)).toByteArray)))
      let zero <- finTerm 32 0
      let cases <- generateCases structs value
        { slot := mappedSlot, offset := zero } (path ++ [.mindex indexName])
      wrapCasesLet cases slotName slotValue
  | .array elem _ =>
      let elemSize <-
        match typeSize? structs elem with
        | some size => pure size
        | none => throwError "unsupported Solidity fixed-array element type"
      if elemSize = 0 then
        throwError "zero-sized Solidity fixed-array element"
      let indexName <- mkFreshUserName `index
      let indexNatName <- mkFreshUserName `indexNat
      let elementSlotName <- mkFreshUserName `elementSlot
      let index := mkIdent indexName
      let indexNat := mkIdent indexNatName
      let elementSlot := mkIdent elementSlotName
      let indexNatValue <- `(term| (keyValueToWord $index).toNat)
      let (slotValue, offset) <-
        if elemSize <= 32 then
          let elemsPerWord := 32 / elemSize
          if elemsPerWord = 0 then
            throwError "invalid packed Solidity fixed-array element size"
          let slotValue <- `(term|
            $(loc.slot) + Ethereum.UInt256.ofNat
              ($indexNat / $(natTerm elemsPerWord)))
          let offset <- `(term|
            Fin.ofNat 32 (($indexNat % $(natTerm elemsPerWord)) * $(natTerm elemSize)))
          pure (slotValue, offset)
        else
          let wordsPerElem := (elemSize + 31) / 32
          let slotValue <- `(term|
            $(loc.slot) + Ethereum.UInt256.ofNat
              ($indexNat * $(natTerm wordsPerElem)))
          let offset <- finTerm 32 0
          pure (slotValue, offset)
      let cases <- generateCases structs elem
        { slot := elementSlot, offset := offset } (path ++ [.aindex indexName])
      let cases <- wrapCasesLet cases elementSlotName slotValue
      wrapCasesLet cases indexNatName indexNatValue
  | .dynamicArray elem =>
      let lengthBody <- anchorBody loc.slot
      let anchorCase : GeneratedCase := { steps := path, body := lengthBody }
      let elemSize <-
        match typeSize? structs elem with
        | some size => pure size
        | none => throwError "unsupported Solidity dynamic-array element type"
      if elemSize = 0 then
        throwError "zero-sized Solidity dynamic-array element"
      let indexName <- mkFreshUserName `index
      let indexNatName <- mkFreshUserName `indexNat
      let dataBaseName <- mkFreshUserName `dataBase
      let elementSlotName <- mkFreshUserName `elementSlot
      let index := mkIdent indexName
      let indexNat := mkIdent indexNatName
      let dataBase := mkIdent dataBaseName
      let elementSlot := mkIdent elementSlotName
      let indexNatValue <- `(term| (keyValueToWord $index).toNat)
      let dataBaseValue <- `(term|
        Ethereum.uInt256OfByteArray (Ethereum.KEC ($(loc.slot)).toByteArray))
      let (slotValue, offset) <-
        if elemSize <= 32 then
          let elemsPerWord := 32 / elemSize
          if elemsPerWord = 0 then
            throwError "invalid packed Solidity dynamic-array element size"
          let slotValue <- `(term|
            $dataBase + Ethereum.UInt256.ofNat
              ($indexNat / $(natTerm elemsPerWord)))
          let offset <- `(term|
            Fin.ofNat 32 (($indexNat % $(natTerm elemsPerWord)) * $(natTerm elemSize)))
          pure (slotValue, offset)
        else
          let wordsPerElem := (elemSize + 31) / 32
          let slotValue <- `(term|
            $dataBase + Ethereum.UInt256.ofNat
              ($indexNat * $(natTerm wordsPerElem)))
          let offset <- finTerm 32 0
          pure (slotValue, offset)
      let elementCases <- generateCases structs elem
        { slot := elementSlot, offset := offset } (path ++ [.aindex indexName])
      let elementCases <- wrapCasesLet elementCases elementSlotName slotValue
      let elementCases <- wrapCasesLet elementCases dataBaseName dataBaseValue
      let elementCases <- wrapCasesLet elementCases indexNatName indexNatValue
      pure (anchorCase :: elementCases)
  | .bytes | .string =>
      let anchorCase : GeneratedCase := { steps := path, body := (← anchorBody loc.slot) }
      let indexName <- mkFreshUserName `index
      let index := mkIdent indexName
      let indexedBody <- `(term|
        some (StorageAddr.byte $(loc.slot) (keyValueToWord $index).toNat))
      pure
        [ anchorCase,
          { steps := path ++ [.aindex indexName], body := indexedBody } ]
  | .struct _ fields =>
      let some allocations := allocateBases structs (declarationsOfFields fields) 0 0
        | throwError "unsupported Solidity struct field"
      let mut cases := []
      for allocation in allocations do
        let fieldSlot <- slotPlusNat loc.slot allocation.slot
        let fieldOffset <- finTerm 32 allocation.offset
        let generated <- generateCases structs allocation.ty
          { slot := fieldSlot, offset := fieldOffset }
          (path ++ [.field allocation.name])
        cases := cases ++ generated
      pure cases
  | .tuple _ =>
      throwError "tuple storage is not supported by Solidity"

private def stepPatternTerm : StepPattern -> TermElabM Term
  | .field name => `(term| .field $(stringTerm name))
  | .tupleElem index => `(term| .tupleElem $(natTerm index))
  | .mindex name => `(term| .mindex $(mkIdent name))
  | .aindex name => `(term| .aindex $(mkIdent name))

private def stepsPatternTerm : List StepPattern -> TermElabM Term
  | [] => `(term| [])
  | step :: rest => do
      let head <- stepPatternTerm step
      let tail <- stepsPatternTerm rest
      `(term| $head :: $tail)

private def generatedRawLayout (structs : List StructDecl)
    (allocations : List BaseAllocation) : TermElabM Term := do
  let refName <- mkFreshUserName `ref
  let ref := mkIdent refName
  let mut alts : Array (TSyntax ``Lean.Parser.Term.matchAlt) := #[]
  for allocation in allocations do
    let slot <- `(term| (⟨$(natTerm allocation.slot)⟩ : Ethereum.UInt256))
    let offset <- finTerm 32 allocation.offset
    let generated <- generateCases structs allocation.ty { slot := slot, offset := offset } []
    for generatedCase in generated do
      let name := stringTerm allocation.name
      let steps <- stepsPatternTerm generatedCase.steps
      let body := generatedCase.body
      alts := alts.push (← `(Lean.Parser.Term.matchAltExpr| | $name, $steps => $body))
  alts := alts.push (← `(Lean.Parser.Term.matchAltExpr| | _, _ => none))
  let body <- `(term| match ($ref).base, ($ref).steps with $alts:matchAlt*)
  `(term|
    ((fun $ref:ident => $body) :
      StorageLayout))

private def elaborateLayout (structsStx declsStx : Term) : TermElabM Term := do
  let structs <- unsafe evalClosedTerm (List StructDecl) (← `(term| List StructDecl)) structsStx
  let decls <- unsafe evalClosedTerm (List StorageDecl) (← `(term| List StorageDecl)) declsStx
  let names := decls.map (·.name)
  unless names.eraseDups.length = names.length do
    throwError "duplicate Solidity storage declaration name"
  let some allocations := allocateBases structs decls 0 0
    | throwError "unsupported Solidity persistent-storage type or invalid layout"
  generatedRawLayout structs allocations

elab "solidityLayout! " "[" structs:term "]" "[" decls:term "]" : term => do
  let stx <- elaborateLayout structs decls
  elabTerm stx none

macro "solidityStorage! " "[" structs:term "]" "[" decls:term "]" : term =>
  `(solidityStorageBackend (solidityLayout! [$structs] [$decls]))

end MetaSolidityLayout
end Solm
