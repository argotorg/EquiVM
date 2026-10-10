import Benchmarks.Morpho.MetaMorphoV1_1.AllocationSyntax

/-! The `extSloads` call with its compiled return-buffer and array reservations explicit. -/

open Solm ABI

namespace Benchmarks.Morpho.MetaMorphoV1_1.SourceMemory

def callOkName : Ident := "__solcCallSucceeded"

def returnDataName : Ident := "__solcReturnData"

def decodedName : Ident := "__solcDecodedReturn"

def returnSizeExpr : Expr := .arrayLength .localVar ⟨returnDataName, []⟩

def arraySizeExpr : Expr :=
  .binary .add (.intLit 32)
    (.binary .mul (.intLit 32) (.arrayLength .localVar ⟨decodedName, []⟩))

def reserveReturnBuffer : Stmt :=
  .internalCall allocateFunction.name [.var cursorName, .var sizeName] cursorName

/-- A typed view call whose memory use is exposed through an explicit cursor result. -/
def extSloadsFunction : FunctionDecl :=
  { name := "__solcExtSloads"
    params :=
      [{ name := "morpho", ty := .elem .address },
       { name := "slot", ty := .dynamicArray (.elem (.bytes ⟨31, by decide⟩)) },
       { name := cursorName, ty := .elem (.int (.uint ⟨256, by decide⟩)) }]
    returnType :=
      [.dynamicArray (.elem (.bytes ⟨31, by decide⟩)), .elem (.int (.uint ⟨256, by decide⟩))]
    body :=
      [.lowLevelCall (.var "morpho") (.intLit 0)
        (.abiEncodeCall "extSloads" [.var "slot"]) callOkName returnDataName false,
       .require (.var callOkName),
       .letDecl sizeName none returnSizeExpr,
       reserveReturnBuffer,
       .letDecl decodedName none
         (.abiDecode (.dynamicArray (.elem (.bytes ⟨31, by decide⟩))) (.var returnDataName)),
       .internalCall allocateFunction.name [.var cursorName, arraySizeExpr] cursorName,
       .return [.var decodedName, .var cursorName]] }

end Benchmarks.Morpho.MetaMorphoV1_1.SourceMemory
