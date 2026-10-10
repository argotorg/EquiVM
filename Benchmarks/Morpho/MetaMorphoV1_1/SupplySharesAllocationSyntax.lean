import Benchmarks.Morpho.MetaMorphoV1_1.ExtSloadsAllocationSyntax

/-! The supply-share reader with an explicit compiler-memory cursor. -/

open Solm ABI

namespace Benchmarks.Morpho.MetaMorphoV1_1.SourceMemory

def slotsAndCursorName : Ident := "__solcSlotsAndCursor"

/-- The two hash buffers and singleton argument array reserve 256 bytes before the call. -/
def allocatedSupplySharesFunction : FunctionDecl :=
  { name := "__solcMorphoSupplyShares"
    params :=
      [{ name := "morpho", ty := .elem .address },
       { name := "id", ty := .elem (.bytes ⟨31, by decide⟩) },
       { name := "user", ty := .elem .address },
       { name := cursorName, ty := .elem (.int (.uint ⟨256, by decide⟩)) }]
    returnType := List.replicate 2 (.elem (.int (.uint ⟨256, by decide⟩)))
    body :=
      [.internalCall allocateFunction.name [.var cursorName, .intLit 256] cursorName,
       .internalCall "MorphoStorageLib_positionSupplySharesSlot" [.var "id", .var "user"]
         "__c0",
       .internalCall "MorphoLib__array" [.var "__c0"] "slot",
       .internalCall extSloadsFunction.name [.var "morpho", .var "slot", .var cursorName]
         slotsAndCursorName,
       .return
         [.cast (.index (.tupleGet (.var slotsAndCursorName) 0) (.intLit 0))
            (.elem (.int (.uint ⟨256, by decide⟩))),
          .tupleGet (.var slotsAndCursorName) 1]] }

end Benchmarks.Morpho.MetaMorphoV1_1.SourceMemory
