import Benchmarks.Morpho.MetaMorphoV1_1.SetCapAllocationSyntax

/-! Cursor propagation through cap submission's last-update reader and cap setter. -/

open Solm ABI

namespace Benchmarks.Morpho.MetaMorphoV1_1.SourceMemory

/-- The packed hash buffer and singleton slot array reserve 160 bytes before the call. -/
def allocatedLastUpdateFunction : FunctionDecl :=
  { name := "__solcMorphoLastUpdate"
    params :=
      [{ name := "morpho", ty := .elem .address },
       { name := "id", ty := .elem (.bytes ⟨31, by decide⟩) },
       { name := cursorName, ty := cursorType }]
    returnType := [cursorType, cursorType]
    body :=
      [reserveBytes 160,
       .internalCall "MorphoStorageLib_marketLastUpdateAndFeeSlot" [.var "id"] "__c0",
       .internalCall "MorphoLib__array" [.var "__c0"] "slot",
       .internalCall extSloadsFunction.name [.var "morpho", .var "slot", .var cursorName]
         slotsAndCursorName,
       .return
         [.cast (.cast (.index (.tupleGet (.var slotsAndCursorName) 0) (.intLit 0))
            (.elem (.int (.uint ⟨256, by decide⟩)))) (.elem (.int (.uint ⟨128, by decide⟩))),
          .tupleGet (.var slotsAndCursorName) 1]] }

def allocatedSubmitCapTransition : TransitionDecl :=
  let source := Syntax.contractSyntax.transitions[18]!
  let branch := match source.body[14]! with
    | .ite condition yes no =>
        .ite condition (yes.take 1 ++
          [.internalCall allocatedSetCapFunction.name
            [.var "marketParams", .var "id", .var "__c5", .var cursorName] "__c6"]) no
    | stmt => stmt
  { source with
    body := source.body.take 4 ++ [.letDecl cursorName none (.intLit 288)] ++
      allocationBody (fun name ↦
        if name == "MorphoLib_lastUpdate" then some allocatedLastUpdateFunction.name else none)
        (fun _ ↦ 0) ((source.body.drop 4).take 10) ++ [branch] }

end Benchmarks.Morpho.MetaMorphoV1_1.SourceMemory
