import Benchmarks.Morpho.MetaMorphoV1_1.MaxMintAllocationSyntax

/-! Cursor propagation through cap enablement and its balance readers. -/

open Solm ABI

namespace Benchmarks.Morpho.MetaMorphoV1_1.SourceMemory

def allocatedSetCapFunction : FunctionDecl :=
  let source := Syntax.contractSyntax.functions[14]!
  { source with
    name := "__solcSetCap"
    params := source.params ++ [{ name := cursorName, ty := cursorType }]
    returnType := [cursorType]
    body := allocationBody (fun name ↦
      if name == "MorphoBalancesLib_expectedSupplyAssets" then
        some allocatedSupplyAssetsFunction.name
      else none) (fun _ ↦ 0) source.body ++ [.return [.var cursorName]] }

def allocatedAcceptCapTransition : TransitionDecl :=
  let source := Syntax.contractSyntax.transitions[30]!
  { source with
    body := source.body.take 9 ++
      [.internalCall allocatedSetCapFunction.name
        [.var "marketParams", .var "id",
         .cast (.storage ⟨"pendingCap", [.mindex (.var "id"), .field "value"]⟩)
           (.elem (.int (.uint ⟨184, by decide⟩))),
         .intLit 288] "__c2"] }

end Benchmarks.Morpho.MetaMorphoV1_1.SourceMemory
