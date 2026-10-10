import Benchmarks.Morpho.MetaMorphoV1_1.ShareViewsAllocationSyntax

/-! Cursor propagation for public asset-conversion views. -/

open Solm ABI

namespace Benchmarks.Morpho.MetaMorphoV1_1.SourceMemory

def allocatedConvertToAssetsFunction : FunctionDecl :=
  let source := Syntax.contractSyntax.functions[41]!
  { source with
    name := "__solcConvertToAssets"
    params := source.params ++ [{ name := cursorName, ty := cursorType }]
    returnType := [returnValueType source.returnType, cursorType]
    body := allocationBody (fun name ↦
      if name == "_accruedFeeAndAssets" then some allocatedAccruedFeeAssetsFunction.name
      else none) (fun _ ↦ 0) source.body }

def allocatedAssetViewBody : List Stmt :=
  (Syntax.contractSyntax.transitions[2]!).body.take 3 ++
    [.internalCall allocatedConvertToAssetsFunction.name
      [.var "shares", .intLit 0, .intLit 128] "__c0",
      .return [.tupleGet (.var "__c0") 0]]

def allocatedConvertToAssetsTransition : TransitionDecl :=
  { Syntax.contractSyntax.transitions[2]! with body := allocatedAssetViewBody }

def allocatedPreviewRedeemTransition : TransitionDecl :=
  { Syntax.contractSyntax.transitions[24]! with body := allocatedAssetViewBody }

end Benchmarks.Morpho.MetaMorphoV1_1.SourceMemory
