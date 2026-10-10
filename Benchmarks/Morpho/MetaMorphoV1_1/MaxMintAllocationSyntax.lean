import Benchmarks.Morpho.MetaMorphoV1_1.MaxDepositAllocationSyntax

/-! Cursor propagation through the additional readers used by maxMint. -/

open Solm ABI

namespace Benchmarks.Morpho.MetaMorphoV1_1.SourceMemory

def allocatedSupplyAssetsFunction : FunctionDecl :=
  let source := Syntax.contractSyntax.functions[51]!
  { source with
    name := "__solcExpectedSupplyAssets"
    params := source.params ++ [{ name := cursorName, ty := cursorType }]
    returnType := [returnValueType source.returnType, cursorType]
    body := allocationBody (fun name ↦
      if name == "MorphoLib_supplyShares" then some allocatedSupplySharesFunction.name
      else if name == "MorphoBalancesLib_expectedMarketBalances" then
        some allocatedMarketBalancesFunction.name
      else none) (fun _ ↦ 0) source.body }

def allocatedAccruedFeeAssetsFunction : FunctionDecl :=
  let source := Syntax.contractSyntax.functions[29]!
  { source with
    name := "__solcAccruedFeeAndAssets"
    params := source.params ++ [{ name := cursorName, ty := cursorType }]
    returnType := [returnValueType source.returnType, cursorType]
    body := allocationBody (fun name ↦
      if name == "_marketParams" then some allocatedMarketParamsFunction.name
      else if name == "MorphoBalancesLib_expectedSupplyAssets" then
        some allocatedSupplyAssetsFunction.name
      else none) (fun _ ↦ 0) source.body }

def allocatedConvertToSharesFunction : FunctionDecl :=
  let source := Syntax.contractSyntax.functions[22]!
  { source with
    name := "__solcConvertToShares"
    params := source.params ++ [{ name := cursorName, ty := cursorType }]
    returnType := [returnValueType source.returnType, cursorType]
    body := allocationBody (fun name ↦
      if name == "_accruedFeeAndAssets" then some allocatedAccruedFeeAssetsFunction.name
      else none) (fun _ ↦ 0) source.body }

def allocatedMaxMintTransition : TransitionDecl :=
  { Syntax.contractSyntax.transitions[59]! with
    body := (Syntax.contractSyntax.transitions[59]!).body.take 3 ++
      [.letDecl cursorName none (.intLit 128)] ++
      cursorCall allocatedMaxDepositFunction.name [] "suppliable" ++
      cursorCall allocatedConvertToSharesFunction.name [.var "suppliable", .intLit 0] "__c1" ++
      [.return [.var "__c1"]] }

end Benchmarks.Morpho.MetaMorphoV1_1.SourceMemory
