import Benchmarks.Morpho.MetaMorphoV1_1.MaxMintAllocationSyntax

/-! Cursor propagation through the withdrawal-limit calculation. -/

open Solm ABI

namespace Benchmarks.Morpho.MetaMorphoV1_1.SourceMemory

def allocatedWithdrawableFunction : FunctionDecl :=
  let source := Syntax.contractSyntax.functions[83]!
  { source with
    name := "__solcWithdrawable"
    params := source.params ++ [{ name := cursorName, ty := cursorType }]
    returnType := [returnValueType source.returnType, cursorType]
    body := allocationBody (fun _ ↦ none)
      (fun name ↦ if name == "balanceOf" then 32 else 0) source.body }

def allocatedSimulateWithdrawFunction : FunctionDecl :=
  let source := Syntax.contractSyntax.functions[59]!
  { source with
    name := "__solcSimulateWithdraw"
    params := source.params ++ [{ name := cursorName, ty := cursorType }]
    returnType := [returnValueType source.returnType, cursorType]
    body := allocationBody (fun name ↦
      if name == "_marketParams" then some allocatedMarketParamsFunction.name
      else if name == "MorphoLib_supplyShares" then some allocatedSupplySharesFunction.name
      else if name == "MorphoBalancesLib_expectedMarketBalances" then
        some allocatedMarketBalancesFunction.name
      else if name == "_withdrawable" then some allocatedWithdrawableFunction.name
      else none) (fun _ ↦ 0) source.body }

def allocatedMaxWithdrawFunction : FunctionDecl :=
  let source := Syntax.contractSyntax.functions[23]!
  { source with
    name := "__solcMaxWithdraw"
    params := source.params ++ [{ name := cursorName, ty := cursorType }]
    returnType := [returnValueType source.returnType, cursorType]
    body := allocationBody (fun name ↦
      if name == "_accruedFeeAndAssets" then some allocatedAccruedFeeAssetsFunction.name
      else if name == "_simulateWithdrawMorpho" then some allocatedSimulateWithdrawFunction.name
      else none) (fun _ ↦ 0) source.body }

def allocatedMaxWithdrawTransition : TransitionDecl :=
  let source := Syntax.contractSyntax.transitions[63]!
  { source with
    body := source.body.take 4 ++ [.letDecl cursorName none (.intLit 128)] ++
      cursorCall allocatedMaxWithdrawFunction.name [.var "owner"] "__c0" ++ source.body.drop 5 }

def allocatedMaxRedeemTransition : TransitionDecl :=
  let source := Syntax.contractSyntax.transitions[66]!
  { source with
    body := source.body.take 3 ++ [.letDecl cursorName none (.intLit 128)] ++
      cursorCall allocatedMaxWithdrawFunction.name [.var "owner"] "__c0" ++ source.body.drop 4 }

end Benchmarks.Morpho.MetaMorphoV1_1.SourceMemory
