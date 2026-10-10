import Benchmarks.Morpho.MetaMorphoV1_1.MaxMintAllocationSyntax

/-! Cursor propagation through interest accrual and the fee-recipient setter. -/

open Solm ABI

namespace Benchmarks.Morpho.MetaMorphoV1_1.SourceMemory

def allocatedAccrueInterestFunction : FunctionDecl :=
  let source := Syntax.contractSyntax.functions[3]!
  { source with
    name := "__solcAccrueInterest"
    params := [{ name := cursorName, ty := cursorType }]
    returnType := [cursorType]
    body := cursorCall allocatedAccruedFeeAssetsFunction.name [] "__c0" ++
      source.body.drop 1 ++ [.return [.var cursorName]] }

def allocatedSetFeeRecipientTransition : TransitionDecl :=
  let source := Syntax.contractSyntax.transitions[71]!
  { source with
    body := source.body.take 6 ++
      [.internalCall allocatedAccrueInterestFunction.name [.intLit 128] "__c1"] ++
      source.body.drop 7 }

def allocatedSetFeeTransition : TransitionDecl :=
  let source := Syntax.contractSyntax.transitions[28]!
  { source with
    body := source.body.take 7 ++
      [.internalCall allocatedAccrueInterestFunction.name [.intLit 128] "__c1"] ++
      source.body.drop 8 }

end Benchmarks.Morpho.MetaMorphoV1_1.SourceMemory
