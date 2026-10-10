import Benchmarks.Morpho.MetaMorphoV1_1.SpecSyntax
import Benchmarks.Morpho.MetaMorphoV1_1.AllocationSyntax

/-! Storage-string getters reserve the copied length word and padded payload. -/

open Solm ABI

namespace Benchmarks.Morpho.MetaMorphoV1_1.SourceMemory

def stringValueName : Ident := "__solcStringValue"

def stringAllocationSizeExpr : Expr :=
  .binary .add (.arrayLength .localVar ⟨stringValueName, []⟩) (.intLit 32)

def allocatedStringViewTransition (index : Nat) (field : Ident) : TransitionDecl :=
  let source := Syntax.contractSyntax.transitions[index]!
  { source with
    body := source.body.take 3 ++
      [.letDecl stringValueName none (.storage ⟨field, []⟩),
       .internalCall allocateFunction.name [.intLit 128, stringAllocationSizeExpr] "__c0",
       .return [.var stringValueName]] }

def allocatedNameTransition : TransitionDecl := allocatedStringViewTransition 1 "_vaultName"

def allocatedSymbolTransition : TransitionDecl := allocatedStringViewTransition 44 "_vaultSymbol"

end Benchmarks.Morpho.MetaMorphoV1_1.SourceMemory
