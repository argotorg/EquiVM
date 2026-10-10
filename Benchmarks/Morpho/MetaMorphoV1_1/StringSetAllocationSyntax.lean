import Benchmarks.Morpho.MetaMorphoV1_1.SpecSyntax
import Benchmarks.Morpho.MetaMorphoV1_1.AllocationSyntax

/-! Metadata setters reserve the ABI-decoded length word and padded string before owner checks. -/

open Solm ABI

namespace Benchmarks.Morpho.MetaMorphoV1_1.SourceMemory

def stringSetAllocationSizeExpr (param : Ident) : Expr :=
  .binary .add (.arrayLength .localVar ⟨param, []⟩) (.intLit 32)

def allocatedStringSetTransition (index : Nat) (param : Ident) : TransitionDecl :=
  let source := Syntax.contractSyntax.transitions[index]!
  { source with
    body := source.body.take 3 ++
      [.internalCall allocateFunction.name
        [.intLit 128, stringSetAllocationSizeExpr param] "__solcStringCursor"] ++
      source.body.drop 3 }

def allocatedSetNameTransition : TransitionDecl := allocatedStringSetTransition 58 "newName"

def allocatedSetSymbolTransition : TransitionDecl := allocatedStringSetTransition 55 "newSymbol"

end Benchmarks.Morpho.MetaMorphoV1_1.SourceMemory
