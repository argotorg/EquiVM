import Benchmarks.Morpho.MetaMorphoV1_1.MaxMintAllocationSyntax

/-! Cursor-aware public share-conversion views, whose bodies are identical. -/

open Solm ABI

namespace Benchmarks.Morpho.MetaMorphoV1_1.SourceMemory

def allocatedShareViewBody : List Stmt :=
  (Syntax.contractSyntax.transitions[60]!).body.take 3 ++
    [.internalCall allocatedConvertToSharesFunction.name
      [.var "assets", .intLit 0, .intLit 128] "__c0",
      .return [.tupleGet (.var "__c0") 0]]

def allocatedConvertToSharesTransition : TransitionDecl :=
  { Syntax.contractSyntax.transitions[60]! with body := allocatedShareViewBody }

def allocatedPreviewDepositTransition : TransitionDecl :=
  { Syntax.contractSyntax.transitions[73]! with body := allocatedShareViewBody }

end Benchmarks.Morpho.MetaMorphoV1_1.SourceMemory
