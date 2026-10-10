import Benchmarks.Morpho.MetaMorphoV1_1.AssetViewsAllocationSyntax

/-! Cursor-aware upward conversion views. -/

open Solm ABI

namespace Benchmarks.Morpho.MetaMorphoV1_1.SourceMemory

def allocatedPreviewMintTransition : TransitionDecl :=
  { Syntax.contractSyntax.transitions[53]! with
    body := (Syntax.contractSyntax.transitions[53]!).body.take 3 ++
      [.internalCall allocatedConvertToAssetsFunction.name
        [.var "shares", .intLit 1, .intLit 128] "__c0",
        .return [.tupleGet (.var "__c0") 0]] }

def allocatedPreviewWithdrawTransition : TransitionDecl :=
  { Syntax.contractSyntax.transitions[4]! with
    body := (Syntax.contractSyntax.transitions[4]!).body.take 3 ++
      [.internalCall allocatedConvertToSharesFunction.name
        [.var "assets", .intLit 1, .intLit 128] "__c0",
        .return [.tupleGet (.var "__c0") 0]] }

end Benchmarks.Morpho.MetaMorphoV1_1.SourceMemory
