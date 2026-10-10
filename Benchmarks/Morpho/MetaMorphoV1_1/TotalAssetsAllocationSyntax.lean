import Benchmarks.Morpho.MetaMorphoV1_1.MaxMintAllocationSyntax

/-! The totalAssets boundary supplies the compiler's initial allocation cursor. -/

open Solm ABI

namespace Benchmarks.Morpho.MetaMorphoV1_1.SourceMemory

def allocatedTotalAssetsTransition : TransitionDecl :=
  { Syntax.contractSyntax.transitions[0]! with
    body := (Syntax.contractSyntax.transitions[0]!).body.take 3 ++
      [.internalCall allocatedAccruedFeeAssetsFunction.name [.intLit 128] "__c0",
        .letDecl "newTotalAssets" (some (.elem (.int (.uint ⟨256, by decide⟩))))
          (.tupleGet (.tupleGet (.var "__c0") 0) 1),
        .return [.var "newTotalAssets"]] }

end Benchmarks.Morpho.MetaMorphoV1_1.SourceMemory
