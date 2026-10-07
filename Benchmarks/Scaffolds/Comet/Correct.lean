import Benchmarks.Scaffolds.Comet.Constructor
import Solm.Refine

/-!
# Compound III CometWithExtendedAssetList benchmark correctness stub

For every well-typed assignment of Comet's 25 immutables, the runtime deployed for it (the template patched with
it) refines the spec run with those immutables.  With the constructor target this gives the
contract refinement.  Proofs are the benchmark target.
-/

open Solm ABI Ethereum Ethereum.EVM Benchmarks.CompoundIII.Comet.Immutables

namespace Benchmarks.CompoundIII.Comet

theorem cometCorrect (imms : Store) (_hfit : immutablesFit contract imms) :
    runtimeRefinement config (deployedRuntime cometBytecode imms) contract
      (restrictImmutables contract imms) := by
  sorry

theorem cometContractCorrect : contractRefinement config cometCreationBytecode contract :=
  .of_runtime cometConstructorCorrect cometCorrect

end Benchmarks.CompoundIII.Comet
