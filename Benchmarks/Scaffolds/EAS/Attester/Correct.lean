import Benchmarks.Scaffolds.EAS.Attester.Constructor
import Solm.Refine

/-!
# EAS Attester benchmark correctness stub

For every well-typed assignment of `_eas`, the runtime deployed for it (the template patched with
it) refines the spec run with those immutables.  With the constructor target this gives the
contract refinement.  Proofs are the benchmark target.
-/

open Solm ABI Ethereum Ethereum.EVM Benchmarks.EAS.Attester.Immutables

namespace Benchmarks.EAS.Attester

theorem attesterCorrect (imms : Store) (_hfit : immutablesFit contract imms) :
    runtimeRefinement config (deployedRuntime attesterBytecode imms) contract
      (restrictImmutables contract imms) := by
  sorry

theorem attesterContractCorrect : contractRefinement config attesterCreationBytecode contract :=
  .of_runtime attesterConstructorCorrect attesterCorrect

end Benchmarks.EAS.Attester
