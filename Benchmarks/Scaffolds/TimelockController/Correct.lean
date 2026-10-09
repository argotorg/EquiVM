import Benchmarks.Scaffolds.TimelockController.Constructor
import Solm.Refine

/-!
# OpenZeppelin TimelockController benchmark correctness stub

Runtime equivalence of the 28-selector binary-search dispatcher against its spec.  Proofs are the
benchmark target.
-/

open Solm ABI Ethereum Ethereum.EVM

namespace OpenZeppelinBench.TimelockController

theorem timelockControllerBenchCorrect :
    runtimeRefinement config timelockControllerBenchBytecode contract := by
  sorry

theorem timelockControllerBenchContractCorrect :
    contractRefinement config timelockControllerBenchCreationBytecode contract :=
  contractRefinement.of_constant timelockControllerBenchConstructorCorrect timelockControllerBenchCorrect

end OpenZeppelinBench.TimelockController
