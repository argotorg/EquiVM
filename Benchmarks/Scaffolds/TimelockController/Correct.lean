import Benchmarks.Scaffolds.TimelockController.Constructor
import Solm.Equiv

/-!
# OpenZeppelin TimelockController benchmark correctness stub

Runtime equivalence of the 28-selector binary-search dispatcher against its spec.  Proofs are the
benchmark target.
-/

open Solm ABI Ethereum Ethereum.EVM

namespace OpenZeppelinBench.TimelockController

theorem timelockControllerBenchCorrect :
    runtimeEquivalence config timelockControllerBenchBytecode contract := by
  sorry

theorem timelockControllerBenchContractCorrect :
    contractEquivalence config timelockControllerBenchCreationBytecode
      timelockControllerBenchBytecode contract :=
  contractEquivalence.intro timelockControllerBenchConstructorCorrect timelockControllerBenchCorrect

end OpenZeppelinBench.TimelockController
