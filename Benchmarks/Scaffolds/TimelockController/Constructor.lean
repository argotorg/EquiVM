import Benchmarks.Scaffolds.TimelockController.Bytecode
import Solm.Equiv

/-!
# OpenZeppelin TimelockController constructor correctness stub

The creation bytecode deploys the concrete payable wrapper with initial delay `1 days`,
`msg.sender` as admin/proposer/canceller, and `address(0)` as open executor.  The
constructor-equivalence proof is the benchmark target.
-/

open Solm ABI Ethereum Ethereum.EVM

namespace OpenZeppelinBench.TimelockController

theorem timelockControllerBenchConstructorCorrect :
    constructorEquivalence config timelockControllerBenchCreationBytecode contract
      timelockControllerBenchBytecode := by
  sorry

end OpenZeppelinBench.TimelockController
