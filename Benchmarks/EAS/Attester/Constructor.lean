import Benchmarks.EAS.Attester.Common
import Solm.Refine

/-!
# EAS Attester constructor correctness stub

The constructor sets `_eas`.  `typedConstructorRefinement` checks that the runtime the EVM returns
is the template patched with the constructor's final immutables (`deployedRuntime`), and that those
are well typed.  Proof left as the benchmark target.
-/

open Solm ABI Ethereum Ethereum.EVM Benchmarks.EAS.Attester.Immutables

namespace Benchmarks.EAS.Attester

theorem attesterConstructorCorrect :
    typedConstructorRefinement config attesterCreationBytecode contract
      (deployedRuntime attesterBytecode) := by
  sorry

end Benchmarks.EAS.Attester
