import Benchmarks.Safe.Constructor
import Solm.Equiv

/-!
# Safe benchmark correctness stub

The upstream Solidity source tree, optimized runtime bytecode, Solm AST spec, and Solm syntax spec
are present. The runtime-equivalence proof is intentionally left as the benchmark target. This file
also exposes the whole-contract wrapper that combines the constructor and runtime targets.
-/

open Solm ABI Ethereum Ethereum.EVM

namespace Benchmarks.Safe

theorem safeCorrect :
    runtimeEquivalence config safeBytecode contract := by
  sorry

theorem safeContractCorrect :
    contractEquivalence config safeCreationBytecode safeBytecode contract :=
  contractEquivalence.intro safeConstructorCorrect safeCorrect

end Benchmarks.Safe
