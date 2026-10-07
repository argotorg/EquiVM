import Benchmarks.Safe.Constructor
import Benchmarks.Safe.Runtime
import Benchmarks.Safe.Blocks
import Solm.Refine

/-!
# Safe benchmark correctness stub

The upstream Solidity source tree, optimized runtime bytecode, Solm AST spec, and Solm syntax spec
are present. `Runtime.lean` separates all 31 selectors, receive, and fallback into unconditional
refinement obligations. `Blocks.lean` imports the generated instruction summaries. The runtime
assembly proof remains intentionally unproved. This file also exposes the whole-contract wrapper
that combines the constructor and runtime targets.
-/

open Solm ABI Ethereum Ethereum.EVM

namespace Benchmarks.Safe

theorem safeCorrect :
    runtimeRefinement config safeBytecode contract := by
  sorry

theorem safeContractCorrect :
    contractRefinement config safeCreationBytecode contract :=
  contractRefinement.of_constant safeConstructorCorrect safeCorrect

end Benchmarks.Safe
