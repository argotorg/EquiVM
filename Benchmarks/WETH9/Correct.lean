import Benchmarks.WETH9.Constructor
import Solm.Equiv

/-!
# WETH9 benchmark correctness stub

The upstream Solidity source, optimized runtime bytecode, Solm AST spec, and Solm syntax spec are
present.  The runtime-equivalence proof is intentionally left as the benchmark target.  This file
also exposes the whole-contract wrapper that combines the constructor and runtime targets.
-/

open Solm ABI Ethereum Ethereum.EVM

namespace Benchmarks.WETH9

theorem weth9Correct :
    runtimeEquivalence!?! config weth9Bytecode contract := by
  sorry

theorem weth9ContractCorrect :
    contractEquivalence config weth9CreationBytecode weth9Bytecode contract :=
  contractEquivalence.intro weth9ConstructorCorrect weth9Correct

end Benchmarks.WETH9
