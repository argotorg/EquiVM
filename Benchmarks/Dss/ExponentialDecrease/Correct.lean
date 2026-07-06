import Benchmarks.Dss.ExponentialDecrease.Constructor
import Solm.Equiv

/-!
# MakerDAO/Sky DSS ExponentialDecrease benchmark correctness stub

The upstream Solidity source, optimized runtime bytecode, Solm AST spec, and Solm syntax companion
are present. The runtime-equivalence proof is intentionally left as the benchmark target. This file
also exposes the whole-contract wrapper that combines the constructor and runtime targets.
-/

open Solm ABI Ethereum Ethereum.EVM

namespace Benchmarks.Dss.ExponentialDecrease

theorem exponentialDecreaseCorrect :
    runtimeEquivalence!?! config exponentialDecreaseBytecode contract := by
  sorry

theorem exponentialDecreaseContractCorrect :
    contractEquivalence config exponentialDecreaseCreationBytecode exponentialDecreaseBytecode contract :=
  contractEquivalence.intro exponentialDecreaseConstructorCorrect exponentialDecreaseCorrect

end Benchmarks.Dss.ExponentialDecrease
