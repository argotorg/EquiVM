import Benchmarks.Dss.LinearDecrease.Constructor
import Solm.Equiv

/-!
# MakerDAO/Sky DSS LinearDecrease benchmark correctness stub

The upstream Solidity source, optimized runtime bytecode, Solm AST spec, and Solm syntax companion
are present. The runtime-equivalence proof is intentionally left as the benchmark target. This file
also exposes the whole-contract wrapper that combines the constructor and runtime targets.
-/

open Solm ABI Ethereum Ethereum.EVM

namespace Benchmarks.Dss.LinearDecrease

theorem linearDecreaseCorrect :
    runtimeEquivalence!?! config linearDecreaseBytecode contract := by
  sorry

theorem linearDecreaseContractCorrect :
    contractEquivalence config linearDecreaseCreationBytecode linearDecreaseBytecode contract :=
  contractEquivalence.intro linearDecreaseConstructorCorrect linearDecreaseCorrect

end Benchmarks.Dss.LinearDecrease
