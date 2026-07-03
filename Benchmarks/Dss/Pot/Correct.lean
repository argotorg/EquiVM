import Benchmarks.Dss.Pot.Constructor
import Solm.Equiv

/-!
# MakerDAO/Sky DSS Pot benchmark correctness stub

The upstream Solidity source, optimized runtime bytecode, Solm AST spec, and Solm syntax companion
are present. The runtime-equivalence proof is intentionally left as the benchmark target. This file
also exposes the whole-contract wrapper that combines the constructor and runtime targets.
-/

open Solm ABI Ethereum Ethereum.EVM

namespace Benchmarks.Dss.Pot

theorem potCorrect :
    runtimeEquivalence!?! config potBytecode contract := by
  sorry

theorem potContractCorrect :
    contractEquivalence config potCreationBytecode potBytecode contract :=
  contractEquivalence.intro potConstructorCorrect potCorrect

end Benchmarks.Dss.Pot
