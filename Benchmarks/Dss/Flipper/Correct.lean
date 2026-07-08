import Benchmarks.Dss.Flipper.Constructor
import Solm.Equiv

/-!
# MakerDAO/Sky DSS Flipper benchmark correctness stub

The upstream Solidity source, optimized runtime bytecode, Solm AST spec, and Solm syntax companion
are present. The runtime-equivalence proof is intentionally left as the benchmark target. This file
also exposes the whole-contract wrapper that combines the constructor and runtime targets.
-/

open Solm ABI Ethereum Ethereum.EVM

namespace Benchmarks.Dss.Flipper

theorem flipperCorrect :
    runtimeEquivalence!?! config flipperBytecode contract := by
  sorry

theorem flipperContractCorrect :
    contractEquivalence config flipperCreationBytecode flipperBytecode contract :=
  contractEquivalence.intro flipperConstructorCorrect flipperCorrect

end Benchmarks.Dss.Flipper
