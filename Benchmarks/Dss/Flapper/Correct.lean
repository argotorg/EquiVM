import Benchmarks.Dss.Flapper.Constructor
import Solm.Equiv

/-!
# MakerDAO/Sky DSS Flapper benchmark correctness stub

The upstream Solidity source, optimized runtime bytecode, Solm AST spec, and Solm syntax companion
are present. The runtime-equivalence proof is intentionally left as the benchmark target. This file
also exposes the whole-contract wrapper that combines the constructor and runtime targets.
-/

open Solm ABI Ethereum Ethereum.EVM

namespace Benchmarks.Dss.Flapper

theorem flapperCorrect :
    runtimeEquivalence!?! config flapperBytecode contract := by
  sorry

theorem flapperContractCorrect :
    contractEquivalence config flapperCreationBytecode flapperBytecode contract :=
  contractEquivalence.intro flapperConstructorCorrect flapperCorrect

end Benchmarks.Dss.Flapper
