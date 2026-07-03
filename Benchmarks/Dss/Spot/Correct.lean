import Benchmarks.Dss.Spot.Constructor
import Solm.Equiv

/-!
# MakerDAO/Sky DSS Spotter benchmark correctness stub

The upstream Solidity source, optimized runtime bytecode, Solm AST spec, and Solm syntax companion
are present. The runtime-equivalence proof is intentionally left as the benchmark target. This file
also exposes the whole-contract wrapper that combines the constructor and runtime targets.
-/

open Solm ABI Ethereum Ethereum.EVM

namespace Benchmarks.Dss.Spot

theorem spotCorrect :
    runtimeEquivalence!?! config spotBytecode contract := by
  sorry

theorem spotContractCorrect :
    contractEquivalence config spotCreationBytecode spotBytecode contract :=
  contractEquivalence.intro spotConstructorCorrect spotCorrect

end Benchmarks.Dss.Spot
