import Benchmarks.Dss.Dai.Constructor
import Solm.Equiv

/-!
# MakerDAO DSS Dai benchmark correctness stub

The upstream Solidity source, optimized runtime bytecode, Solm AST spec, and Solm syntax companion
are present. The runtime-equivalence proof is intentionally left as the benchmark target. This file
also exposes the whole-contract wrapper that combines the constructor and runtime targets.
-/

open Solm ABI Ethereum Ethereum.EVM

namespace Benchmarks.Dss.Dai

theorem daiCorrect :
    runtimeEquivalence!?! config daiBytecode contract := by
  sorry

theorem daiContractCorrect :
    contractEquivalence config daiCreationBytecode daiBytecode contract :=
  contractEquivalence.intro daiConstructorCorrect daiCorrect

end Benchmarks.Dss.Dai
