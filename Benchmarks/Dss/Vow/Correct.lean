import Benchmarks.Dss.Vow.Constructor
import Solm.Equiv

/-!
# MakerDAO/Sky DSS Vow benchmark correctness stub

The upstream Solidity source, optimized runtime bytecode, Solm AST spec, and Solm syntax companion
are present. The runtime-equivalence proof is intentionally left as the benchmark target. This file
also exposes the whole-contract wrapper that combines the constructor and runtime targets.
-/

open Solm ABI Ethereum Ethereum.EVM

namespace Benchmarks.Dss.Vow

theorem vowCorrect :
    runtimeEquivalence!?! config vowBytecode contract := by
  sorry

theorem vowContractCorrect :
    contractEquivalence config vowCreationBytecode vowBytecode contract :=
  contractEquivalence.intro vowConstructorCorrect vowCorrect

end Benchmarks.Dss.Vow
