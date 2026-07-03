import Benchmarks.Dss.Vat.Constructor
import Solm.Equiv

/-!
# MakerDAO/Sky DSS Vat benchmark correctness stub

The upstream Solidity source, optimized runtime bytecode, Solm AST spec, and Solm syntax companion
are present. The runtime-equivalence proof is intentionally left as the benchmark target. This file
also exposes the whole-contract wrapper that combines the constructor and runtime targets.
-/

open Solm ABI Ethereum Ethereum.EVM

namespace Benchmarks.Dss.Vat

theorem vatCorrect :
    runtimeEquivalence!?! config vatBytecode contract := by
  sorry

theorem vatContractCorrect :
    contractEquivalence config vatCreationBytecode vatBytecode contract :=
  contractEquivalence.intro vatConstructorCorrect vatCorrect

end Benchmarks.Dss.Vat
