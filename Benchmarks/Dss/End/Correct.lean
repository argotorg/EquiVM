import Benchmarks.Dss.End.Constructor
import Solm.Equiv

/-!
# MakerDAO/Sky DSS End benchmark correctness stub

The upstream Solidity source, optimized runtime bytecode, Solm AST spec, and Solm syntax companion
are present. The runtime-equivalence proof is intentionally left as the benchmark target. This file
also exposes the whole-contract wrapper that combines the constructor and runtime targets.
-/

open Solm ABI Ethereum Ethereum.EVM

namespace Benchmarks.Dss.End

theorem endCorrect :
    runtimeEquivalence!?! config endBytecode contract := by
  sorry

theorem endContractCorrect :
    contractEquivalence config endCreationBytecode endBytecode contract :=
  contractEquivalence.intro endConstructorCorrect endCorrect

end Benchmarks.Dss.End
