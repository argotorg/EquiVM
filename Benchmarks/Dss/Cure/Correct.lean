import Benchmarks.Dss.Cure.Constructor
import Solm.Equiv

/-!
# MakerDAO/Sky DSS Cure benchmark correctness stub

The upstream Solidity source, optimized runtime bytecode, Solm AST spec, and Solm syntax companion
are present. The runtime-equivalence proof is intentionally left as the benchmark target. This file
also exposes the whole-contract wrapper that combines the constructor and runtime targets.
-/

open Solm ABI Ethereum Ethereum.EVM

namespace Benchmarks.Dss.Cure

theorem cureCorrect :
    runtimeEquivalence!?! config cureBytecode contract := by
  sorry

theorem cureContractCorrect :
    contractEquivalence config cureCreationBytecode cureBytecode contract :=
  contractEquivalence.intro cureConstructorCorrect cureCorrect

end Benchmarks.Dss.Cure
