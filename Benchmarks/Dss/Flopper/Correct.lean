import Benchmarks.Dss.Flopper.Constructor
import Solm.Equiv

/-!
# MakerDAO/Sky DSS Flopper benchmark correctness stub

The upstream Solidity source, optimized runtime bytecode, Solm AST spec, and Solm syntax companion
are present. The runtime-equivalence proof is intentionally left as the benchmark target. This file
also exposes the whole-contract wrapper that combines the constructor and runtime targets.
-/

open Solm ABI Ethereum Ethereum.EVM

namespace Benchmarks.Dss.Flopper

theorem flopperCorrect :
    runtimeEquivalence!?! config flopperBytecode contract := by
  sorry

theorem flopperContractCorrect :
    contractEquivalence config flopperCreationBytecode flopperBytecode contract :=
  contractEquivalence.intro flopperConstructorCorrect flopperCorrect

end Benchmarks.Dss.Flopper
