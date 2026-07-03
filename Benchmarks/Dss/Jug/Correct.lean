import Benchmarks.Dss.Jug.Constructor
import Solm.Equiv

/-!
# MakerDAO/Sky DSS Jug benchmark correctness stub

The upstream Solidity source, optimized runtime bytecode, Solm AST spec, and Solm syntax companion
are present. The runtime-equivalence proof is intentionally left as the benchmark target. This file
also exposes the whole-contract wrapper that combines the constructor and runtime targets.
-/

open Solm ABI Ethereum Ethereum.EVM

namespace Benchmarks.Dss.Jug

theorem jugCorrect :
    runtimeEquivalence!?! config jugBytecode contract := by
  sorry

theorem jugContractCorrect :
    contractEquivalence config jugCreationBytecode jugBytecode contract :=
  contractEquivalence.intro jugConstructorCorrect jugCorrect

end Benchmarks.Dss.Jug
