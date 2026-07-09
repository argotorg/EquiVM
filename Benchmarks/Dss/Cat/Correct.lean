import Benchmarks.Dss.Cat.Constructor
import Solm.Equiv

/-!
# MakerDAO/Sky DSS Cat benchmark correctness stub

The upstream Solidity source, optimized runtime bytecode, Solm AST spec, and Solm syntax companion
are present. The runtime-equivalence proof is intentionally left as the benchmark target. This file
also exposes the whole-contract wrapper that combines the constructor and runtime targets.
-/

open Solm ABI Ethereum Ethereum.EVM

namespace Benchmarks.Dss.Cat

theorem catCorrect :
    runtimeEquivalence!?! config catBytecode contract := by
  sorry

theorem catContractCorrect :
    contractEquivalence config catCreationBytecode catBytecode contract :=
  contractEquivalence.intro catConstructorCorrect catCorrect

end Benchmarks.Dss.Cat
