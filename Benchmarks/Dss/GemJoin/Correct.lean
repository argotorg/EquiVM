import Benchmarks.Dss.GemJoin.Constructor
import Solm.Equiv

/-!
# MakerDAO/Sky DSS GemJoin benchmark correctness stub

The upstream Solidity source, optimized runtime bytecode, Solm AST spec, and Solm syntax companion
are present. The runtime-equivalence proof is intentionally left as the benchmark target. This file
also exposes the whole-contract wrapper that combines the constructor and runtime targets.
-/

open Solm ABI Ethereum Ethereum.EVM

namespace Benchmarks.Dss.GemJoin

theorem gemJoinCorrect :
    runtimeEquivalence!?! config gemJoinBytecode contract := by
  sorry

theorem gemJoinContractCorrect :
    contractEquivalence config gemJoinCreationBytecode gemJoinBytecode contract :=
  contractEquivalence.intro gemJoinConstructorCorrect gemJoinCorrect

end Benchmarks.Dss.GemJoin
