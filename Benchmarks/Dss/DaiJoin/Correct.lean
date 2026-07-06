import Benchmarks.Dss.DaiJoin.Constructor
import Solm.Equiv

/-!
# MakerDAO/Sky DSS DaiJoin benchmark correctness stub

The upstream Solidity source, optimized runtime bytecode, Solm AST spec, and Solm syntax companion
are present. The runtime-equivalence proof is intentionally left as the benchmark target. This file
also exposes the whole-contract wrapper that combines the constructor and runtime targets.
-/

open Solm ABI Ethereum Ethereum.EVM

namespace Benchmarks.Dss.DaiJoin

theorem daiJoinCorrect :
    runtimeEquivalence!?! config daiJoinBytecode contract := by
  sorry

theorem daiJoinContractCorrect :
    contractEquivalence config daiJoinCreationBytecode daiJoinBytecode contract :=
  contractEquivalence.intro daiJoinConstructorCorrect daiJoinCorrect

end Benchmarks.Dss.DaiJoin
