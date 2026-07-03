import Benchmarks.CompoundIII.CometRewards.Constructor
import Solm.Equiv

/-!
# Compound III CometRewards benchmark correctness stub

The upstream Solidity source closure, optimized runtime bytecode, Solm AST spec, and Solm syntax
spec are present. The runtime-equivalence proof is intentionally left as the benchmark target. This
file also exposes the whole-contract wrapper that combines the constructor and runtime targets.
-/

open Solm ABI Ethereum Ethereum.EVM

namespace Benchmarks.CompoundIII.CometRewards

theorem cometRewardsCorrect :
    runtimeEquivalence!?! config cometRewardsBytecode contract := by
  sorry

theorem cometRewardsContractCorrect :
    contractEquivalence config cometRewardsCreationBytecode cometRewardsBytecode contract :=
  contractEquivalence.intro cometRewardsConstructorCorrect cometRewardsCorrect

end Benchmarks.CompoundIII.CometRewards
