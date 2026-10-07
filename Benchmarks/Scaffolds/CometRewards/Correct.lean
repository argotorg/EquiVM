import Benchmarks.Scaffolds.CometRewards.Constructor
import Solm.Refine

/-!
# Compound III CometRewards benchmark correctness stub

Runtime equivalence of the via-IR CometRewards dispatcher against its spec.  Proofs are the
benchmark target.
-/

open Solm ABI Ethereum Ethereum.EVM

namespace Benchmarks.CompoundIII.CometRewards

theorem cometRewardsCorrect :
    runtimeRefinement config cometRewardsBytecode contract := by
  sorry

theorem cometRewardsContractCorrect :
    contractRefinement config cometRewardsCreationBytecode contract :=
  contractRefinement.of_constant cometRewardsConstructorCorrect cometRewardsCorrect

end Benchmarks.CompoundIII.CometRewards
