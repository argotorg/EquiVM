import Benchmarks.Scaffolds.CometRewards.Constructor
import Solm.Equiv

/-!
# Compound III CometRewards benchmark correctness stub

Runtime equivalence of the via-IR CometRewards dispatcher against its spec.  Proofs are the
benchmark target.
-/

open Solm ABI Ethereum Ethereum.EVM

namespace Benchmarks.CompoundIII.CometRewards

theorem cometRewardsCorrect :
    runtimeEquivalence config cometRewardsBytecode contract := by
  sorry

theorem cometRewardsContractCorrect :
    contractEquivalence config cometRewardsCreationBytecode cometRewardsBytecode contract :=
  contractEquivalence.intro cometRewardsConstructorCorrect cometRewardsCorrect

end Benchmarks.CompoundIII.CometRewards
