import Benchmarks.Scaffolds.CometRewards.Bytecode
import Solm.Equiv

/-!
# Compound III CometRewards constructor correctness stub

The creation bytecode stores the deployer as `governor` and returns the runtime.  The
constructor-equivalence proof is the benchmark target.
-/

open Solm ABI Ethereum Ethereum.EVM

namespace Benchmarks.CompoundIII.CometRewards

theorem cometRewardsConstructorCorrect :
    constructorEquivalence config cometRewardsCreationBytecode contract cometRewardsBytecode := by
  sorry

end Benchmarks.CompoundIII.CometRewards
