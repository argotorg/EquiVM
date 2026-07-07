import Benchmarks.CompoundIII.CometRewards.Claim
import Benchmarks.CompoundIII.CometRewards.ClaimTo
import Benchmarks.CompoundIII.CometRewards.Constructor
import Benchmarks.CompoundIII.CometRewards.GetRewardOwed
import Benchmarks.CompoundIII.CometRewards.Governor
import Benchmarks.CompoundIII.CometRewards.RewardConfig
import Benchmarks.CompoundIII.CometRewards.RewardsClaimed
import Benchmarks.CompoundIII.CometRewards.SetRewardConfig
import Benchmarks.CompoundIII.CometRewards.SetRewardConfigWithMultiplier
import Benchmarks.CompoundIII.CometRewards.SetRewardsClaimed
import Benchmarks.CompoundIII.CometRewards.TransferGovernor
import Benchmarks.CompoundIII.CometRewards.WithdrawToken
import Solm.Equiv

/-!
# Compound III CometRewards benchmark correctness scaffold

This file assembles the CometRewards runtime dispatcher.  Function-body correctness obligations
live in their own files; shared via-IR dispatcher reach obligations live in `Common.lean`.
-/

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach Reasoning.Refinement

namespace Benchmarks.CompoundIII.CometRewards

theorem cometRewardsCorrect :
    runtimeEquivalence!?! config cometRewardsBytecode contract := by
  refine ⟨fun cA gh bl σ_evm σ_solm σ₀ g A I hcode hsize hperm
      hAccounts => ?_⟩
  by_cases hwv : I.weiValue = ⟨0⟩
  · by_cases hsz : 4 ≤ I.calldata.size
    · by_cases h0 : selIs I (cometRewardsSelBytes 0)
      · exact cometRewardsWithdrawTokenBodyCore hcode hsize hperm hwv h0
          (cometRewardsReachWithdrawToken hcode hsz hsize h0) hAccounts
      · by_cases h1 : selIs I (cometRewardsSelBytes 1)
        · exact cometRewardsGovernorBodyCore hcode hsize hperm hwv h1
            (cometRewardsReachGovernor hcode hsz hsize h1) hAccounts
        · by_cases h2 : selIs I (cometRewardsSelBytes 2)
          · exact cometRewardsRewardConfigBodyCore hcode hsize hperm hwv h2
              (cometRewardsReachRewardConfig hcode hsz hsize h2) hAccounts
          · by_cases h3 : selIs I (cometRewardsSelBytes 3)
            · exact cometRewardsGetRewardOwedBodyCore hcode hsize hperm hwv h3
                (cometRewardsReachGetRewardOwed hcode hsz hsize h3) hAccounts
            · by_cases h4 : selIs I (cometRewardsSelBytes 4)
              · exact cometRewardsClaimToBodyCore hcode hsize hperm hwv h4
                  (cometRewardsReachClaimTo hcode hsz hsize h4) hAccounts
              · by_cases h5 : selIs I (cometRewardsSelBytes 5)
                · exact cometRewardsSetRewardsClaimedBodyCore hcode hsize hperm hwv h5
                    (cometRewardsReachSetRewardsClaimed hcode hsz hsize h5) hAccounts
                · by_cases h6 : selIs I (cometRewardsSelBytes 6)
                  · exact cometRewardsRewardsClaimedBodyCore hcode hsize hperm hwv h6
                      (cometRewardsReachRewardsClaimed hcode hsz hsize h6) hAccounts
                  · by_cases h7 : selIs I (cometRewardsSelBytes 7)
                    · exact cometRewardsSetRewardConfigBodyCore hcode hsize hperm hwv h7
                        (cometRewardsReachSetRewardConfig hcode hsz hsize h7) hAccounts
                    · by_cases h8 : selIs I (cometRewardsSelBytes 8)
                      · exact cometRewardsClaimBodyCore hcode hsize hperm hwv h8
                          (cometRewardsReachClaim hcode hsz hsize h8) hAccounts
                      · by_cases h9 : selIs I (cometRewardsSelBytes 9)
                        · exact cometRewardsTransferGovernorBodyCore hcode hsize hperm hwv h9
                            (cometRewardsReachTransferGovernor hcode hsz hsize h9) hAccounts
                        · by_cases h10 : selIs I (cometRewardsSelBytes 10)
                          · exact cometRewardsSetRewardConfigWithMultiplierBodyCore hcode hsize
                              hperm hwv h10
                              (cometRewardsReachSetRewardConfigWithMultiplier hcode hsz hsize
                                h10)
                              hAccounts
                          · refine cometRewardsNoDispatch hcode hsize hperm hwv ?_
                            intro i hi
                            interval_cases i
                            · simpa [selIs, cometRewardsSelBytes] using h0
                            · simpa [selIs, cometRewardsSelBytes] using h1
                            · simpa [selIs, cometRewardsSelBytes] using h2
                            · simpa [selIs, cometRewardsSelBytes] using h3
                            · simpa [selIs, cometRewardsSelBytes] using h4
                            · simpa [selIs, cometRewardsSelBytes] using h5
                            · simpa [selIs, cometRewardsSelBytes] using h6
                            · simpa [selIs, cometRewardsSelBytes] using h7
                            · simpa [selIs, cometRewardsSelBytes] using h8
                            · simpa [selIs, cometRewardsSelBytes] using h9
                            · simpa [selIs, cometRewardsSelBytes] using h10
    · exact cometRewardsShortRevert hcode hsize hperm hwv (by omega)
  · exact cometRewardsNonPayable hcode hsize hwv

theorem cometRewardsContractCorrect :
    contractEquivalence config cometRewardsCreationBytecode cometRewardsBytecode contract :=
  contractEquivalence.intro cometRewardsConstructorCorrect cometRewardsCorrect

end Benchmarks.CompoundIII.CometRewards
