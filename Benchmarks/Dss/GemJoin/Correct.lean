import Benchmarks.Dss.GemJoin.Constructor
import Benchmarks.Dss.GemJoin.Cage
import Benchmarks.Dss.GemJoin.Dec
import Benchmarks.Dss.GemJoin.Deny
import Benchmarks.Dss.GemJoin.Exit
import Benchmarks.Dss.GemJoin.Gem
import Benchmarks.Dss.GemJoin.Ilk
import Benchmarks.Dss.GemJoin.Join
import Benchmarks.Dss.GemJoin.Live
import Benchmarks.Dss.GemJoin.Rely
import Benchmarks.Dss.GemJoin.Vat
import Benchmarks.Dss.GemJoin.Wards

/-!
# MakerDAO/Sky DSS GemJoin benchmark correctness

This file exposes the runtime-equivalence proof and the whole-contract wrapper that combines
the constructor and runtime targets.
-/

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach Reasoning.Refinement

namespace Benchmarks.Dss.GemJoin

theorem gemJoinCorrect :
    runtimeEquivalence!?! config gemJoinBytecode contract := by
  refine runtimeEquivalence!?!.intro ?_
  intro cA gh bl σ_evm σ_solm σ₀ g A I hcode hsize hperm hAccounts
  by_cases hwv : I.weiValue = ⟨0⟩
  · by_cases hcage : selIs I (gemJoinSelBytes 0)
    · exact gemJoinCageBodyCore hcode hsize hperm hwv hcage hAccounts
    · by_cases hdec : selIs I (gemJoinSelBytes 1)
      · exact gemJoinDecBodyCore hcode hsize hperm hwv hdec hAccounts
      · by_cases hdeny : selIs I (gemJoinSelBytes 2)
        · exact gemJoinDenyBodyCore hcode hsize hperm hwv hdeny hAccounts
        · by_cases hexit : selIs I (gemJoinSelBytes 3)
          · exact gemJoinExitBodyCore hcode hsize hperm hwv hexit hAccounts
          · by_cases hgem : selIs I (gemJoinSelBytes 4)
            · exact gemJoinGemBodyCore hcode hsize hperm hwv hgem hAccounts
            · by_cases hilk : selIs I (gemJoinSelBytes 5)
              · exact gemJoinIlkBodyCore hcode hsize hperm hwv hilk hAccounts
              · by_cases hjoin : selIs I (gemJoinSelBytes 6)
                · exact gemJoinJoinBodyCore hcode hsize hperm hwv hjoin hAccounts
                · by_cases hlive : selIs I (gemJoinSelBytes 7)
                  · exact gemJoinLiveBodyCore hcode hsize hperm hwv hlive hAccounts
                  · by_cases hrely : selIs I (gemJoinSelBytes 8)
                    · exact gemJoinRelyBodyCore hcode hsize hperm hwv hrely hAccounts
                    · by_cases hvat : selIs I (gemJoinSelBytes 9)
                      · exact gemJoinVatBodyCore hcode hsize hperm hwv hvat hAccounts
                      · by_cases hwards : selIs I (gemJoinSelBytes 10)
                        · exact gemJoinWardsBodyCore hcode hsize hperm hwv hwards hAccounts
                        · exact gemJoinNoDispatch hcode hsize hperm hwv
                            (gemJoinNoSelectorMatches hcage hdec hdeny hexit hgem hilk hjoin hlive
                              hrely hvat hwards)
                            hAccounts
  · exact gemJoinNonPayable hcode hwv

theorem gemJoinContractCorrect :
    contractEquivalence config gemJoinCreationBytecode gemJoinBytecode contract :=
  contractEquivalence.intro gemJoinConstructorCorrect gemJoinCorrect

end Benchmarks.Dss.GemJoin
