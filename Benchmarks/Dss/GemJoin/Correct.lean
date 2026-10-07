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

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Dss.GemJoin

theorem gemJoinCorrect :
    runtimeEquivalenceAnyPerm config gemJoinBytecode contract := by
  refine runtimeEquivalenceAnyPerm.intro ?_
  intro σ σ₀ g A I hcode hsize
  by_cases hwv : I.weiValue = ⟨0⟩
  · by_cases hcage : selIs I (gemJoinSelBytes 0)
    · exact gemJoinCageBodyCoreAnyPerm hcode hsize hwv hcage
    · by_cases hdec : selIs I (gemJoinSelBytes 1)
      · exact gemJoinDecBodyCore hcode hsize hwv hdec
      · by_cases hdeny : selIs I (gemJoinSelBytes 2)
        · exact gemJoinDenyBodyCoreAnyPerm hcode hsize hwv hdeny
        · by_cases hexit : selIs I (gemJoinSelBytes 3)
          · exact gemJoinExitBodyCore hcode hsize hwv hexit
          · by_cases hgem : selIs I (gemJoinSelBytes 4)
            · exact gemJoinGemBodyCore hcode hsize hwv hgem
            · by_cases hilk : selIs I (gemJoinSelBytes 5)
              · exact gemJoinIlkBodyCore hcode hsize hwv hilk
              · by_cases hjoin : selIs I (gemJoinSelBytes 6)
                · exact gemJoinJoinBodyCore hcode hsize hwv hjoin
                · by_cases hlive : selIs I (gemJoinSelBytes 7)
                  · exact gemJoinLiveBodyCore hcode hsize hwv hlive
                  · by_cases hrely : selIs I (gemJoinSelBytes 8)
                    · exact gemJoinRelyBodyCoreAnyPerm hcode hsize hwv hrely
                    · by_cases hvat : selIs I (gemJoinSelBytes 9)
                      · exact gemJoinVatBodyCore hcode hsize hwv hvat
                      · by_cases hwards : selIs I (gemJoinSelBytes 10)
                        · exact gemJoinWardsBodyCore hcode hsize hwv hwards
                        · exact gemJoinNoDispatch hcode hsize hwv
                            (gemJoinNoSelectorMatches hcage hdec hdeny hexit hgem hilk hjoin hlive
                              hrely hvat hwards)
  · exact gemJoinNonPayable hcode hwv

theorem gemJoinContractCorrect :
    contractEquivalenceAnyPerm config gemJoinCreationBytecode gemJoinBytecode contract :=
  contractEquivalenceAnyPerm.intro gemJoinConstructorCorrect gemJoinCorrect

end Benchmarks.Dss.GemJoin
