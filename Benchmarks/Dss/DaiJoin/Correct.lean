import Benchmarks.Dss.DaiJoin.Constructor
import Benchmarks.Dss.DaiJoin.Cage
import Benchmarks.Dss.DaiJoin.Dai
import Benchmarks.Dss.DaiJoin.Deny
import Benchmarks.Dss.DaiJoin.ExitRuntime
import Benchmarks.Dss.DaiJoin.Join
import Benchmarks.Dss.DaiJoin.Live
import Benchmarks.Dss.DaiJoin.Rely
import Benchmarks.Dss.DaiJoin.Vat
import Benchmarks.Dss.DaiJoin.Wards
import Solm.Equiv

/-!
# MakerDAO/Sky DSS DaiJoin benchmark correctness stub

The upstream Solidity source, optimized runtime bytecode, Solm AST spec, and Solm syntax companion
are present. The runtime-equivalence proof is intentionally left as the benchmark target. This file
also exposes the whole-contract wrapper that combines the constructor and runtime targets.
-/

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach Reasoning.Refinement

set_option maxRecDepth 2000000

namespace Benchmarks.Dss.DaiJoin

theorem daiJoinCorrect :
    runtimeEquivalence config daiJoinBytecode contract := by
  refine runtimeEquivalence.intro ?_
  intro cA gh bl σ_evm σ_solm σ₀ g A I hcode hsize hperm hAccounts
  by_cases hwv : I.weiValue = ⟨0⟩
  · by_cases hcage : selIs I (daiJoinSelBytes 0)
    · exact daiJoinCageBodyCore hcode hsize hperm hwv hcage hAccounts
    · by_cases hdai : selIs I (daiJoinSelBytes 1)
      · exact daiJoinDaiBodyCore hcode hsize hperm hwv hdai hAccounts
      · by_cases hdeny : selIs I (daiJoinSelBytes 2)
        · exact daiJoinDenyBodyCore hcode hsize hperm hwv hdeny hAccounts
        · by_cases hexit : selIs I (daiJoinSelBytes 3)
          · exact daiJoinExitBodyCore hcode hsize hperm hwv hexit hAccounts
          · by_cases hjoin : selIs I (daiJoinSelBytes 4)
            · exact daiJoinJoinBodyCore hcode hsize hperm hwv hjoin hAccounts
            · by_cases hlive : selIs I (daiJoinSelBytes 5)
              · exact daiJoinLiveBodyCore hcode hsize hperm hwv hlive hAccounts
              · by_cases hrely : selIs I (daiJoinSelBytes 6)
                · exact daiJoinRelyBodyCore hcode hsize hperm hwv hrely hAccounts
                · by_cases hvat : selIs I (daiJoinSelBytes 7)
                  · exact daiJoinVatBodyCore hcode hsize hperm hwv hvat hAccounts
                  · by_cases hwards : selIs I (daiJoinSelBytes 8)
                    · exact daiJoinWardsBodyCore hcode hsize hperm hwv hwards hAccounts
                    · exact daiJoinNoDispatch hcode hsize hperm hwv
                        (daiJoinNoSelectorMatches hcage hdai hdeny hexit hjoin hlive hrely hvat
                          hwards)
                        hAccounts
  · exact daiJoinNonPayable hcode hwv

theorem daiJoinContractCorrect :
    contractEquivalence config daiJoinCreationBytecode daiJoinBytecode contract :=
  contractEquivalence.intro daiJoinConstructorCorrect daiJoinCorrect

end Benchmarks.Dss.DaiJoin
