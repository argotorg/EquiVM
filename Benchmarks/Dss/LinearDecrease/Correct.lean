import Benchmarks.Dss.LinearDecrease.Constructor
import Benchmarks.Dss.LinearDecrease.Deny
import Benchmarks.Dss.LinearDecrease.File
import Benchmarks.Dss.LinearDecrease.Price
import Benchmarks.Dss.LinearDecrease.Rely
import Benchmarks.Dss.LinearDecrease.Tau
import Benchmarks.Dss.LinearDecrease.Wards
import Solm.Refine

/-!
# MakerDAO/Sky DSS LinearDecrease benchmark correctness

The runtime proof dispatches to the function proofs and combines with the constructor proof for
whole-contract equivalence.
-/

open Solm ABI Ethereum Ethereum.EVM

namespace Benchmarks.Dss.LinearDecrease

theorem linearDecreaseCorrect :
    runtimeRefinement config linearDecreaseBytecode contract := by
  refine runtimeRefinement.intro ?_
  intro σ σ₀ g A I hcode hsize hperm
  by_cases hwv : I.weiValue = ⟨0⟩
  · by_cases hdeny : selIs I (stairstepSelBytes 0)
    · exact stairstepDenyBody hcode hsize hperm hwv hdeny
    · by_cases hfile : selIs I (stairstepSelBytes 1)
      · exact stairstepFileBody hcode hsize hperm hwv hfile
      · by_cases hprice : selIs I (stairstepSelBytes 2)
        · exact stairstepPriceBody hcode hsize hperm hwv hprice
        · by_cases hrely : selIs I (stairstepSelBytes 3)
          · exact stairstepRelyBody hcode hsize hperm hwv hrely
          · by_cases htau : selIs I (stairstepSelBytes 4)
            · exact stairstepTauBody hcode hsize hperm hwv htau
            · by_cases hwards : selIs I (stairstepSelBytes 5)
              · exact stairstepWardsBody hcode hsize hperm hwv hwards
              · exact stairstepNoDispatch hcode hsize hperm hwv
                  (stairstepNoSelectorMatches hdeny hfile hprice hrely htau hwards)
  · exact stairstepNonPayable hcode hwv

theorem linearDecreaseContractCorrect :
    contractRefinement config linearDecreaseCreationBytecode contract :=
  contractRefinement.of_constant linearDecreaseConstructorCorrect linearDecreaseCorrect

end Benchmarks.Dss.LinearDecrease
