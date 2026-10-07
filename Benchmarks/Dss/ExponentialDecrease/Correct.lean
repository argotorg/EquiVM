import Benchmarks.Dss.ExponentialDecrease.Constructor
import Benchmarks.Dss.ExponentialDecrease.Cut
import Benchmarks.Dss.ExponentialDecrease.Deny
import Benchmarks.Dss.ExponentialDecrease.File
import Benchmarks.Dss.ExponentialDecrease.Price
import Benchmarks.Dss.ExponentialDecrease.Rely
import Benchmarks.Dss.ExponentialDecrease.Wards
import Solm.Equiv

/-!
# MakerDAO/Sky DSS ExponentialDecrease benchmark correctness stub

The upstream Solidity source, optimized runtime bytecode, Solm AST spec, and Solm syntax companion
are present. The runtime-equivalence proof is intentionally left as the benchmark target. This file
also exposes the whole-contract wrapper that combines the constructor and runtime targets.
-/

open Solm ABI Ethereum Ethereum.EVM

namespace Benchmarks.Dss.ExponentialDecrease

theorem exponentialDecreaseCorrect :
    runtimeEquivalence config exponentialDecreaseBytecode contract := by
  refine runtimeEquivalence.intro ?_
  intro σ σ₀ g A I hcode hsize
  by_cases hwv : I.weiValue = ⟨0⟩
  · by_cases hcut : selIs I (stairstepSelBytes 0)
    · exact stairstepCutBody hcode hsize hwv hcut
    · by_cases hdeny : selIs I (stairstepSelBytes 1)
      · exact stairstepDenyBodyAnyPerm hcode hsize hwv hdeny
      · by_cases hfile : selIs I (stairstepSelBytes 2)
        · exact stairstepFileBody hcode hsize hwv hfile
        · by_cases hprice : selIs I (stairstepSelBytes 3)
          · exact stairstepPriceBody hcode hsize hwv hprice
          · by_cases hrely : selIs I (stairstepSelBytes 4)
            · exact stairstepRelyBodyAnyPerm hcode hsize hwv hrely
            · by_cases hwards : selIs I (stairstepSelBytes 5)
              · exact stairstepWardsBody hcode hsize hwv hwards
              · exact stairstepNoDispatch hcode hsize hwv
                  (stairstepNoSelectorMatches hcut hdeny hfile hprice hrely hwards)
  · exact stairstepNonPayable hcode hwv

theorem exponentialDecreaseContractCorrect :
    contractEquivalence config exponentialDecreaseCreationBytecode
      exponentialDecreaseBytecode contract :=
  contractEquivalence.intro exponentialDecreaseConstructorCorrect exponentialDecreaseCorrect

end Benchmarks.Dss.ExponentialDecrease
