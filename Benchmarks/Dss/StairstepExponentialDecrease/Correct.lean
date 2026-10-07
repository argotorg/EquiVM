import Benchmarks.Dss.StairstepExponentialDecrease.Constructor
import Benchmarks.Dss.StairstepExponentialDecrease.Cut
import Benchmarks.Dss.StairstepExponentialDecrease.Deny
import Benchmarks.Dss.StairstepExponentialDecrease.File
import Benchmarks.Dss.StairstepExponentialDecrease.Price
import Benchmarks.Dss.StairstepExponentialDecrease.Rely
import Benchmarks.Dss.StairstepExponentialDecrease.Step
import Benchmarks.Dss.StairstepExponentialDecrease.Wards
import Solm.Refine

/-!
# MakerDAO/Sky DSS StairstepExponentialDecrease benchmark correctness stub

The upstream Solidity source, optimized runtime bytecode, Solm AST spec, and Solm syntax companion
are present. The runtime-equivalence proof is intentionally left as the benchmark target. This file
also exposes the whole-contract wrapper that combines the constructor and runtime targets.
-/

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

set_option maxRecDepth 2000000

namespace Benchmarks.Dss.StairstepExponentialDecrease

theorem stairstepExponentialDecreaseCorrect :
    runtimeRefinement config stairstepExponentialDecreaseBytecode contract := by
  refine runtimeRefinement.intro ?_
  intro σ σ₀ g A I hcode hsize hperm
  by_cases hwv : I.weiValue = ⟨0⟩
  · by_cases hcut : selIs I (stairstepSelBytes 0)
    · exact stairstepCutBody hcode hsize hperm hwv hcut
    · by_cases hdeny : selIs I (stairstepSelBytes 1)
      · exact stairstepDenyBody hcode hsize hperm hwv hdeny
      · by_cases hfile : selIs I (stairstepSelBytes 2)
        · exact stairstepFileBody hcode hsize hperm hwv hfile
        · by_cases hprice : selIs I (stairstepSelBytes 3)
          · exact stairstepPriceBody hcode hsize hperm hwv hprice
          · by_cases hrely : selIs I (stairstepSelBytes 4)
            · exact stairstepRelyBody hcode hsize hperm hwv hrely
            · by_cases hstep : selIs I (stairstepSelBytes 5)
              · exact stairstepStepBody hcode hsize hperm hwv hstep
              · by_cases hwards : selIs I (stairstepSelBytes 6)
                · exact stairstepWardsBody hcode hsize hperm hwv hwards
                · exact stairstepNoDispatch hcode hsize hperm hwv
                    (stairstepNoSelectorMatches hcut hdeny hfile hprice hrely hstep hwards)
  · exact stairstepNonPayable hcode hwv

theorem stairstepExponentialDecreaseContractCorrect :
    contractRefinement config stairstepExponentialDecreaseCreationBytecode contract :=
  contractRefinement.of_constant stairstepExponentialDecreaseConstructorCorrect stairstepExponentialDecreaseCorrect

end Benchmarks.Dss.StairstepExponentialDecrease
