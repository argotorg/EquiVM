import Benchmarks.Dss.StairstepExponentialDecrease.Constructor
import Benchmarks.Dss.StairstepExponentialDecrease.Cut
import Benchmarks.Dss.StairstepExponentialDecrease.Deny
import Benchmarks.Dss.StairstepExponentialDecrease.File
import Benchmarks.Dss.StairstepExponentialDecrease.Price
import Benchmarks.Dss.StairstepExponentialDecrease.Rely
import Benchmarks.Dss.StairstepExponentialDecrease.Step
import Benchmarks.Dss.StairstepExponentialDecrease.Wards
import Solm.Equiv

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
    runtimeEquivalenceAnyPerm config stairstepExponentialDecreaseBytecode contract := by
  refine runtimeEquivalenceAnyPerm.intro ?_
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
            · by_cases hstep : selIs I (stairstepSelBytes 5)
              · exact stairstepStepBody hcode hsize hwv hstep
              · by_cases hwards : selIs I (stairstepSelBytes 6)
                · exact stairstepWardsBody hcode hsize hwv hwards
                · exact stairstepNoDispatch hcode hsize hwv
                    (stairstepNoSelectorMatches hcut hdeny hfile hprice hrely hstep hwards)
  · exact stairstepNonPayable hcode hwv

theorem stairstepExponentialDecreaseContractCorrect :
    contractEquivalenceAnyPerm config stairstepExponentialDecreaseCreationBytecode
      stairstepExponentialDecreaseBytecode contract :=
  contractEquivalenceAnyPerm.intro stairstepExponentialDecreaseConstructorCorrect
    stairstepExponentialDecreaseCorrect

end Benchmarks.Dss.StairstepExponentialDecrease
