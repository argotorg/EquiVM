import Benchmarks.Dss.LinearDecrease.Constructor
import Benchmarks.Dss.LinearDecrease.Deny
import Benchmarks.Dss.LinearDecrease.File
import Benchmarks.Dss.LinearDecrease.Price
import Benchmarks.Dss.LinearDecrease.Rely
import Benchmarks.Dss.LinearDecrease.Tau
import Benchmarks.Dss.LinearDecrease.Wards
import Solm.Equiv

/-!
# MakerDAO/Sky DSS LinearDecrease benchmark correctness stub

The upstream Solidity source, optimized runtime bytecode, Solm AST spec, and Solm syntax companion
are present. The runtime-equivalence proof is intentionally left as the benchmark target. This file
also exposes the whole-contract wrapper that combines the constructor and runtime targets.
-/

open Solm ABI Ethereum Ethereum.EVM

namespace Benchmarks.Dss.LinearDecrease

theorem linearDecreaseCorrect :
    runtimeEquivalence!?! config linearDecreaseBytecode contract := by
  refine runtimeEquivalence!?!.intro ?_
  intro cA gh bl σ_evm σ_solm σ₀ g A I hcode hsize hperm hAccounts
  by_cases hwv : I.weiValue = ⟨0⟩
  · by_cases hdeny : selIs I (stairstepSelBytes 0)
    · exact stairstepDenyBody hcode hsize hperm hwv hdeny hAccounts
    · by_cases hfile : selIs I (stairstepSelBytes 1)
      · exact stairstepFileBody hcode hsize hperm hwv hfile hAccounts
      · by_cases hprice : selIs I (stairstepSelBytes 2)
        · exact stairstepPriceBody hcode hsize hperm hwv hprice hAccounts
        · by_cases hrely : selIs I (stairstepSelBytes 3)
          · exact stairstepRelyBody hcode hsize hperm hwv hrely hAccounts
          · by_cases htau : selIs I (stairstepSelBytes 4)
            · exact stairstepTauBody hcode hsize hperm hwv htau hAccounts
            · by_cases hwards : selIs I (stairstepSelBytes 5)
              · exact stairstepWardsBody hcode hsize hperm hwv hwards hAccounts
              · exact stairstepNoDispatch hcode hsize hperm hwv
                  (stairstepNoSelectorMatches hdeny hfile hprice hrely htau hwards)
                  hAccounts
  · exact stairstepNonPayable hcode hwv

theorem linearDecreaseContractCorrect :
    contractEquivalence config linearDecreaseCreationBytecode linearDecreaseBytecode contract :=
  contractEquivalence.intro linearDecreaseConstructorCorrect linearDecreaseCorrect

end Benchmarks.Dss.LinearDecrease
