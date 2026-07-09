import Benchmarks.Dss.Spot.Constructor
import Benchmarks.Dss.Spot.Cage
import Benchmarks.Dss.Spot.Deny
import Benchmarks.Dss.Spot.FileMat
import Benchmarks.Dss.Spot.FilePar
import Benchmarks.Dss.Spot.FilePip
import Benchmarks.Dss.Spot.Ilks
import Benchmarks.Dss.Spot.Live
import Benchmarks.Dss.Spot.Par
import Benchmarks.Dss.Spot.Poke
import Benchmarks.Dss.Spot.Rely
import Benchmarks.Dss.Spot.Vat
import Benchmarks.Dss.Spot.Wards
import Solm.Equiv

/-!
# MakerDAO/Sky DSS Spotter benchmark correctness stub

The upstream Solidity source, optimized runtime bytecode, Solm AST spec, and Solm syntax companion
are present. The runtime-equivalence proof is intentionally left as the benchmark target. This file
also exposes the whole-contract wrapper that combines the constructor and runtime targets.
-/

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach Reasoning.Refinement

set_option maxRecDepth 2000000

namespace Benchmarks.Dss.Spot

theorem spotCorrect :
    runtimeEquivalence!?! config spotBytecode contract := by
  refine runtimeEquivalence!?!.intro ?_
  intro cA gh bl σ_evm σ_solm σ₀ g A I hcode hsize hperm hAccounts
  by_cases hwv : I.weiValue = ⟨0⟩
  · by_cases hcage : selIs I (spotSelBytes 0)
    · exact spotCageBodyCore hcode hsize hperm hwv hcage hAccounts
    · by_cases hdeny : selIs I (spotSelBytes 1)
      · exact spotDenyBodyCore hcode hsize hperm hwv hdeny hAccounts
      · by_cases hfileMat : selIs I (spotSelBytes 2)
        · exact spotFileMatBodyCore hcode hsize hperm hwv hfileMat hAccounts
        · by_cases hfilePar : selIs I (spotSelBytes 3)
          · exact spotFileParBodyCore hcode hsize hperm hwv hfilePar hAccounts
          · by_cases hfilePip : selIs I (spotSelBytes 4)
            · exact spotFilePipBodyCore hcode hsize hperm hwv hfilePip hAccounts
            · by_cases hilks : selIs I (spotSelBytes 5)
              · exact spotIlksBodyCore hcode hsize hperm hwv hilks hAccounts
              · by_cases hlive : selIs I (spotSelBytes 6)
                · exact spotLiveBodyCore hcode hsize hperm hwv hlive hAccounts
                · by_cases hpar : selIs I (spotSelBytes 7)
                  · exact spotParBodyCore hcode hsize hperm hwv hpar hAccounts
                  · by_cases hpoke : selIs I (spotSelBytes 8)
                    · exact spotPokeBodyCore hcode hsize hperm hwv hpoke hAccounts
                    · by_cases hrely : selIs I (spotSelBytes 9)
                      · exact spotRelyBodyCore hcode hsize hperm hwv hrely hAccounts
                      · by_cases hvat : selIs I (spotSelBytes 10)
                        · exact spotVatBodyCore hcode hsize hperm hwv hvat hAccounts
                        · by_cases hwards : selIs I (spotSelBytes 11)
                          · exact spotWardsBodyCore hcode hsize hperm hwv hwards hAccounts
                          · exact spotNoDispatch hcode hsize hperm hwv
                              (spotNoSelectorMatches hcage hdeny hfileMat hfilePar hfilePip
                                hilks hlive hpar hpoke hrely hvat hwards)
                              hAccounts
  · exact spotNonPayable hcode hwv

theorem spotContractCorrect :
    contractEquivalence config spotCreationBytecode spotBytecode contract :=
  contractEquivalence.intro spotConstructorCorrect spotCorrect

end Benchmarks.Dss.Spot
