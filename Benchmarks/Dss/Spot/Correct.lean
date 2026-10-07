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

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

set_option maxRecDepth 2000000

namespace Benchmarks.Dss.Spot

theorem spotCorrect :
    runtimeEquivalence config spotBytecode contract := by
  refine runtimeEquivalence.intro ?_
  intro σ σ₀ g A I hcode hsize
  by_cases hwv : I.weiValue = ⟨0⟩
  · by_cases hcage : selIs I (spotSelBytes 0)
    · exact spotCageBodyCoreAnyPerm hcode hsize hwv hcage
    · by_cases hdeny : selIs I (spotSelBytes 1)
      · exact spotDenyBodyCoreAnyPerm hcode hsize hwv hdeny
      · by_cases hfileMat : selIs I (spotSelBytes 2)
        · exact spotFileMatBodyCore hcode hsize hwv hfileMat
        · by_cases hfilePar : selIs I (spotSelBytes 3)
          · exact spotFileParBodyCore hcode hsize hwv hfilePar
          · by_cases hfilePip : selIs I (spotSelBytes 4)
            · exact spotFilePipBodyCore hcode hsize hwv hfilePip
            · by_cases hilks : selIs I (spotSelBytes 5)
              · exact spotIlksBodyCore hcode hsize hwv hilks
              · by_cases hlive : selIs I (spotSelBytes 6)
                · exact spotLiveBodyCore hcode hsize hwv hlive
                · by_cases hpar : selIs I (spotSelBytes 7)
                  · exact spotParBodyCore hcode hsize hwv hpar
                  · by_cases hpoke : selIs I (spotSelBytes 8)
                    · exact spotPokeBodyCore hcode hsize hwv hpoke
                    · by_cases hrely : selIs I (spotSelBytes 9)
                      · exact spotRelyBodyCoreAnyPerm hcode hsize hwv hrely
                      · by_cases hvat : selIs I (spotSelBytes 10)
                        · exact spotVatBodyCore hcode hsize hwv hvat
                        · by_cases hwards : selIs I (spotSelBytes 11)
                          · exact spotWardsBodyCore hcode hsize hwv hwards
                          · exact spotNoDispatch hcode hsize hwv
                              (spotNoSelectorMatches hcage hdeny hfileMat hfilePar hfilePip
                                hilks hlive hpar hpoke hrely hvat hwards)
  · exact spotNonPayable hcode hwv

theorem spotContractCorrect :
    contractEquivalence config spotCreationBytecode spotBytecode contract :=
  contractEquivalence.intro spotConstructorCorrect spotCorrect

end Benchmarks.Dss.Spot
