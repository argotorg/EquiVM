import Benchmarks.Dss.Flapper.Constructor
import Benchmarks.Dss.Flapper.Beg
import Benchmarks.Dss.Flapper.Bids
import Benchmarks.Dss.Flapper.Cage
import Benchmarks.Dss.Flapper.Deal
import Benchmarks.Dss.Flapper.Deny
import Benchmarks.Dss.Flapper.File
import Benchmarks.Dss.Flapper.Fill
import Benchmarks.Dss.Flapper.Gem
import Benchmarks.Dss.Flapper.Kick
import Benchmarks.Dss.Flapper.Kicks
import Benchmarks.Dss.Flapper.Lid
import Benchmarks.Dss.Flapper.Live
import Benchmarks.Dss.Flapper.Rely
import Benchmarks.Dss.Flapper.Tau
import Benchmarks.Dss.Flapper.Tend
import Benchmarks.Dss.Flapper.Tick
import Benchmarks.Dss.Flapper.Ttl
import Benchmarks.Dss.Flapper.Vat
import Benchmarks.Dss.Flapper.Wards
import Benchmarks.Dss.Flapper.Yank
import Solm.Equiv

/-!
# MakerDAO/Sky DSS Flapper benchmark correctness stub

The upstream Solidity source, optimized runtime bytecode, Solm AST spec, and Solm syntax companion
are present. The runtime-equivalence proof is intentionally left as the benchmark target. This file
also exposes the whole-contract wrapper that combines the constructor and runtime targets.
-/

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Dss.Flapper

theorem flapperCorrect :
    runtimeEquivalenceAnyPerm config flapperBytecode contract := by
  refine runtimeEquivalenceAnyPerm.intro ?_
  intro σ σ₀ g A I hcode hsize
  by_cases hwv : I.weiValue = ⟨0⟩
  · by_cases hbeg : selIs I (flapperSelBytes 0)
    · exact flapperBegBodyCore hcode hsize hwv hbeg
    · by_cases hbids : selIs I (flapperSelBytes 1)
      · exact flapperBidsBodyCore hcode hsize hwv hbids
      · by_cases hcage : selIs I (flapperSelBytes 2)
        · exact flapperCageBodyCore hcode hsize hwv hcage
        · by_cases hdeal : selIs I (flapperSelBytes 3)
          · exact flapperDealBodyCore hcode hsize hwv hdeal
          · by_cases hdeny : selIs I (flapperSelBytes 4)
            · exact flapperDenyBodyCore hcode hsize hwv hdeny
            · by_cases hfile : selIs I (flapperSelBytes 5)
              · exact flapperFileBodyCore hcode hsize hwv hfile
              · by_cases hfill : selIs I (flapperSelBytes 6)
                · exact flapperFillBodyCore hcode hsize hwv hfill
                · by_cases hgem : selIs I (flapperSelBytes 7)
                  · exact flapperGemBodyCore hcode hsize hwv hgem
                  · by_cases hkick : selIs I (flapperSelBytes 8)
                    · exact flapperKickBodyCore hcode hsize hwv hkick
                    · by_cases hkicks : selIs I (flapperSelBytes 9)
                      · exact flapperKicksBodyCore hcode hsize hwv hkicks
                      · by_cases hlid : selIs I (flapperSelBytes 10)
                        · exact flapperLidBodyCore hcode hsize hwv hlid
                        · by_cases hlive : selIs I (flapperSelBytes 11)
                          · exact flapperLiveBodyCore hcode hsize hwv hlive
                          · by_cases hrely : selIs I (flapperSelBytes 12)
                            · exact flapperRelyBodyCore hcode hsize hwv hrely
                            · by_cases htau : selIs I (flapperSelBytes 13)
                              · exact flapperTauBodyCore hcode hsize hwv htau
                              · by_cases htend : selIs I (flapperSelBytes 14)
                                · exact flapperTendBodyCore hcode hsize hwv htend
                                · by_cases htick : selIs I (flapperSelBytes 15)
                                  · exact flapperTickBodyCore hcode hsize hwv htick

                                  · by_cases httl : selIs I (flapperSelBytes 16)
                                    · exact flapperTtlBodyCore hcode hsize hwv httl

                                    · by_cases hvat : selIs I (flapperSelBytes 17)
                                      · exact flapperVatBodyCore hcode hsize hwv hvat

                                      · by_cases hwards : selIs I (flapperSelBytes 18)
                                        · exact flapperWardsBodyCore hcode hsize hwv
                                            hwards
                                        · by_cases hyank : selIs I (flapperSelBytes 19)
                                          · exact flapperYankBodyCore hcode hsize hwv
                                              hyank
                                          · exact flapperNoDispatch hcode hsize hwv
                                              (flapperNoSelectorMatches hbeg hbids hcage hdeal
                                                hdeny hfile hfill hgem hkick hkicks hlid hlive
                                                hrely htau htend htick httl hvat hwards hyank)
  · exact flapperNonPayable hcode hwv

theorem flapperContractCorrect :
    contractEquivalenceAnyPerm config flapperCreationBytecode flapperBytecode contract :=
  contractEquivalenceAnyPerm.intro flapperConstructorCorrect flapperCorrect

end Benchmarks.Dss.Flapper
