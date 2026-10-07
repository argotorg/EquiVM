import Benchmarks.Dss.End.Constructor
import Benchmarks.Dss.End.Wards
import Benchmarks.Dss.End.Vat
import Benchmarks.Dss.End.Cat
import Benchmarks.Dss.End.Dog
import Benchmarks.Dss.End.Vow
import Benchmarks.Dss.End.Pot
import Benchmarks.Dss.End.Spot
import Benchmarks.Dss.End.Cure
import Benchmarks.Dss.End.Live
import Benchmarks.Dss.End.When
import Benchmarks.Dss.End.Wait
import Benchmarks.Dss.End.Debt
import Benchmarks.Dss.End.Tag
import Benchmarks.Dss.End.Gap
import Benchmarks.Dss.End.Art
import Benchmarks.Dss.End.Fix
import Benchmarks.Dss.End.Bag
import Benchmarks.Dss.End.Out
import Benchmarks.Dss.End.Rely
import Benchmarks.Dss.End.Deny
import Benchmarks.Dss.End.FileAddress
import Benchmarks.Dss.End.FileUint
import Benchmarks.Dss.End.Cage
import Benchmarks.Dss.End.CageIlk
import Benchmarks.Dss.End.Snip
import Benchmarks.Dss.End.Skip
import Benchmarks.Dss.End.Skim
import Benchmarks.Dss.End.Free
import Benchmarks.Dss.End.Thaw
import Benchmarks.Dss.End.Flow
import Benchmarks.Dss.End.Pack
import Benchmarks.Dss.End.Cash
import Solm.Refine

/-!
# MakerDAO/Sky DSS End benchmark correctness
-/

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Dss.End

theorem endCorrect :
    runtimeRefinement config endBytecode contract := by
  refine runtimeRefinement.intro ?_
  intro σ σ₀ g A I hcode hsize
  by_cases hwv : I.weiValue = ⟨0⟩
  · by_cases hwards : selIs I (selectorOf wardsTransition)
    · exact endWardsBody hcode hsize hwv hwards
    · by_cases hvat : selIs I (selectorOf vatTransition)
      · exact endVatBody hcode hsize hwv hvat
      · by_cases hcat : selIs I (selectorOf catTransition)
        · exact endCatBody hcode hsize hwv hcat
        · by_cases hdog : selIs I (selectorOf dogTransition)
          · exact endDogBody hcode hsize hwv hdog
          · by_cases hvow : selIs I (selectorOf vowTransition)
            · exact endVowBody hcode hsize hwv hvow
            · by_cases hpot : selIs I (selectorOf potTransition)
              · exact endPotBody hcode hsize hwv hpot
              · by_cases hspot : selIs I (selectorOf spotTransition)
                · exact endSpotBody hcode hsize hwv hspot
                · by_cases hcure : selIs I (selectorOf cureTransition)
                  · exact endCureBody hcode hsize hwv hcure
                  · by_cases hlive : selIs I (selectorOf liveTransition)
                    · exact endLiveBody hcode hsize hwv hlive
                    · by_cases hwhen : selIs I (selectorOf whenTransition)
                      · exact endWhenBody hcode hsize hwv hwhen
                      · by_cases hwait : selIs I (selectorOf waitTransition)
                        · exact endWaitBody hcode hsize hwv hwait
                        · by_cases hdebt : selIs I (selectorOf debtTransition)
                          · exact endDebtBody hcode hsize hwv hdebt
                          · by_cases htag : selIs I (selectorOf tagTransition)
                            · exact endTagBody hcode hsize hwv htag
                            · by_cases hgap : selIs I (selectorOf gapTransition)
                              · exact endGapBody hcode hsize hwv hgap
                              · by_cases hArt : selIs I (selectorOf ArtTransition)
                                · exact endArtBody hcode hsize hwv hArt
                                · by_cases hfix : selIs I (selectorOf fixTransition)
                                  · exact endFixBody hcode hsize hwv hfix
                                  · by_cases hbag : selIs I (selectorOf bagTransition)
                                    · exact endBagBody hcode hsize hwv hbag
                                    · by_cases hout : selIs I (selectorOf outTransition)
                                      · exact endOutBody hcode hsize hwv hout
                                      · by_cases hrely : selIs I (selectorOf relyTransition)
                                        · exact endRelyBody hcode hsize hwv hrely
                                        · by_cases hdeny : selIs I (selectorOf denyTransition)
                                          · exact endDenyBody hcode hsize hwv hdeny
                                          · by_cases hfileAddress :
                                                selIs I (selectorOf fileAddressTransition)
                                            · exact endFileAddressBody hcode hsize hwv
                                                hfileAddress
                                            · by_cases hfileUint :
                                                  selIs I (selectorOf fileUintTransition)
                                              · exact endFileUintBody hcode hsize hwv
                                                  hfileUint
                                              · by_cases hcage : selIs I (selectorOf cageTransition)
                                                · exact endCageBody hcode hsize hwv
                                                    hcage
                                                · by_cases hcageIlk :
                                                      selIs I (selectorOf cageIlkTransition)
                                                  · exact endCageIlkBody hcode hsize hwv
                                                      hcageIlk
                                                  · by_cases hsnip :
                                                        selIs I (selectorOf snipTransition)
                                                    · exact endSnipBody hcode hsize hwv
                                                        hsnip
                                                    · by_cases hskip :
                                                          selIs I (selectorOf skipTransition)
                                                      · exact endSkipBody hcode hsize hwv
                                                          hskip
                                                      · by_cases hskim :
                                                            selIs I (selectorOf skimTransition)
                                                        · exact endSkimBody hcode hsize hwv
                                                            hskim
                                                        · by_cases hfree :
                                                              selIs I (selectorOf freeTransition)
                                                          · exact endFreeBody hcode hsize hwv
                                                              hfree
                                                          · by_cases hthaw :
                                                                selIs I (selectorOf thawTransition)
                                                            · exact endThawBody hcode hsize hwv
                                                                hthaw
                                                            · by_cases hflow :
                                                                  selIs I (selectorOf flowTransition)
                                                              · exact endFlowBody hcode hsize hwv
                                                                  hflow
                                                              · by_cases hpack :
                                                                    selIs I (selectorOf packTransition)
                                                                · exact endPackBody hcode hsize hwv
                                                                    hpack
                                                                · by_cases hcash :
                                                                      selIs I (selectorOf cashTransition)
                                                                  · exact endCashBody hcode hsize
                                                                      hwv hcash
                                                                  · exact endNoDispatch hcode hsize
                                                                      hwv hwards hvat hcat hdog hvow
                                                                      hpot hspot hcure hlive hwhen hwait
                                                                      hdebt htag hgap hArt hfix hbag
                                                                      hout hrely hdeny hfileAddress
                                                                      hfileUint hcage hcageIlk hsnip
                                                                      hskip hskim hfree hthaw hflow
                                                                      hpack hcash
  · exact endNonPayable hcode hwv

theorem endContractCorrect :
    contractRefinement config endCreationBytecode contract :=
  contractRefinement.of_constant endConstructorCorrect endCorrect

end Benchmarks.Dss.End
