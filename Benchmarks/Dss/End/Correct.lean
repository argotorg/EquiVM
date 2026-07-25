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
import Solm.Equiv

/-!
# MakerDAO/Sky DSS End benchmark correctness
-/

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach Reasoning.Refinement

namespace Benchmarks.Dss.End

theorem endCorrect :
    runtimeEquivalence config endBytecode contract := by
  refine runtimeEquivalence.intro ?_
  intro cA gh bl σ_evm σ_solm σ₀ g A I hcode hsize hperm hAccounts
  by_cases hwv : I.weiValue = ⟨0⟩
  · by_cases hwards : selIs I (selectorOf wardsTransition)
    · exact endWardsBody hcode hsize hperm hwv hwards hAccounts
    · by_cases hvat : selIs I (selectorOf vatTransition)
      · exact endVatBody hcode hsize hperm hwv hvat hAccounts
      · by_cases hcat : selIs I (selectorOf catTransition)
        · exact endCatBody hcode hsize hperm hwv hcat hAccounts
        · by_cases hdog : selIs I (selectorOf dogTransition)
          · exact endDogBody hcode hsize hperm hwv hdog hAccounts
          · by_cases hvow : selIs I (selectorOf vowTransition)
            · exact endVowBody hcode hsize hperm hwv hvow hAccounts
            · by_cases hpot : selIs I (selectorOf potTransition)
              · exact endPotBody hcode hsize hperm hwv hpot hAccounts
              · by_cases hspot : selIs I (selectorOf spotTransition)
                · exact endSpotBody hcode hsize hperm hwv hspot hAccounts
                · by_cases hcure : selIs I (selectorOf cureTransition)
                  · exact endCureBody hcode hsize hperm hwv hcure hAccounts
                  · by_cases hlive : selIs I (selectorOf liveTransition)
                    · exact endLiveBody hcode hsize hperm hwv hlive hAccounts
                    · by_cases hwhen : selIs I (selectorOf whenTransition)
                      · exact endWhenBody hcode hsize hperm hwv hwhen hAccounts
                      · by_cases hwait : selIs I (selectorOf waitTransition)
                        · exact endWaitBody hcode hsize hperm hwv hwait hAccounts
                        · by_cases hdebt : selIs I (selectorOf debtTransition)
                          · exact endDebtBody hcode hsize hperm hwv hdebt hAccounts
                          · by_cases htag : selIs I (selectorOf tagTransition)
                            · exact endTagBody hcode hsize hperm hwv htag hAccounts
                            · by_cases hgap : selIs I (selectorOf gapTransition)
                              · exact endGapBody hcode hsize hperm hwv hgap hAccounts
                              · by_cases hArt : selIs I (selectorOf ArtTransition)
                                · exact endArtBody hcode hsize hperm hwv hArt hAccounts
                                · by_cases hfix : selIs I (selectorOf fixTransition)
                                  · exact endFixBody hcode hsize hperm hwv hfix hAccounts
                                  · by_cases hbag : selIs I (selectorOf bagTransition)
                                    · exact endBagBody hcode hsize hperm hwv hbag hAccounts
                                    · by_cases hout : selIs I (selectorOf outTransition)
                                      · exact endOutBody hcode hsize hperm hwv hout hAccounts
                                      · by_cases hrely : selIs I (selectorOf relyTransition)
                                        · exact endRelyBody hcode hsize hperm hwv hrely hAccounts
                                        · by_cases hdeny : selIs I (selectorOf denyTransition)
                                          · exact endDenyBody hcode hsize hperm hwv hdeny hAccounts
                                          · by_cases hfileAddress :
                                                selIs I (selectorOf fileAddressTransition)
                                            · exact endFileAddressBody hcode hsize hperm hwv
                                                hfileAddress hAccounts
                                            · by_cases hfileUint :
                                                  selIs I (selectorOf fileUintTransition)
                                              · exact endFileUintBody hcode hsize hperm hwv
                                                  hfileUint hAccounts
                                              · by_cases hcage : selIs I (selectorOf cageTransition)
                                                · exact endCageBody hcode hsize hperm hwv
                                                    hcage hAccounts
                                                · by_cases hcageIlk :
                                                      selIs I (selectorOf cageIlkTransition)
                                                  · exact endCageIlkBody hcode hsize hperm hwv
                                                      hcageIlk hAccounts
                                                  · by_cases hsnip :
                                                        selIs I (selectorOf snipTransition)
                                                    · exact endSnipBody hcode hsize hperm hwv
                                                        hsnip hAccounts
                                                    · by_cases hskip :
                                                          selIs I (selectorOf skipTransition)
                                                      · exact endSkipBody hcode hsize hperm hwv
                                                          hskip hAccounts
                                                      · by_cases hskim :
                                                            selIs I (selectorOf skimTransition)
                                                        · exact endSkimBody hcode hsize hperm hwv
                                                            hskim hAccounts
                                                        · by_cases hfree :
                                                              selIs I (selectorOf freeTransition)
                                                          · exact endFreeBody hcode hsize hperm hwv
                                                              hfree hAccounts
                                                          · by_cases hthaw :
                                                                selIs I (selectorOf thawTransition)
                                                            · exact endThawBody hcode hsize hperm hwv
                                                                hthaw hAccounts
                                                            · by_cases hflow :
                                                                  selIs I (selectorOf flowTransition)
                                                              · exact endFlowBody hcode hsize hperm hwv
                                                                  hflow hAccounts
                                                              · by_cases hpack :
                                                                    selIs I (selectorOf packTransition)
                                                                · exact endPackBody hcode hsize hperm hwv
                                                                    hpack hAccounts
                                                                · by_cases hcash :
                                                                      selIs I (selectorOf cashTransition)
                                                                  · exact endCashBody hcode hsize hperm
                                                                      hwv hcash hAccounts
                                                                  · exact endNoDispatch hcode hsize hperm
                                                                      hwv hwards hvat hcat hdog hvow
                                                                      hpot hspot hcure hlive hwhen hwait
                                                                      hdebt htag hgap hArt hfix hbag
                                                                      hout hrely hdeny hfileAddress
                                                                      hfileUint hcage hcageIlk hsnip
                                                                      hskip hskim hfree hthaw hflow
                                                                      hpack hcash hAccounts
  · exact endNonPayable hcode hwv

theorem endContractCorrect :
    contractEquivalence config endCreationBytecode endBytecode contract :=
  contractEquivalence.intro endConstructorCorrect endCorrect

end Benchmarks.Dss.End
