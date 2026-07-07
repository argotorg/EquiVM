import Benchmarks.Dss.End.Constructor
import Benchmarks.Dss.End.Dispatch
import Solm.Equiv

/-!
# MakerDAO/Sky DSS End benchmark correctness stub

The upstream Solidity source, optimized runtime bytecode, Solm AST spec, and Solm syntax companion
are present. The runtime-equivalence proof is intentionally left as the benchmark target. This file
also exposes the whole-contract wrapper that combines the constructor and runtime targets.
-/

open Solm ABI Ethereum Ethereum.EVM
open Reasoning.Theory Reasoning.Reach Reasoning.Refinement

set_option maxRecDepth 2000000

namespace Benchmarks.Dss.End

theorem endCorrect :
    runtimeEquivalence!?! config endBytecode contract := by
  refine runtimeEquivalence!?!.intro ?_
  intro cA gh bl σ_evm σ_solm σ₀ g A I hcode hsize hperm hAccounts
  by_cases hwv : I.weiValue = ⟨0⟩
  · by_cases hwards : selIs I (endSelBytes 0)
    · exact endWardsBodyCore hcode hsize hperm hwv hwards hAccounts
    · by_cases hvat : selIs I (endSelBytes 1)
      · exact endVatBodyCore hcode hsize hperm hwv hvat hAccounts
      · by_cases hcat : selIs I (endSelBytes 2)
        · exact endCatBodyCore hcode hsize hperm hwv hcat hAccounts
        · by_cases hdog : selIs I (endSelBytes 3)
          · exact endDogBodyCore hcode hsize hperm hwv hdog hAccounts
          · by_cases hvow : selIs I (endSelBytes 4)
            · exact endVowBodyCore hcode hsize hperm hwv hvow hAccounts
            · by_cases hpot : selIs I (endSelBytes 5)
              · exact endPotBodyCore hcode hsize hperm hwv hpot hAccounts
              · by_cases hspot : selIs I (endSelBytes 6)
                · exact endSpotBodyCore hcode hsize hperm hwv hspot hAccounts
                · by_cases hcure : selIs I (endSelBytes 7)
                  · exact endCureBodyCore hcode hsize hperm hwv hcure hAccounts
                  · by_cases hlive : selIs I (endSelBytes 8)
                    · exact endLiveBodyCore hcode hsize hperm hwv hlive hAccounts
                    · by_cases hwhen : selIs I (endSelBytes 9)
                      · exact endWhenBodyCore hcode hsize hperm hwv hwhen hAccounts
                      · by_cases hwait : selIs I (endSelBytes 10)
                        · exact endWaitBodyCore hcode hsize hperm hwv hwait hAccounts
                        · by_cases hdebt : selIs I (endSelBytes 11)
                          · exact endDebtBodyCore hcode hsize hperm hwv hdebt hAccounts
                          · by_cases htag : selIs I (endSelBytes 12)
                            · exact endTagBodyCore hcode hsize hperm hwv htag hAccounts
                            · by_cases hgap : selIs I (endSelBytes 13)
                              · exact endGapBodyCore hcode hsize hperm hwv hgap hAccounts
                              · by_cases hArt : selIs I (endSelBytes 14)
                                · exact endArtBodyCore hcode hsize hperm hwv hArt hAccounts
                                · by_cases hfix : selIs I (endSelBytes 15)
                                  · exact endFixBodyCore hcode hsize hperm hwv hfix hAccounts
                                  · by_cases hbag : selIs I (endSelBytes 16)
                                    · exact endBagBodyCore hcode hsize hperm hwv hbag hAccounts
                                    · by_cases hout : selIs I (endSelBytes 17)
                                      · exact endOutBodyCore hcode hsize hperm hwv hout hAccounts
                                      · by_cases hrely : selIs I (endSelBytes 18)
                                        · exact endRelyBodyCore hcode hsize hperm hwv hrely hAccounts
                                        · by_cases hdeny : selIs I (endSelBytes 19)
                                          · exact endDenyBodyCore hcode hsize hperm hwv hdeny hAccounts
                                          · by_cases hfileAddress : selIs I (endSelBytes 20)
                                            · exact endFileAddressBodyCore hcode hsize hperm hwv
                                                hfileAddress hAccounts
                                            · by_cases hfileUint : selIs I (endSelBytes 21)
                                              · exact endFileUintBodyCore hcode hsize hperm hwv
                                                  hfileUint hAccounts
                                              · by_cases hcage : selIs I (endSelBytes 22)
                                                · exact endCageBodyCore hcode hsize hperm hwv hcage
                                                    hAccounts
                                                · by_cases hcageIlk : selIs I (endSelBytes 23)
                                                  · exact endCageIlkBodyCore hcode hsize hperm hwv
                                                      hcageIlk hAccounts
                                                  · by_cases hsnip : selIs I (endSelBytes 24)
                                                    · exact endSnipBodyCore hcode hsize hperm hwv
                                                        hsnip hAccounts
                                                    · by_cases hskip : selIs I (endSelBytes 25)
                                                      · exact endSkipBodyCore hcode hsize hperm hwv
                                                          hskip hAccounts
                                                      · by_cases hskim : selIs I (endSelBytes 26)
                                                        · exact endSkimBodyCore hcode hsize hperm
                                                            hwv hskim hAccounts
                                                        · by_cases hfree : selIs I (endSelBytes 27)
                                                          · exact endFreeBodyCore hcode hsize hperm
                                                              hwv hfree hAccounts
                                                          · by_cases hthaw : selIs I (endSelBytes 28)
                                                            · exact endThawBodyCore hcode hsize hperm
                                                                hwv hthaw hAccounts
                                                            · by_cases hflow :
                                                                selIs I (endSelBytes 29)
                                                              · exact endFlowBodyCore hcode hsize
                                                                  hperm hwv hflow hAccounts
                                                              · by_cases hpack :
                                                                  selIs I (endSelBytes 30)
                                                                · exact endPackBodyCore hcode
                                                                    hsize hperm hwv hpack
                                                                    hAccounts
                                                                · by_cases hcash :
                                                                    selIs I (endSelBytes 31)
                                                                  · exact endCashBodyCore hcode
                                                                      hsize hperm hwv hcash
                                                                      hAccounts
                                                                  · exact endNoDispatch hcode hsize
                                                                      hperm hwv
                                                                      (endNoSelectorMatches
                                                                        hwards hvat hcat hdog
                                                                        hvow hpot hspot hcure
                                                                        hlive hwhen hwait hdebt
                                                                        htag hgap hArt hfix
                                                                        hbag hout hrely hdeny
                                                                        hfileAddress hfileUint
                                                                        hcage hcageIlk hsnip
                                                                        hskip hskim hfree hthaw
                                                                        hflow hpack hcash)
                                                                      hAccounts
  · exact endNonPayable hcode hwv

theorem endContractCorrect :
    contractEquivalence config endCreationBytecode endBytecode contract :=
  contractEquivalence.intro endConstructorCorrect endCorrect

end Benchmarks.Dss.End
