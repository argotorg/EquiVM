import Benchmarks.Dss.Cure.Constructor
import Benchmarks.Dss.Cure.Amt
import Benchmarks.Dss.Cure.Cage
import Benchmarks.Dss.Cure.Deny
import Benchmarks.Dss.Cure.Drop
import Benchmarks.Dss.Cure.File
import Benchmarks.Dss.Cure.LCount
import Benchmarks.Dss.Cure.Lift
import Benchmarks.Dss.Cure.List
import Benchmarks.Dss.Cure.Live
import Benchmarks.Dss.Cure.Load
import Benchmarks.Dss.Cure.Loaded
import Benchmarks.Dss.Cure.Pos
import Benchmarks.Dss.Cure.Rely
import Benchmarks.Dss.Cure.Say
import Benchmarks.Dss.Cure.Srcs
import Benchmarks.Dss.Cure.TCount
import Benchmarks.Dss.Cure.Tell
import Benchmarks.Dss.Cure.Wait
import Benchmarks.Dss.Cure.Wards
import Benchmarks.Dss.Cure.When
import Solm.Refine

/-!
# MakerDAO/Sky DSS Cure benchmark correctness scaffold

The runtime proof now follows the phase-1 shape: this file is a thin selector router, and each ABI
function has a separate `...BodyCore` proof obligation in its own file.
-/

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

set_option maxRecDepth 2000000

namespace Benchmarks.Dss.Cure

theorem cureCorrect :
    runtimeRefinementWithWF cureStorageWF config cureBytecode contract := by
  refine runtimeRefinementWithWF.intro ?_
  intro σ σ₀ g A I hcode hsize hperm hStorageWF
  by_cases hwv : I.weiValue = ⟨0⟩
  · by_cases hamt : selIs I (cureSelBytes 0)
    · exact cureAmtBodyCore hcode hsize hperm hwv hamt
    · by_cases hcage : selIs I (cureSelBytes 1)
      · exact cureCageBodyCore hcode hsize hperm hwv hcage
      · by_cases hdeny : selIs I (cureSelBytes 2)
        · exact cureDenyBodyCore hcode hsize hperm hwv hdeny
        · by_cases hdrop : selIs I (cureSelBytes 3)
          · exact cureDropBodyCore hcode hsize hperm hwv hdrop hStorageWF
          · by_cases hfile : selIs I (cureSelBytes 4)
            · exact cureFileBodyCore hcode hsize hperm hwv hfile
            · by_cases hlCount : selIs I (cureSelBytes 5)
              · exact cureLCountBodyCore hcode hsize hperm hwv hlCount
              · by_cases hlift : selIs I (cureSelBytes 6)
                · exact cureLiftBodyCore hcode hsize hperm hwv hlift
                · by_cases hlist : selIs I (cureSelBytes 7)
                  · exact cureListBodyCore hcode hsize hperm hwv hlist hStorageWF
                  · by_cases hlive : selIs I (cureSelBytes 8)
                    · exact cureLiveBodyCore hcode hsize hperm hwv hlive
                    · by_cases hload : selIs I (cureSelBytes 9)
                      · exact cureLoadBodyCore hcode hsize hperm hwv hload
                      · by_cases hloaded : selIs I (cureSelBytes 10)
                        · exact cureLoadedBodyCore hcode hsize hperm hwv hloaded
                        · by_cases hpos : selIs I (cureSelBytes 11)
                          · exact curePosBodyCore hcode hsize hperm hwv hpos
                          · by_cases hrely : selIs I (cureSelBytes 12)
                            · exact cureRelyBodyCore hcode hsize hperm hwv hrely
                            · by_cases hsay : selIs I (cureSelBytes 13)
                              · exact cureSayBodyCore hcode hsize hperm hwv hsay
                              · by_cases hsrcs : selIs I (cureSelBytes 14)
                                · exact cureSrcsBodyCore hcode hsize hperm hwv hsrcs
                                · by_cases htCount : selIs I (cureSelBytes 15)
                                  · exact cureTCountBodyCore hcode hsize hperm hwv htCount
                                  · by_cases htell : selIs I (cureSelBytes 16)
                                    · exact cureTellBodyCore hcode hsize hperm hwv htell
                                    · by_cases hwait : selIs I (cureSelBytes 17)
                                      · exact cureWaitBodyCore hcode hsize hperm hwv hwait
                                      · by_cases hwards : selIs I (cureSelBytes 18)
                                        · exact cureWardsBodyCore hcode hsize hperm hwv hwards
                                        · by_cases hwhen : selIs I (cureSelBytes 19)
                                          · exact cureWhenBodyCore hcode hsize hperm hwv hwhen
                                          · exact cureNoDispatch hcode hsize hperm hwv
                                              (cureNoSelectorMatches hamt hcage hdeny hdrop hfile
                                                hlCount hlift hlist hlive hload hloaded hpos hrely
                                                hsay hsrcs htCount htell hwait hwards hwhen)

  · exact cureNonPayable hcode hwv

theorem cureContractCorrect :
    contractRefinementWF cureStorageWF config cureCreationBytecode contract :=
  contractRefinementWF.of_constant cureConstructorCorrect cureCorrect

end Benchmarks.Dss.Cure
