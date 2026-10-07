import Benchmarks.Dss.Flopper.Constructor
import Benchmarks.Dss.Flopper.Beg
import Benchmarks.Dss.Flopper.Bids
import Benchmarks.Dss.Flopper.Cage
import Benchmarks.Dss.Flopper.DealRuntime
import Benchmarks.Dss.Flopper.Dent
import Benchmarks.Dss.Flopper.Deny
import Benchmarks.Dss.Flopper.File
import Benchmarks.Dss.Flopper.Gem
import Benchmarks.Dss.Flopper.Kick
import Benchmarks.Dss.Flopper.Kicks
import Benchmarks.Dss.Flopper.Live
import Benchmarks.Dss.Flopper.Pad
import Benchmarks.Dss.Flopper.Rely
import Benchmarks.Dss.Flopper.Tau
import Benchmarks.Dss.Flopper.Tick
import Benchmarks.Dss.Flopper.Ttl
import Benchmarks.Dss.Flopper.Vat
import Benchmarks.Dss.Flopper.Vow
import Benchmarks.Dss.Flopper.Wards
import Benchmarks.Dss.Flopper.Yank
import Solm.Equiv

/-!
# MakerDAO/Sky DSS Flopper benchmark correctness stub

The upstream Solidity source, optimized runtime bytecode, Solm AST spec, and Solm syntax companion
are present. The runtime-equivalence proof is intentionally left as the benchmark target. This file
also exposes the whole-contract wrapper that combines the constructor and runtime targets.
-/

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Dss.Flopper

theorem flopperCorrect :
    runtimeEquivalenceAnyPerm config flopperBytecode contract := by
  refine runtimeEquivalenceAnyPerm.intro ?_
  intro σ σ₀ g A I hcode hsize
  by_cases hwv : I.weiValue = ⟨0⟩
  · by_cases hbeg : selIs I (flopperSelBytes 0)
    · exact flopperBegBody hcode hsize hwv hbeg
    · by_cases hbids : selIs I (flopperSelBytes 1)
      · exact flopperBidsBody hcode hsize hwv hbids
      · by_cases hcage : selIs I (flopperSelBytes 2)
        · exact flopperCageBodyCore hcode hsize hwv hcage
        · by_cases hdeal : selIs I (flopperSelBytes 3)
          · exact flopperDealBody hcode hsize hwv hdeal
          · by_cases hdent : selIs I (flopperSelBytes 4)
            · exact flopperDentBody hcode hsize hwv hdent
            · by_cases hdeny : selIs I (flopperSelBytes 5)
              · exact flopperDenyBody hcode hsize hwv hdeny
              · by_cases hfile : selIs I (flopperSelBytes 6)
                · exact flopperFileBodyCore hcode hsize hwv hfile
                · by_cases hgem : selIs I (flopperSelBytes 7)
                  · exact flopperGemBody hcode hsize hwv hgem
                  · by_cases hkick : selIs I (flopperSelBytes 8)
                    · exact flopperKickBody hcode hsize hwv hkick
                    · by_cases hkicks : selIs I (flopperSelBytes 9)
                      · exact flopperKicksBody hcode hsize hwv hkicks
                      · by_cases hlive : selIs I (flopperSelBytes 10)
                        · exact flopperLiveBody hcode hsize hwv hlive
                        · by_cases hpad : selIs I (flopperSelBytes 11)
                          · exact flopperPadBody hcode hsize hwv hpad
                          · by_cases hrely : selIs I (flopperSelBytes 12)
                            · exact flopperRelyBody hcode hsize hwv hrely
                            · by_cases htau : selIs I (flopperSelBytes 13)
                              · exact flopperTauBody hcode hsize hwv htau
                              · by_cases htick : selIs I (flopperSelBytes 14)
                                · exact flopperTickBody hcode hsize hwv htick
                                · by_cases httl : selIs I (flopperSelBytes 15)
                                  · exact flopperTtlBody hcode hsize hwv httl
                                  · by_cases hvat : selIs I (flopperSelBytes 16)
                                    · exact flopperVatBody hcode hsize hwv hvat
                                    · by_cases hvow : selIs I (flopperSelBytes 17)
                                      · exact flopperVowBody hcode hsize hwv hvow
                                      · by_cases hwards : selIs I (flopperSelBytes 18)
                                        · exact flopperWardsBody hcode hsize hwv hwards
                                        · by_cases hyank : selIs I (flopperSelBytes 19)
                                          · exact flopperYankBody hcode hsize hwv hyank
                                          · exact flopperNoDispatch hcode hsize hwv
                                              (flopperNoSelectorMatches hbeg hbids hcage hdeal
                                                hdent hdeny hfile hgem hkick hkicks hlive hpad hrely
                                                htau htick httl hvat hvow hwards hyank)
  · exact flopperNonPayable hcode hwv

theorem flopperContractCorrect :
    contractEquivalenceAnyPerm config flopperCreationBytecode flopperBytecode contract :=
  contractEquivalenceAnyPerm.intro flopperConstructorCorrect flopperCorrect

end Benchmarks.Dss.Flopper
