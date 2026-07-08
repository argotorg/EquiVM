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

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach Reasoning.Refinement

namespace Benchmarks.Dss.Flopper

theorem flopperCorrect :
    runtimeEquivalence!?! config flopperBytecode contract := by
  refine runtimeEquivalence!?!.intro ?_
  intro cA gh bl σ_evm σ_solm σ₀ g A I hcode hsize hperm hAccounts
  by_cases hwv : I.weiValue = ⟨0⟩
  · by_cases hbeg : selIs I (flopperSelBytes 0)
    · exact flopperBegBody hcode hsize hperm hwv hbeg hAccounts
    · by_cases hbids : selIs I (flopperSelBytes 1)
      · exact flopperBidsBody hcode hsize hperm hwv hbids hAccounts
      · by_cases hcage : selIs I (flopperSelBytes 2)
        · exact flopperCageBodyCore hcode hsize hperm hwv hcage hAccounts
        · by_cases hdeal : selIs I (flopperSelBytes 3)
          · exact flopperDealBody hcode hsize hperm hwv hdeal hAccounts
          · by_cases hdent : selIs I (flopperSelBytes 4)
            · exact flopperDentBody hcode hsize hperm hwv hdent hAccounts
            · by_cases hdeny : selIs I (flopperSelBytes 5)
              · exact flopperDenyBody hcode hsize hperm hwv hdeny hAccounts
              · by_cases hfile : selIs I (flopperSelBytes 6)
                · exact flopperFileBodyCore hcode hsize hperm hwv hfile hAccounts
                · by_cases hgem : selIs I (flopperSelBytes 7)
                  · exact flopperGemBody hcode hsize hperm hwv hgem hAccounts
                  · by_cases hkick : selIs I (flopperSelBytes 8)
                    · exact flopperKickBody hcode hsize hperm hwv hkick hAccounts
                    · by_cases hkicks : selIs I (flopperSelBytes 9)
                      · exact flopperKicksBody hcode hsize hperm hwv hkicks hAccounts
                      · by_cases hlive : selIs I (flopperSelBytes 10)
                        · exact flopperLiveBody hcode hsize hperm hwv hlive hAccounts
                        · by_cases hpad : selIs I (flopperSelBytes 11)
                          · exact flopperPadBody hcode hsize hperm hwv hpad hAccounts
                          · by_cases hrely : selIs I (flopperSelBytes 12)
                            · exact flopperRelyBody hcode hsize hperm hwv hrely hAccounts
                            · by_cases htau : selIs I (flopperSelBytes 13)
                              · exact flopperTauBody hcode hsize hperm hwv htau hAccounts
                              · by_cases htick : selIs I (flopperSelBytes 14)
                                · exact flopperTickBody hcode hsize hperm hwv htick hAccounts
                                · by_cases httl : selIs I (flopperSelBytes 15)
                                  · exact flopperTtlBody hcode hsize hperm hwv httl hAccounts
                                  · by_cases hvat : selIs I (flopperSelBytes 16)
                                    · exact flopperVatBody hcode hsize hperm hwv hvat hAccounts
                                    · by_cases hvow : selIs I (flopperSelBytes 17)
                                      · exact flopperVowBody hcode hsize hperm hwv hvow hAccounts
                                      · by_cases hwards : selIs I (flopperSelBytes 18)
                                        · exact flopperWardsBody hcode hsize hperm hwv hwards
                                            hAccounts
                                        · by_cases hyank : selIs I (flopperSelBytes 19)
                                          · exact flopperYankBody hcode hsize hperm hwv hyank
                                              hAccounts
                                          · exact flopperNoDispatch hcode hsize hperm hwv
                                              (flopperNoSelectorMatches hbeg hbids hcage hdeal
                                                hdent hdeny hfile hgem hkick hkicks hlive hpad hrely
                                                htau htick httl hvat hvow hwards hyank)
                                              hAccounts
  · exact flopperNonPayable hcode hwv

theorem flopperContractCorrect :
    contractEquivalence config flopperCreationBytecode flopperBytecode contract :=
  contractEquivalence.intro flopperConstructorCorrect flopperCorrect

end Benchmarks.Dss.Flopper
