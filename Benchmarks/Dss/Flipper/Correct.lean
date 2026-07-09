import Benchmarks.Dss.Flipper.Constructor
import Benchmarks.Dss.Flipper.Beg
import Benchmarks.Dss.Flipper.Bids
import Benchmarks.Dss.Flipper.Cat
import Benchmarks.Dss.Flipper.Deal
import Benchmarks.Dss.Flipper.DentBody
import Benchmarks.Dss.Flipper.Deny
import Benchmarks.Dss.Flipper.FileAddress
import Benchmarks.Dss.Flipper.FileUint
import Benchmarks.Dss.Flipper.Ilk
import Benchmarks.Dss.Flipper.KickBody
import Benchmarks.Dss.Flipper.Kicks
import Benchmarks.Dss.Flipper.Rely
import Benchmarks.Dss.Flipper.Tau
import Benchmarks.Dss.Flipper.TendBody
import Benchmarks.Dss.Flipper.Tick
import Benchmarks.Dss.Flipper.Ttl
import Benchmarks.Dss.Flipper.Vat
import Benchmarks.Dss.Flipper.Wards
import Benchmarks.Dss.Flipper.YankBody
import Solm.Equiv

/-!
# MakerDAO/Sky DSS Flipper benchmark correctness stub

The upstream Solidity source, optimized runtime bytecode, Solm AST spec, and Solm syntax companion
are present. The runtime-equivalence proof is intentionally left as the benchmark target. This file
also exposes the whole-contract wrapper that combines the constructor and runtime targets.
-/

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach Reasoning.Refinement

set_option maxRecDepth 2000000

namespace Benchmarks.Dss.Flipper

theorem flipperNoSelectorMatches {I : ExecutionEnv}
    (hbeg : ¬ selIs I (flipperSelBytes 0))
    (hbids : ¬ selIs I (flipperSelBytes 1))
    (hcat : ¬ selIs I (flipperSelBytes 2))
    (hdeal : ¬ selIs I (flipperSelBytes 3))
    (hdent : ¬ selIs I (flipperSelBytes 4))
    (hdeny : ¬ selIs I (flipperSelBytes 5))
    (hfileAddress : ¬ selIs I (flipperSelBytes 6))
    (hfileUint : ¬ selIs I (flipperSelBytes 7))
    (hilk : ¬ selIs I (flipperSelBytes 8))
    (hkick : ¬ selIs I (flipperSelBytes 9))
    (hkicks : ¬ selIs I (flipperSelBytes 10))
    (hrely : ¬ selIs I (flipperSelBytes 11))
    (htau : ¬ selIs I (flipperSelBytes 12))
    (htend : ¬ selIs I (flipperSelBytes 13))
    (htick : ¬ selIs I (flipperSelBytes 14))
    (httl : ¬ selIs I (flipperSelBytes 15))
    (hvat : ¬ selIs I (flipperSelBytes 16))
    (hwards : ¬ selIs I (flipperSelBytes 17))
    (hyank : ¬ selIs I (flipperSelBytes 18)) :
    ∀ i, i < 19 → (flipperSelBytes i == I.calldata.extract 0 4) = false := by
  intro i hi
  interval_cases i
  · simpa [selIs, flipperSelBytes] using hbeg
  · simpa [selIs, flipperSelBytes] using hbids
  · simpa [selIs, flipperSelBytes] using hcat
  · simpa [selIs, flipperSelBytes] using hdeal
  · simpa [selIs, flipperSelBytes] using hdent
  · simpa [selIs, flipperSelBytes] using hdeny
  · simpa [selIs, flipperSelBytes] using hfileAddress
  · simpa [selIs, flipperSelBytes] using hfileUint
  · simpa [selIs, flipperSelBytes] using hilk
  · simpa [selIs, flipperSelBytes] using hkick
  · simpa [selIs, flipperSelBytes] using hkicks
  · simpa [selIs, flipperSelBytes] using hrely
  · simpa [selIs, flipperSelBytes] using htau
  · simpa [selIs, flipperSelBytes] using htend
  · simpa [selIs, flipperSelBytes] using htick
  · simpa [selIs, flipperSelBytes] using httl
  · simpa [selIs, flipperSelBytes] using hvat
  · simpa [selIs, flipperSelBytes] using hwards
  · simpa [selIs, flipperSelBytes] using hyank

theorem flipperCorrect :
    runtimeEquivalence!?! config flipperBytecode contract := by
  refine runtimeEquivalence!?!.intro ?_
  intro cA gh bl σ_evm σ_solm σ₀ g A I hcode hsize hperm hAccounts
  by_cases hwv : I.weiValue = ⟨0⟩
  · by_cases hbeg : selIs I (flipperSelBytes 0)
    · exact flipperBegBodyCore hcode hsize hperm hwv hbeg hAccounts
    · by_cases hbids : selIs I (flipperSelBytes 1)
      · exact flipperBidsBodyCore hcode hsize hperm hwv hbids hAccounts
      · by_cases hcat : selIs I (flipperSelBytes 2)
        · exact flipperCatBodyCore hcode hsize hperm hwv hcat hAccounts
        · by_cases hdeal : selIs I (flipperSelBytes 3)
          · exact flipperDealBodyCore hcode hsize hperm hwv hdeal hAccounts
          · by_cases hdent : selIs I (flipperSelBytes 4)
            · exact flipperDentBodyCore hcode hsize hperm hwv hdent hAccounts
            · by_cases hdeny : selIs I (flipperSelBytes 5)
              · exact flipperDenyBodyCore hcode hsize hperm hwv hdeny hAccounts
              · by_cases hfileAddress : selIs I (flipperSelBytes 6)
                · exact flipperFileAddressBodyCore hcode hsize hperm hwv hfileAddress
                    hAccounts
                · by_cases hfileUint : selIs I (flipperSelBytes 7)
                  · exact flipperFileUintBodyCore hcode hsize hperm hwv hfileUint
                      hAccounts
                  · by_cases hilk : selIs I (flipperSelBytes 8)
                    · exact flipperIlkBodyCore hcode hsize hperm hwv hilk hAccounts
                    · by_cases hkick : selIs I (flipperSelBytes 9)
                      · exact flipperKickBodyCore hcode hsize hperm hwv hkick hAccounts
                      · by_cases hkicks : selIs I (flipperSelBytes 10)
                        · exact flipperKicksBodyCore hcode hsize hperm hwv hkicks hAccounts
                        · by_cases hrely : selIs I (flipperSelBytes 11)
                          · exact flipperRelyBodyCore hcode hsize hperm hwv hrely hAccounts
                          · by_cases htau : selIs I (flipperSelBytes 12)
                            · exact flipperTauBodyCore hcode hsize hperm hwv htau hAccounts
                            · by_cases htend : selIs I (flipperSelBytes 13)
                              · exact flipperTendBodyCore hcode hsize hperm hwv htend
                                  hAccounts
                              · by_cases htick : selIs I (flipperSelBytes 14)
                                · exact flipperTickBodyCore hcode hsize hperm hwv htick
                                    hAccounts
                                · by_cases httl : selIs I (flipperSelBytes 15)
                                  · exact flipperTtlBodyCore hcode hsize hperm hwv httl
                                      hAccounts
                                  · by_cases hvat : selIs I (flipperSelBytes 16)
                                    · exact flipperVatBodyCore hcode hsize hperm hwv hvat
                                        hAccounts
                                    · by_cases hwards : selIs I (flipperSelBytes 17)
                                      · exact flipperWardsBodyCore hcode hsize hperm hwv
                                          hwards hAccounts
                                      · by_cases hyank : selIs I (flipperSelBytes 18)
                                        · exact flipperYankBodyCore hcode hsize hperm hwv
                                            hyank hAccounts
                                        · exact flipperNoDispatch hcode hsize hperm hwv
                                            (flipperNoSelectorMatches hbeg hbids hcat
                                              hdeal hdent hdeny hfileAddress hfileUint
                                              hilk hkick hkicks hrely htau htend htick httl
                                              hvat hwards hyank)
                                            hAccounts
  · exact flipperNonPayable hcode hwv

theorem flipperContractCorrect :
    contractEquivalence config flipperCreationBytecode flipperBytecode contract :=
  contractEquivalence.intro flipperConstructorCorrect flipperCorrect

end Benchmarks.Dss.Flipper
