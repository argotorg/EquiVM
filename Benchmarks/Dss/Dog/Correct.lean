import Benchmarks.Dss.Dog.Constructor
import Benchmarks.Dss.Dog.Bark
import Benchmarks.Dss.Dog.Cage
import Benchmarks.Dss.Dog.Chop
import Benchmarks.Dss.Dog.Deny
import Benchmarks.Dss.Dog.Digs
import Benchmarks.Dss.Dog.Dirt
import Benchmarks.Dss.Dog.FileAddress
import Benchmarks.Dss.Dog.FileIlkClip
import Benchmarks.Dss.Dog.FileIlkUint
import Benchmarks.Dss.Dog.FileUint
import Benchmarks.Dss.Dog.Hole
import Benchmarks.Dss.Dog.Ilks
import Benchmarks.Dss.Dog.Live
import Benchmarks.Dss.Dog.Rely
import Benchmarks.Dss.Dog.Vat
import Benchmarks.Dss.Dog.Vow
import Benchmarks.Dss.Dog.Wards
import Solm.Equiv

/-!
# MakerDAO/Sky DSS Dog benchmark correctness stub

The upstream Solidity source, optimized runtime bytecode, Solm AST spec, and Solm syntax companion
are present. The runtime-equivalence proof is intentionally left as the benchmark target. This file
also exposes the whole-contract wrapper that combines the constructor and runtime targets.
-/

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach Reasoning.Refinement
open Benchmarks.Dss.Dog.Immutables

set_option maxRecDepth 2000000

namespace Benchmarks.Dss.Dog

theorem dogNoSelectorMatches {I : ExecutionEnv}
    (hDirt : ¬ selIs I (dogSelBytes 0))
    (hHole : ¬ selIs I (dogSelBytes 1))
    (hBark : ¬ selIs I (dogSelBytes 2))
    (hCage : ¬ selIs I (dogSelBytes 3))
    (hChop : ¬ selIs I (dogSelBytes 4))
    (hDeny : ¬ selIs I (dogSelBytes 5))
    (hDigs : ¬ selIs I (dogSelBytes 6))
    (hFileIlkUint : ¬ selIs I (dogSelBytes 7))
    (hFileUint : ¬ selIs I (dogSelBytes 8))
    (hFileAddress : ¬ selIs I (dogSelBytes 9))
    (hFileIlkClip : ¬ selIs I (dogSelBytes 10))
    (hIlks : ¬ selIs I (dogSelBytes 11))
    (hLive : ¬ selIs I (dogSelBytes 12))
    (hRely : ¬ selIs I (dogSelBytes 13))
    (hVat : ¬ selIs I (dogSelBytes 14))
    (hVow : ¬ selIs I (dogSelBytes 15))
    (hWards : ¬ selIs I (dogSelBytes 16)) :
    ∀ i, i < 17 → (dogSelBytes i == I.calldata.extract 0 4) = false := by
  intro i hi
  interval_cases i
  · simpa [selIs, dogSelBytes] using hDirt
  · simpa [selIs, dogSelBytes] using hHole
  · simpa [selIs, dogSelBytes] using hBark
  · simpa [selIs, dogSelBytes] using hCage
  · simpa [selIs, dogSelBytes] using hChop
  · simpa [selIs, dogSelBytes] using hDeny
  · simpa [selIs, dogSelBytes] using hDigs
  · simpa [selIs, dogSelBytes] using hFileIlkUint
  · simpa [selIs, dogSelBytes] using hFileUint
  · simpa [selIs, dogSelBytes] using hFileAddress
  · simpa [selIs, dogSelBytes] using hFileIlkClip
  · simpa [selIs, dogSelBytes] using hIlks
  · simpa [selIs, dogSelBytes] using hLive
  · simpa [selIs, dogSelBytes] using hRely
  · simpa [selIs, dogSelBytes] using hVat
  · simpa [selIs, dogSelBytes] using hVow
  · simpa [selIs, dogSelBytes] using hWards

theorem dogCorrect (v : DogImmutables) {code : ByteArray}
    (hpatch : patchRuntime dogBytecode (patches v) = some code) :
    runtimeEquivalence!?! (config v) code (contract v) := by
  refine runtimeEquivalence!?!.intro ?_
  intro cA gh bl σ_evm σ_solm σ₀ g A I hcode hsize hperm hAccounts
  by_cases hwv : I.weiValue = ⟨0⟩
  · by_cases hDirt : selIs I (dogSelBytes 0)
    · exact dogDirtBodyCore hpatch hcode hsize hperm hwv hDirt hAccounts
    · by_cases hHole : selIs I (dogSelBytes 1)
      · exact dogHoleBodyCore hpatch hcode hsize hperm hwv hHole hAccounts
      · by_cases hBark : selIs I (dogSelBytes 2)
        · exact dogBarkBodyCore hpatch hcode hsize hperm hwv hBark hAccounts
        · by_cases hCage : selIs I (dogSelBytes 3)
          · exact dogCageBodyCore hpatch hcode hsize hperm hwv hCage hAccounts
          · by_cases hChop : selIs I (dogSelBytes 4)
            · exact dogChopBodyCore hpatch hcode hsize hperm hwv hChop hAccounts
            · by_cases hDeny : selIs I (dogSelBytes 5)
              · exact dogDenyBodyCore hpatch hcode hsize hperm hwv hDeny hAccounts
              · by_cases hDigs : selIs I (dogSelBytes 6)
                · exact dogDigsBodyCore hpatch hcode hsize hperm hwv hDigs hAccounts
                · by_cases hFileIlkUint : selIs I (dogSelBytes 7)
                  · exact dogFileIlkUintBodyCore hpatch hcode hsize hperm hwv
                      hFileIlkUint hAccounts
                  · by_cases hFileUint : selIs I (dogSelBytes 8)
                    · exact dogFileUintBodyCore hpatch hcode hsize hperm hwv hFileUint
                        hAccounts
                    · by_cases hFileAddress : selIs I (dogSelBytes 9)
                      · exact dogFileAddressBodyCore hpatch hcode hsize hperm hwv
                          hFileAddress hAccounts
                      · by_cases hFileIlkClip : selIs I (dogSelBytes 10)
                        · exact dogFileIlkClipBodyCore hpatch hcode hsize hperm hwv
                            hFileIlkClip hAccounts
                        · by_cases hIlks : selIs I (dogSelBytes 11)
                          · exact dogIlksBodyCore hpatch hcode hsize hperm hwv hIlks
                              hAccounts
                          · by_cases hLive : selIs I (dogSelBytes 12)
                            · exact dogLiveBodyCore hpatch hcode hsize hperm hwv hLive
                                hAccounts
                            · by_cases hRely : selIs I (dogSelBytes 13)
                              · exact dogRelyBodyCore hpatch hcode hsize hperm hwv hRely
                                  hAccounts
                              · by_cases hVat : selIs I (dogSelBytes 14)
                                · exact dogVatBodyCore hpatch hcode hsize hperm hwv hVat
                                    hAccounts
                                · by_cases hVow : selIs I (dogSelBytes 15)
                                  · exact dogVowBodyCore hpatch hcode hsize hperm hwv hVow
                                      hAccounts
                                  · by_cases hWards : selIs I (dogSelBytes 16)
                                    · exact dogWardsBodyCore hpatch hcode hsize hperm hwv
                                        hWards hAccounts
                                    · exact dogNoDispatch hpatch hcode hsize hperm hwv
                                        (dogNoSelectorMatches hDirt hHole hBark hCage
                                          hChop hDeny hDigs hFileIlkUint hFileUint
                                          hFileAddress hFileIlkClip hIlks hLive hRely
                                          hVat hVow hWards)
                                        hAccounts
  · exact dogNonPayable hpatch hcode hwv

theorem dogContractCorrect (v : DogImmutables) {code : ByteArray}
    (hcode : patchRuntime dogBytecode (patches v) = some code) :
    contractEquivalenceWith (config v) dogCreationBytecode code (contract v)
      (runtimeCodeOf dogBytecode) :=
  contractEquivalenceWith.intro
    (dogConstructorCorrect v)
    (dogCorrect v hcode)

end Benchmarks.Dss.Dog
