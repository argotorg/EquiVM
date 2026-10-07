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
import Solm.Refine

/-!
# MakerDAO/Sky DSS Dog benchmark correctness stub

The upstream Solidity source, optimized runtime bytecode, Solm AST spec, and Solm syntax companion
are present. The runtime-equivalence proof is intentionally left as the benchmark target. This file
also exposes the whole-contract wrapper that combines the constructor and runtime targets.
-/

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
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
    runtimeRefinement config code contract (immStore v) := by
  refine runtimeRefinement.intro ?_
  intro σ σ₀ g A I hcode hsize
  by_cases hwv : I.weiValue = ⟨0⟩
  · by_cases hDirt : selIs I (dogSelBytes 0)
    · exact dogDirtBodyCore hpatch hcode hsize hwv hDirt
    · by_cases hHole : selIs I (dogSelBytes 1)
      · exact dogHoleBodyCore hpatch hcode hsize hwv hHole
      · by_cases hBark : selIs I (dogSelBytes 2)
        · exact dogBarkBodyCore hpatch hcode hsize hwv hBark
        · by_cases hCage : selIs I (dogSelBytes 3)
          · exact dogCageBodyCore hpatch hcode hsize hwv hCage
          · by_cases hChop : selIs I (dogSelBytes 4)
            · exact dogChopBodyCore hpatch hcode hsize hwv hChop
            · by_cases hDeny : selIs I (dogSelBytes 5)
              · exact dogDenyBodyCore hpatch hcode hsize hwv hDeny
              · by_cases hDigs : selIs I (dogSelBytes 6)
                · exact dogDigsBodyCore hpatch hcode hsize hwv hDigs
                · by_cases hFileIlkUint : selIs I (dogSelBytes 7)
                  · exact dogFileIlkUintBodyCore hpatch hcode hsize hwv
                      hFileIlkUint
                  · by_cases hFileUint : selIs I (dogSelBytes 8)
                    · exact dogFileUintBodyCore hpatch hcode hsize hwv hFileUint
                    · by_cases hFileAddress : selIs I (dogSelBytes 9)
                      · exact dogFileAddressBodyCore hpatch hcode hsize hwv
                          hFileAddress
                      · by_cases hFileIlkClip : selIs I (dogSelBytes 10)
                        · exact dogFileIlkClipBodyCore hpatch hcode hsize hwv
                            hFileIlkClip
                        · by_cases hIlks : selIs I (dogSelBytes 11)
                          · exact dogIlksBodyCore hpatch hcode hsize hwv hIlks
                          · by_cases hLive : selIs I (dogSelBytes 12)
                            · exact dogLiveBodyCore hpatch hcode hsize hwv hLive
                            · by_cases hRely : selIs I (dogSelBytes 13)
                              · exact dogRelyBodyCore hpatch hcode hsize hwv hRely
                              · by_cases hVat : selIs I (dogSelBytes 14)
                                · exact dogVatBodyCore hpatch hcode hsize hwv hVat
                                · by_cases hVow : selIs I (dogSelBytes 15)
                                  · exact dogVowBodyCore hpatch hcode hsize hwv hVow
                                  · by_cases hWards : selIs I (dogSelBytes 16)
                                    · exact dogWardsBodyCore hpatch hcode hsize hwv
                                        hWards
                                    · exact dogNoDispatch hpatch hcode hsize hwv
                                        (dogNoSelectorMatches hDirt hHole hBark hCage
                                          hChop hDeny hDigs hFileIlkUint hFileUint
                                          hFileAddress hFileIlkClip hIlks hLive hRely
                                          hVat hVow hWards)
  · exact dogNonPayable hpatch hcode hwv

/-- A well-typed immutables store runs as the store of some valuation. -/
theorem restrictImmutables_of_fit {imms : Store} (h : immutablesFit contract imms) :
    ∃ v, restrictImmutables contract imms = immStore v := by
  obtain ⟨vo, hvo, hfo⟩ := h ⟨"vat", .address⟩ (by simp [contract])
  simp only at hvo
  cases vo <;> simp [elemValueFits] at hfo
  rename_i vat
  rw [Std.HashMap.get?_eq_getElem?] at hvo
  exact ⟨{ vat := vat }, by simp [restrictImmutables, contract, immStore, hvo]⟩

theorem dogRuntimeCorrect (imms : Store) (hfit : immutablesFit contract imms) :
    runtimeRefinement config (immutableLayout.deployed dogBytecode imms) contract
      (restrictImmutables contract imms) := by
  obtain ⟨v, hv⟩ := restrictImmutables_of_fit hfit
  rw [← Reasoning.Immutables.Layout.deployed_restrict immutableLayout_keys, hv,
    dogDeployed_eq (vat := v.vat) (by simp [immStore])]
  exact dogCorrect v (dogPatchRuntime_eq_ctorPatchedRuntime v.vat)

theorem dogContractCorrect :
    contractRefinement config dogCreationBytecode contract :=
  .of_runtime dogConstructorCorrect dogRuntimeCorrect

end Benchmarks.Dss.Dog
