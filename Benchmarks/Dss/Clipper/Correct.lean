import Benchmarks.Dss.Clipper.Active
import Benchmarks.Dss.Clipper.Buf
import Benchmarks.Dss.Clipper.Calc
import Benchmarks.Dss.Clipper.Chip
import Benchmarks.Dss.Clipper.Chost
import Benchmarks.Dss.Clipper.Constructor
import Benchmarks.Dss.Clipper.Count
import Benchmarks.Dss.Clipper.Cusp
import Benchmarks.Dss.Clipper.Deny
import Benchmarks.Dss.Clipper.Dog
import Benchmarks.Dss.Clipper.Fallback
import Benchmarks.Dss.Clipper.FileAddress
import Benchmarks.Dss.Clipper.FileUint
import Benchmarks.Dss.Clipper.GetStatus
import Benchmarks.Dss.Clipper.Ilk
import Benchmarks.Dss.Clipper.Kick
import Benchmarks.Dss.Clipper.Kicks
import Benchmarks.Dss.Clipper.List
import Benchmarks.Dss.Clipper.RedoBody
import Benchmarks.Dss.Clipper.Rely
import Benchmarks.Dss.Clipper.Sales
import Benchmarks.Dss.Clipper.Spotter
import Benchmarks.Dss.Clipper.Stopped
import Benchmarks.Dss.Clipper.Tail
import Benchmarks.Dss.Clipper.TakeBody
import Benchmarks.Dss.Clipper.Tip
import Benchmarks.Dss.Clipper.Upchost
import Benchmarks.Dss.Clipper.Vat
import Benchmarks.Dss.Clipper.Vow
import Benchmarks.Dss.Clipper.Wards
import Benchmarks.Dss.Clipper.Yank
import Solm.Refine

/-!
# MakerDAO/Sky DSS Clipper benchmark correctness

This file proves runtime equivalence and exposes the whole-contract wrapper combining it with
constructor equivalence.
-/

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Benchmarks.Dss.Clipper.Immutables

set_option maxRecDepth 2000000

namespace Benchmarks.Dss.Clipper

theorem clipperCorrect (v : ClipperImmutables) {code : ByteArray}
    (hcode : patchRuntime clipperBytecode (patches v) = some code) :
    runtimeRefinementWithWF clipperStorageWF config code contract (immStore v) := by
  refine runtimeRefinementWithWF.intro ?_
  intro σ σ₀ g A I hIcode hsize hperm hStorageWF
  by_cases hwv : I.weiValue = ⟨0⟩
  · by_cases hactive : selIs I (clipperSelBytes 0)
    · exact clipperActiveBody v hcode hIcode hsize hperm hwv hactive
    · by_cases hbuf : selIs I (clipperSelBytes 1)
      · exact clipperBufBody v hcode hIcode hsize hperm hwv hbuf
      · by_cases hcalc : selIs I (clipperSelBytes 2)
        · exact clipperCalcBody v hcode hIcode hsize hperm hwv hcalc
        · by_cases hchip : selIs I (clipperSelBytes 3)
          · exact clipperChipBody v hcode hIcode hsize hperm hwv hchip
          · by_cases hchost : selIs I (clipperSelBytes 4)
            · exact clipperChostBody v hcode hIcode hsize hperm hwv hchost
            · by_cases hcount : selIs I (clipperSelBytes 5)
              · exact clipperCountBody v hcode hIcode hsize hperm hwv hcount
              · by_cases hcusp : selIs I (clipperSelBytes 6)
                · exact clipperCuspBody v hcode hIcode hsize hperm hwv hcusp
                · by_cases hdeny : selIs I (clipperSelBytes 7)
                  · exact clipperDenyBody v hcode hIcode hsize hperm hwv hdeny
                  · by_cases hdog : selIs I (clipperSelBytes 8)
                    · exact clipperDogBody v hcode hIcode hsize hperm hwv hdog
                    · by_cases hfileUint : selIs I (clipperSelBytes 9)
                      · exact clipperFileUintBody v hcode hIcode hsize hperm hwv hfileUint

                      · by_cases hfileAddress : selIs I (clipperSelBytes 10)
                        · exact clipperFileAddressBody v hcode hIcode hsize hperm hwv
                            hfileAddress
                        · by_cases hgetStatus : selIs I (clipperSelBytes 11)
                          · exact clipperGetStatusBody v hcode hIcode hsize hperm hwv
                              hgetStatus
                          · by_cases hilk : selIs I (clipperSelBytes 12)
                            · exact clipperIlkBody v hcode hIcode hsize hperm hwv hilk
                            · by_cases hkick : selIs I (clipperSelBytes 13)
                              · exact clipperKickBody v hcode hIcode hsize hperm hwv hkick
                                  hStorageWF
                              · by_cases hkicks : selIs I (clipperSelBytes 14)
                                · exact clipperKicksBody v hcode hIcode hsize hperm hwv
                                    hkicks
                                · by_cases hlist : selIs I (clipperSelBytes 15)
                                  · exact clipperListBody v hcode hIcode hsize hperm hwv
                                      hlist hStorageWF
                                  · by_cases hredo : selIs I (clipperSelBytes 16)
                                    · exact clipperRedoBody v hcode hIcode hsize hperm hwv
                                        hredo
                                    · by_cases hrely : selIs I (clipperSelBytes 17)
                                      · exact clipperRelyBody v hcode hIcode hsize hperm
                                          hwv hrely
                                      · by_cases hsales : selIs I (clipperSelBytes 18)
                                        · exact clipperSalesBody v hcode hIcode hsize hperm
                                            hwv hsales
                                        · by_cases hspotter : selIs I (clipperSelBytes 19)
                                          · exact clipperSpotterBody v hcode hIcode hsize
                                              hperm hwv hspotter
                                          · by_cases hstopped : selIs I (clipperSelBytes 20)
                                            · exact clipperStoppedBody v hcode hIcode hsize
                                                hperm hwv hstopped
                                            · by_cases htail : selIs I (clipperSelBytes 21)
                                              · exact clipperTailBody v hcode hIcode hsize
                                                  hperm hwv htail
                                              · by_cases htake : selIs I (clipperSelBytes 22)
                                                · exact clipperTakeBody v hcode hIcode hsize
                                                    hperm hwv htake hStorageWF
                                                · by_cases htip : selIs I (clipperSelBytes 23)
                                                  · exact clipperTipBody v hcode hIcode hsize
                                                      hperm hwv htip
                                                  · by_cases hupchost :
                                                        selIs I (clipperSelBytes 24)
                                                    · exact clipperUpchostBody v hcode hIcode
                                                        hsize hperm hwv hupchost
                                                    · by_cases hvat :
                                                          selIs I (clipperSelBytes 25)
                                                      · exact clipperVatBody v hcode hIcode
                                                          hsize hperm hwv hvat
                                                      · by_cases hvow :
                                                            selIs I (clipperSelBytes 26)
                                                        · exact clipperVowBody v hcode hIcode
                                                            hsize hperm hwv hvow
                                                        · by_cases hwards :
                                                              selIs I (clipperSelBytes 27)
                                                          · exact clipperWardsBody v hcode
                                                              hIcode hsize hperm hwv hwards
                                                          · by_cases hyank :
                                                                selIs I (clipperSelBytes 28)
                                                            · exact clipperYankBody v hcode
                                                                hIcode hsize hperm hwv hyank

                                                            · exact clipperNoDispatch v hcode
                                                                hIcode hsize hperm hwv
                                                                (clipperNoSelectorMatches
                                                                  hactive hbuf hcalc hchip
                                                                  hchost hcount hcusp hdeny
                                                                  hdog hfileUint hfileAddress
                                                                  hgetStatus hilk hkick hkicks
                                                                  hlist hredo hrely hsales
                                                                  hspotter hstopped htail htake
                                                                  htip hupchost hvat hvow hwards
                                                                  hyank)
  · exact clipperNonPayable v hcode hIcode hwv

/-- The runtime half for every well-typed immutables store: the store holds some `vat` and a
    32-byte `ilk`, and the code deployed for it is the template patched with them. -/
theorem clipperRuntimeCorrect (imms : Store) (hfit : immutablesFit contract imms) :
    runtimeRefinementWithWF clipperStorageWF config (deployedRuntime imms) contract
      (restrictImmutables contract imms) := by
  obtain ⟨vv, hvv, hfv⟩ := hfit ⟨"vat", .address⟩ (by simp [contract])
  obtain ⟨vi, hvi, hfi⟩ := hfit ⟨"ilk", .bytes ⟨31, by decide⟩⟩ (by simp [contract])
  simp only at hvv hvi
  cases vv <;> simp [elemValueFits] at hfv
  cases vi <;> simp [elemValueFits] at hfi
  rename_i vat n ilk
  obtain ⟨hn, hlen⟩ := hfi
  have hilk : n = bytes32Width := by rw [bytes32Width]; exact hn.symm
  subst hilk
  have hcode : deployedRuntime imms = clipperCtorPatchedRuntime vat ilk := by
    simp only [deployedRuntime, hvv, hvi]
  have hrestr :
      restrictImmutables contract imms = immStore (clipperCtorImmutables vat ilk hlen) := by
    rw [Std.HashMap.get?_eq_getElem?] at hvv hvi
    simp [restrictImmutables, contract, immStore, clipperCtorImmutables, hvv, hvi]
  rw [hcode, hrestr]
  exact clipperCorrect _ (clipperPatchRuntime_eq_ctorPatchedRuntime vat ilk hlen)

theorem clipperContractCorrect :
    contractRefinementWF clipperStorageWF config clipperCreationBytecode contract :=
  .of_runtime clipperConstructorCorrect clipperRuntimeCorrect

end Benchmarks.Dss.Clipper
