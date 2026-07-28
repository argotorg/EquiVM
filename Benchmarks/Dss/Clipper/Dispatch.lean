import Benchmarks.Dss.Clipper.Trusted

/-!
# MakerDAO/Sky DSS Clipper dispatcher facts

Shared selector-disjointness facts used by the top-level runtime dispatcher scaffold.
-/

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Benchmarks.Dss.Clipper.Immutables

set_option maxRecDepth 2000000

namespace Benchmarks.Dss.Clipper

attribute [local simp]
  activeSelectorBytes
  bufSelectorBytes
  calcSelectorBytes
  chipSelectorBytes
  chostSelectorBytes
  countSelectorBytes
  cuspSelectorBytes
  denySelectorBytes
  dogSelectorBytes
  fileUintSelectorBytes
  fileAddressSelectorBytes
  getStatusSelectorBytes
  ilkSelectorBytes
  kickSelectorBytes
  kicksSelectorBytes
  listSelectorBytes
  redoSelectorBytes
  relySelectorBytes
  salesSelectorBytes
  spotterSelectorBytes
  stoppedSelectorBytes
  tailSelectorBytes
  takeSelectorBytes
  tipSelectorBytes
  upchostSelectorBytes
  vatSelectorBytes
  vowSelectorBytes
  wardsSelectorBytes
  yankSelectorBytes

theorem clipperNoSelectorMatches {I : ExecutionEnv}
    (hactive : ¬ selIs I (clipperSelBytes 0))
    (hbuf : ¬ selIs I (clipperSelBytes 1))
    (hcalc : ¬ selIs I (clipperSelBytes 2))
    (hchip : ¬ selIs I (clipperSelBytes 3))
    (hchost : ¬ selIs I (clipperSelBytes 4))
    (hcount : ¬ selIs I (clipperSelBytes 5))
    (hcusp : ¬ selIs I (clipperSelBytes 6))
    (hdeny : ¬ selIs I (clipperSelBytes 7))
    (hdog : ¬ selIs I (clipperSelBytes 8))
    (hfileUint : ¬ selIs I (clipperSelBytes 9))
    (hfileAddress : ¬ selIs I (clipperSelBytes 10))
    (hgetStatus : ¬ selIs I (clipperSelBytes 11))
    (hilk : ¬ selIs I (clipperSelBytes 12))
    (hkick : ¬ selIs I (clipperSelBytes 13))
    (hkicks : ¬ selIs I (clipperSelBytes 14))
    (hlist : ¬ selIs I (clipperSelBytes 15))
    (hredo : ¬ selIs I (clipperSelBytes 16))
    (hrely : ¬ selIs I (clipperSelBytes 17))
    (hsales : ¬ selIs I (clipperSelBytes 18))
    (hspotter : ¬ selIs I (clipperSelBytes 19))
    (hstopped : ¬ selIs I (clipperSelBytes 20))
    (htail : ¬ selIs I (clipperSelBytes 21))
    (htake : ¬ selIs I (clipperSelBytes 22))
    (htip : ¬ selIs I (clipperSelBytes 23))
    (hupchost : ¬ selIs I (clipperSelBytes 24))
    (hvat : ¬ selIs I (clipperSelBytes 25))
    (hvow : ¬ selIs I (clipperSelBytes 26))
    (hwards : ¬ selIs I (clipperSelBytes 27))
    (hyank : ¬ selIs I (clipperSelBytes 28)) :
    ∀ i, i < 29 → (clipperSelBytes i == I.calldata.extract 0 4) = false := by
  intro i hi
  interval_cases i
  · simpa [clipperSelBytes, selIs] using hactive
  · simpa [clipperSelBytes, selIs] using hbuf
  · simpa [clipperSelBytes, selIs] using hcalc
  · simpa [clipperSelBytes, selIs] using hchip
  · simpa [clipperSelBytes, selIs] using hchost
  · simpa [clipperSelBytes, selIs] using hcount
  · simpa [clipperSelBytes, selIs] using hcusp
  · simpa [clipperSelBytes, selIs] using hdeny
  · simpa [clipperSelBytes, selIs] using hdog
  · simpa [clipperSelBytes, selIs] using hfileUint
  · simpa [clipperSelBytes, selIs] using hfileAddress
  · simpa [clipperSelBytes, selIs] using hgetStatus
  · simpa [clipperSelBytes, selIs] using hilk
  · simpa [clipperSelBytes, selIs] using hkick
  · simpa [clipperSelBytes, selIs] using hkicks
  · simpa [clipperSelBytes, selIs] using hlist
  · simpa [clipperSelBytes, selIs] using hredo
  · simpa [clipperSelBytes, selIs] using hrely
  · simpa [clipperSelBytes, selIs] using hsales
  · simpa [clipperSelBytes, selIs] using hspotter
  · simpa [clipperSelBytes, selIs] using hstopped
  · simpa [clipperSelBytes, selIs] using htail
  · simpa [clipperSelBytes, selIs] using htake
  · simpa [clipperSelBytes, selIs] using htip
  · simpa [clipperSelBytes, selIs] using hupchost
  · simpa [clipperSelBytes, selIs] using hvat
  · simpa [clipperSelBytes, selIs] using hvow
  · simpa [clipperSelBytes, selIs] using hwards
  · simpa [clipperSelBytes, selIs] using hyank

theorem clipperDispatch_none_short (v : ClipperImmutables) {cd : ByteArray}
    (h : cd.size < 4) :
    dispatchMsg (contract v) cd = none := by
  rw [dispatchMsg_eq_dispatchList (contract v) cd (by rfl) (by rfl)]
  change dispatchList (transitions v) cd = none
  exact dispatchList_none_short _ (by
    intro t ht
    simp [transitions] at ht
    rcases ht with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      | rfl | rfl | rfl
    all_goals
      simp [selectorOf]
      native_decide) h

theorem clipperDispatch_none_nomatch (v : ClipperImmutables) {cd : ByteArray}
    (hnm : ∀ i, i < 29 → (clipperSelBytes i == cd.extract 0 4) = false) :
    dispatchMsg (contract v) cd = none := by
  apply dispatchMsg_none_of_all_ne (hfallback := by rfl) (hreceive := by rfl)
  intro t ht
  simp [contract, transitions] at ht
  rcases ht with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    | rfl | rfl | rfl
  · rw [selectorOf, activeSelectorBytes]
    simpa [clipperSelBytes] using hnm 0 (by omega)
  · rw [selectorOf, bufSelectorBytes]
    simpa [clipperSelBytes] using hnm 1 (by omega)
  · rw [selectorOf, calcSelectorBytes]
    simpa [clipperSelBytes] using hnm 2 (by omega)
  · rw [selectorOf, chipSelectorBytes]
    simpa [clipperSelBytes] using hnm 3 (by omega)
  · rw [selectorOf, chostSelectorBytes]
    simpa [clipperSelBytes] using hnm 4 (by omega)
  · rw [selectorOf, countSelectorBytes]
    simpa [clipperSelBytes] using hnm 5 (by omega)
  · rw [selectorOf, cuspSelectorBytes]
    simpa [clipperSelBytes] using hnm 6 (by omega)
  · rw [selectorOf, denySelectorBytes]
    simpa [clipperSelBytes] using hnm 7 (by omega)
  · rw [selectorOf, dogSelectorBytes]
    simpa [clipperSelBytes] using hnm 8 (by omega)
  · rw [selectorOf, fileUintSelectorBytes]
    simpa [clipperSelBytes] using hnm 9 (by omega)
  · rw [selectorOf, fileAddressSelectorBytes]
    simpa [clipperSelBytes] using hnm 10 (by omega)
  · rw [selectorOf, getStatusSelectorBytes]
    simpa [clipperSelBytes] using hnm 11 (by omega)
  · rw [selectorOf, ilkSelectorBytes v]
    simpa [clipperSelBytes] using hnm 12 (by omega)
  · rw [selectorOf, kickSelectorBytes v]
    simpa [clipperSelBytes] using hnm 13 (by omega)
  · rw [selectorOf, kicksSelectorBytes]
    simpa [clipperSelBytes] using hnm 14 (by omega)
  · rw [selectorOf, listSelectorBytes]
    simpa [clipperSelBytes] using hnm 15 (by omega)
  · rw [selectorOf, redoSelectorBytes v]
    simpa [clipperSelBytes] using hnm 16 (by omega)
  · rw [selectorOf, relySelectorBytes]
    simpa [clipperSelBytes] using hnm 17 (by omega)
  · rw [selectorOf, salesSelectorBytes]
    simpa [clipperSelBytes] using hnm 18 (by omega)
  · rw [selectorOf, spotterSelectorBytes]
    simpa [clipperSelBytes] using hnm 19 (by omega)
  · rw [selectorOf, stoppedSelectorBytes]
    simpa [clipperSelBytes] using hnm 20 (by omega)
  · rw [selectorOf, tailSelectorBytes]
    simpa [clipperSelBytes] using hnm 21 (by omega)
  · rw [selectorOf, takeSelectorBytes v]
    simpa [clipperSelBytes] using hnm 22 (by omega)
  · rw [selectorOf, tipSelectorBytes]
    simpa [clipperSelBytes] using hnm 23 (by omega)
  · rw [selectorOf, upchostSelectorBytes v]
    simpa [clipperSelBytes] using hnm 24 (by omega)
  · rw [selectorOf, vatSelectorBytes v]
    simpa [clipperSelBytes] using hnm 25 (by omega)
  · rw [selectorOf, vowSelectorBytes]
    simpa [clipperSelBytes] using hnm 26 (by omega)
  · rw [selectorOf, wardsSelectorBytes]
    simpa [clipperSelBytes] using hnm 27 (by omega)
  · rw [selectorOf, yankSelectorBytes v]
    simpa [clipperSelBytes] using hnm 28 (by omega)

end Benchmarks.Dss.Clipper
