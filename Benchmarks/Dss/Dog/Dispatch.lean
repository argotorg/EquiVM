import Benchmarks.Dss.Dog.Trusted

/-!
# MakerDAO/Sky DSS Dog dispatcher facts

Solm dispatch routing facts and the shared runtime revert paths.
-/

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Benchmarks.Dss.Dog.Immutables

set_option maxRecDepth 2000000

namespace Benchmarks.Dss.Dog

attribute [local simp]
  dirtSelectorBytes
  holeSelectorBytes
  barkSelectorBytes
  cageSelectorBytes
  chopSelectorBytes
  denySelectorBytes
  digsSelectorBytes
  fileIlkUintSelectorBytes
  fileUintSelectorBytes
  fileAddressSelectorBytes
  fileIlkClipSelectorBytes
  ilksSelectorBytes
  liveSelectorBytes
  relySelectorBytes
  vatSelectorBytes
  vowSelectorBytes
  wardsSelectorBytes

theorem dogDispatchDirt {v : DogImmutables} {I : ExecutionEnv}
    (_hsel : selIs I (dogSelBytes 0)) :
    dispatchMsg (contract v) I.calldata = some DirtTransition := by
  have hcd : I.calldata.extract 0 4 = dogSelBytes 0 := (byteArray_eq_of_beq _hsel).symm
  exact dispatchMsg_eq_some_of_split
    (contract := contract v)
    (pre := [])
    (ti := DirtTransition)
    (post :=
      [HoleTransition, barkTransition v, cageTransition, chopTransition, denyTransition,
        digsTransition, fileIlkUintTransition, fileUintTransition, fileAddressTransition,
        fileIlkClipTransition, ilksTransition, liveTransition, relyTransition, vatTransition v,
        vowTransition, wardsTransition])
    (hfallback := by rfl)
    (htr := by rfl)
    (hpre := by intro t ht; simp at ht)
    (hhit := by
      rw [selectorOf, dirtSelectorBytes, hcd]
      native_decide)
    (hreceive := by rfl)

theorem dogDispatchHole {v : DogImmutables} {I : ExecutionEnv}
    (_hsel : selIs I (dogSelBytes 1)) :
    dispatchMsg (contract v) I.calldata = some HoleTransition := by
  have hcd : I.calldata.extract 0 4 = dogSelBytes 1 := (byteArray_eq_of_beq _hsel).symm
  exact dispatchMsg_eq_some_of_split
    (contract := contract v)
    (pre := [DirtTransition])
    (ti := HoleTransition)
    (post :=
      [barkTransition v, cageTransition, chopTransition, denyTransition, digsTransition,
        fileIlkUintTransition, fileUintTransition, fileAddressTransition, fileIlkClipTransition,
        ilksTransition, liveTransition, relyTransition, vatTransition v, vowTransition,
        wardsTransition])
    (hfallback := by rfl)
    (htr := by rfl)
    (hpre := by
      intro t ht
      simp at ht
      rcases ht with rfl
      rw [selectorOf, dirtSelectorBytes, hcd]
      native_decide)
    (hhit := by
      rw [selectorOf, holeSelectorBytes, hcd]
      native_decide)
    (hreceive := by rfl)

theorem dogDispatchBark {v : DogImmutables} {I : ExecutionEnv}
    (_hsel : selIs I (dogSelBytes 2)) :
    dispatchMsg (contract v) I.calldata = some (barkTransition v) := by
  have hcd : I.calldata.extract 0 4 = dogSelBytes 2 := (byteArray_eq_of_beq _hsel).symm
  exact dispatchMsg_eq_some_of_split
    (contract := contract v)
    (pre := [DirtTransition, HoleTransition])
    (ti := barkTransition v)
    (post :=
      [cageTransition, chopTransition, denyTransition, digsTransition, fileIlkUintTransition,
        fileUintTransition, fileAddressTransition, fileIlkClipTransition, ilksTransition,
        liveTransition, relyTransition, vatTransition v, vowTransition, wardsTransition])
    (hfallback := by rfl)
    (htr := by rfl)
    (hpre := by
      intro t ht
      simp at ht
      rcases ht with rfl | rfl
      · rw [selectorOf, dirtSelectorBytes, hcd]
        native_decide
      · rw [selectorOf, holeSelectorBytes, hcd]
        native_decide)
    (hhit := by
      rw [selectorOf, barkSelectorBytes v, hcd]
      native_decide)
    (hreceive := by rfl)

theorem dogDispatchCage {v : DogImmutables} {I : ExecutionEnv}
    (_hsel : selIs I (dogSelBytes 3)) :
    dispatchMsg (contract v) I.calldata = some cageTransition := by
  have hcd : I.calldata.extract 0 4 = dogSelBytes 3 := (byteArray_eq_of_beq _hsel).symm
  exact dispatchMsg_eq_some_of_split
    (contract := contract v)
    (pre := [DirtTransition, HoleTransition, barkTransition v])
    (ti := cageTransition)
    (post :=
      [chopTransition, denyTransition, digsTransition, fileIlkUintTransition,
        fileUintTransition, fileAddressTransition, fileIlkClipTransition, ilksTransition,
        liveTransition, relyTransition, vatTransition v, vowTransition, wardsTransition])
    (hfallback := by rfl)
    (htr := by rfl)
    (hpre := by
      intro t ht
      simp at ht
      rcases ht with rfl | rfl | rfl
      · rw [selectorOf, dirtSelectorBytes, hcd]
        native_decide
      · rw [selectorOf, holeSelectorBytes, hcd]
        native_decide
      · rw [selectorOf, barkSelectorBytes v, hcd]
        native_decide)
    (hhit := by
      rw [selectorOf, cageSelectorBytes, hcd]
      native_decide)
    (hreceive := by rfl)

theorem dogDispatchChop {v : DogImmutables} {I : ExecutionEnv}
    (_hsel : selIs I (dogSelBytes 4)) :
    dispatchMsg (contract v) I.calldata = some chopTransition := by
  have hcd : I.calldata.extract 0 4 = dogSelBytes 4 := (byteArray_eq_of_beq _hsel).symm
  exact dispatchMsg_eq_some_of_split
    (contract := contract v)
    (pre := [DirtTransition, HoleTransition, barkTransition v, cageTransition])
    (ti := chopTransition)
    (post :=
      [denyTransition, digsTransition, fileIlkUintTransition, fileUintTransition,
        fileAddressTransition, fileIlkClipTransition, ilksTransition, liveTransition,
        relyTransition, vatTransition v, vowTransition, wardsTransition])
    (hfallback := by rfl)
    (htr := by rfl)
    (hpre := by
      intro t ht
      simp at ht
      rcases ht with rfl | rfl | rfl | rfl
      · rw [selectorOf, dirtSelectorBytes, hcd]
        native_decide
      · rw [selectorOf, holeSelectorBytes, hcd]
        native_decide
      · rw [selectorOf, barkSelectorBytes v, hcd]
        native_decide
      · rw [selectorOf, cageSelectorBytes, hcd]
        native_decide)
    (hhit := by
      rw [selectorOf, chopSelectorBytes, hcd]
      native_decide)
    (hreceive := by rfl)

theorem dogDispatchDeny {v : DogImmutables} {I : ExecutionEnv}
    (_hsel : selIs I (dogSelBytes 5)) :
    dispatchMsg (contract v) I.calldata = some denyTransition := by
  have hcd : I.calldata.extract 0 4 = dogSelBytes 5 := (byteArray_eq_of_beq _hsel).symm
  exact dispatchMsg_eq_some_of_split
    (contract := contract v)
    (pre := [DirtTransition, HoleTransition, barkTransition v, cageTransition, chopTransition])
    (ti := denyTransition)
    (post :=
      [digsTransition, fileIlkUintTransition, fileUintTransition, fileAddressTransition,
        fileIlkClipTransition, ilksTransition, liveTransition, relyTransition, vatTransition v,
        vowTransition, wardsTransition])
    (hfallback := by rfl)
    (htr := by rfl)
    (hpre := by
      intro t ht
      simp at ht
      rcases ht with rfl | rfl | rfl | rfl | rfl
      · rw [selectorOf, dirtSelectorBytes, hcd]
        native_decide
      · rw [selectorOf, holeSelectorBytes, hcd]
        native_decide
      · rw [selectorOf, barkSelectorBytes v, hcd]
        native_decide
      · rw [selectorOf, cageSelectorBytes, hcd]
        native_decide
      · rw [selectorOf, chopSelectorBytes, hcd]
        native_decide)
    (hhit := by
      rw [selectorOf, denySelectorBytes, hcd]
      native_decide)
    (hreceive := by rfl)

theorem dogDispatchDigs {v : DogImmutables} {I : ExecutionEnv}
    (_hsel : selIs I (dogSelBytes 6)) :
    dispatchMsg (contract v) I.calldata = some digsTransition := by
  have hcd : I.calldata.extract 0 4 = dogSelBytes 6 := (byteArray_eq_of_beq _hsel).symm
  exact dispatchMsg_eq_some_of_split
    (contract := contract v)
    (pre :=
      [DirtTransition, HoleTransition, barkTransition v, cageTransition, chopTransition,
        denyTransition])
    (ti := digsTransition)
    (post :=
      [fileIlkUintTransition, fileUintTransition, fileAddressTransition, fileIlkClipTransition,
        ilksTransition, liveTransition, relyTransition, vatTransition v, vowTransition,
        wardsTransition])
    (hfallback := by rfl)
    (htr := by rfl)
    (hpre := by
      intro t ht
      simp at ht
      rcases ht with rfl | rfl | rfl | rfl | rfl | rfl
      · rw [selectorOf, dirtSelectorBytes, hcd]
        native_decide
      · rw [selectorOf, holeSelectorBytes, hcd]
        native_decide
      · rw [selectorOf, barkSelectorBytes v, hcd]
        native_decide
      · rw [selectorOf, cageSelectorBytes, hcd]
        native_decide
      · rw [selectorOf, chopSelectorBytes, hcd]
        native_decide
      · rw [selectorOf, denySelectorBytes, hcd]
        native_decide)
    (hhit := by
      rw [selectorOf, digsSelectorBytes, hcd]
      native_decide)
    (hreceive := by rfl)

theorem dogDispatchFileIlkUint {v : DogImmutables} {I : ExecutionEnv}
    (_hsel : selIs I (dogSelBytes 7)) :
    dispatchMsg (contract v) I.calldata = some fileIlkUintTransition := by
  have hcd : I.calldata.extract 0 4 = dogSelBytes 7 := (byteArray_eq_of_beq _hsel).symm
  exact dispatchMsg_eq_some_of_split
    (contract := contract v)
    (pre :=
      [DirtTransition, HoleTransition, barkTransition v, cageTransition, chopTransition,
        denyTransition, digsTransition])
    (ti := fileIlkUintTransition)
    (post :=
      [fileUintTransition, fileAddressTransition, fileIlkClipTransition, ilksTransition,
        liveTransition, relyTransition, vatTransition v, vowTransition, wardsTransition])
    (hfallback := by rfl)
    (htr := by rfl)
    (hpre := by
      intro t ht
      simp at ht
      rcases ht with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · rw [selectorOf, dirtSelectorBytes, hcd]
        native_decide
      · rw [selectorOf, holeSelectorBytes, hcd]
        native_decide
      · rw [selectorOf, barkSelectorBytes v, hcd]
        native_decide
      · rw [selectorOf, cageSelectorBytes, hcd]
        native_decide
      · rw [selectorOf, chopSelectorBytes, hcd]
        native_decide
      · rw [selectorOf, denySelectorBytes, hcd]
        native_decide
      · rw [selectorOf, digsSelectorBytes, hcd]
        native_decide)
    (hhit := by
      rw [selectorOf, fileIlkUintSelectorBytes, hcd]
      native_decide)
    (hreceive := by rfl)

theorem dogDispatchFileUint {v : DogImmutables} {I : ExecutionEnv}
    (_hsel : selIs I (dogSelBytes 8)) :
    dispatchMsg (contract v) I.calldata = some fileUintTransition := by
  have hcd : I.calldata.extract 0 4 = dogSelBytes 8 := (byteArray_eq_of_beq _hsel).symm
  exact dispatchMsg_eq_some_of_split
    (contract := contract v)
    (pre :=
      [DirtTransition, HoleTransition, barkTransition v, cageTransition, chopTransition,
        denyTransition, digsTransition, fileIlkUintTransition])
    (ti := fileUintTransition)
    (post :=
      [fileAddressTransition, fileIlkClipTransition, ilksTransition, liveTransition,
        relyTransition, vatTransition v, vowTransition, wardsTransition])
    (hfallback := by rfl)
    (htr := by rfl)
    (hpre := by
      intro t ht
      simp at ht
      rcases ht with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · rw [selectorOf, dirtSelectorBytes, hcd]
        native_decide
      · rw [selectorOf, holeSelectorBytes, hcd]
        native_decide
      · rw [selectorOf, barkSelectorBytes v, hcd]
        native_decide
      · rw [selectorOf, cageSelectorBytes, hcd]
        native_decide
      · rw [selectorOf, chopSelectorBytes, hcd]
        native_decide
      · rw [selectorOf, denySelectorBytes, hcd]
        native_decide
      · rw [selectorOf, digsSelectorBytes, hcd]
        native_decide
      · rw [selectorOf, fileIlkUintSelectorBytes, hcd]
        native_decide)
    (hhit := by
      rw [selectorOf, fileUintSelectorBytes, hcd]
      native_decide)
    (hreceive := by rfl)

theorem dogDispatchFileAddress {v : DogImmutables} {I : ExecutionEnv}
    (_hsel : selIs I (dogSelBytes 9)) :
    dispatchMsg (contract v) I.calldata = some fileAddressTransition := by
  have hcd : I.calldata.extract 0 4 = dogSelBytes 9 := (byteArray_eq_of_beq _hsel).symm
  exact dispatchMsg_eq_some_of_split
    (contract := contract v)
    (pre :=
      [DirtTransition, HoleTransition, barkTransition v, cageTransition, chopTransition,
        denyTransition, digsTransition, fileIlkUintTransition, fileUintTransition])
    (ti := fileAddressTransition)
    (post :=
      [fileIlkClipTransition, ilksTransition, liveTransition, relyTransition, vatTransition v,
        vowTransition, wardsTransition])
    (hfallback := by rfl)
    (htr := by rfl)
    (hpre := by
      intro t ht
      simp at ht
      rcases ht with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      all_goals
        first
        | rw [selectorOf, dirtSelectorBytes, hcd]
        | rw [selectorOf, holeSelectorBytes, hcd]
        | rw [selectorOf, barkSelectorBytes v, hcd]
        | rw [selectorOf, cageSelectorBytes, hcd]
        | rw [selectorOf, chopSelectorBytes, hcd]
        | rw [selectorOf, denySelectorBytes, hcd]
        | rw [selectorOf, digsSelectorBytes, hcd]
        | rw [selectorOf, fileIlkUintSelectorBytes, hcd]
        | rw [selectorOf, fileUintSelectorBytes, hcd]
      all_goals native_decide)
    (hhit := by
      rw [selectorOf, fileAddressSelectorBytes, hcd]
      native_decide)
    (hreceive := by rfl)

theorem dogDispatchFileIlkClip {v : DogImmutables} {I : ExecutionEnv}
    (_hsel : selIs I (dogSelBytes 10)) :
    dispatchMsg (contract v) I.calldata = some fileIlkClipTransition := by
  have hcd : I.calldata.extract 0 4 = dogSelBytes 10 := (byteArray_eq_of_beq _hsel).symm
  exact dispatchMsg_eq_some_of_split
    (contract := contract v)
    (pre :=
      [DirtTransition, HoleTransition, barkTransition v, cageTransition, chopTransition,
        denyTransition, digsTransition, fileIlkUintTransition, fileUintTransition,
        fileAddressTransition])
    (ti := fileIlkClipTransition)
    (post :=
      [ilksTransition, liveTransition, relyTransition, vatTransition v, vowTransition,
        wardsTransition])
    (hfallback := by rfl)
    (htr := by rfl)
    (hpre := by
      intro t ht
      simp at ht
      rcases ht with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      all_goals
        first
        | rw [selectorOf, dirtSelectorBytes, hcd]
        | rw [selectorOf, holeSelectorBytes, hcd]
        | rw [selectorOf, barkSelectorBytes v, hcd]
        | rw [selectorOf, cageSelectorBytes, hcd]
        | rw [selectorOf, chopSelectorBytes, hcd]
        | rw [selectorOf, denySelectorBytes, hcd]
        | rw [selectorOf, digsSelectorBytes, hcd]
        | rw [selectorOf, fileIlkUintSelectorBytes, hcd]
        | rw [selectorOf, fileUintSelectorBytes, hcd]
        | rw [selectorOf, fileAddressSelectorBytes, hcd]
      all_goals native_decide)
    (hhit := by
      rw [selectorOf, fileIlkClipSelectorBytes, hcd]
      native_decide)
    (hreceive := by rfl)

theorem dogDispatchIlks {v : DogImmutables} {I : ExecutionEnv}
    (_hsel : selIs I (dogSelBytes 11)) :
    dispatchMsg (contract v) I.calldata = some ilksTransition := by
  have hcd : I.calldata.extract 0 4 = dogSelBytes 11 := (byteArray_eq_of_beq _hsel).symm
  exact dispatchMsg_eq_some_of_split
    (contract := contract v)
    (pre :=
      [DirtTransition, HoleTransition, barkTransition v, cageTransition, chopTransition,
        denyTransition, digsTransition, fileIlkUintTransition, fileUintTransition,
        fileAddressTransition, fileIlkClipTransition])
    (ti := ilksTransition)
    (post := [liveTransition, relyTransition, vatTransition v, vowTransition, wardsTransition])
    (hfallback := by rfl)
    (htr := by rfl)
    (hpre := by
      intro t ht
      simp at ht
      rcases ht with
        rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      all_goals
        first
        | rw [selectorOf, dirtSelectorBytes, hcd]
        | rw [selectorOf, holeSelectorBytes, hcd]
        | rw [selectorOf, barkSelectorBytes v, hcd]
        | rw [selectorOf, cageSelectorBytes, hcd]
        | rw [selectorOf, chopSelectorBytes, hcd]
        | rw [selectorOf, denySelectorBytes, hcd]
        | rw [selectorOf, digsSelectorBytes, hcd]
        | rw [selectorOf, fileIlkUintSelectorBytes, hcd]
        | rw [selectorOf, fileUintSelectorBytes, hcd]
        | rw [selectorOf, fileAddressSelectorBytes, hcd]
        | rw [selectorOf, fileIlkClipSelectorBytes, hcd]
      all_goals native_decide)
    (hhit := by
      rw [selectorOf, ilksSelectorBytes, hcd]
      native_decide)
    (hreceive := by rfl)

theorem dogDispatchLive {v : DogImmutables} {I : ExecutionEnv}
    (_hsel : selIs I (dogSelBytes 12)) :
    dispatchMsg (contract v) I.calldata = some liveTransition := by
  have hcd : I.calldata.extract 0 4 = dogSelBytes 12 := (byteArray_eq_of_beq _hsel).symm
  exact dispatchMsg_eq_some_of_split
    (contract := contract v)
    (pre :=
      [DirtTransition, HoleTransition, barkTransition v, cageTransition, chopTransition,
        denyTransition, digsTransition, fileIlkUintTransition, fileUintTransition,
        fileAddressTransition, fileIlkClipTransition, ilksTransition])
    (ti := liveTransition)
    (post := [relyTransition, vatTransition v, vowTransition, wardsTransition])
    (hfallback := by rfl)
    (htr := by rfl)
    (hpre := by
      intro t ht
      simp at ht
      rcases ht with
        rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      all_goals
        first
        | rw [selectorOf, dirtSelectorBytes, hcd]
        | rw [selectorOf, holeSelectorBytes, hcd]
        | rw [selectorOf, barkSelectorBytes v, hcd]
        | rw [selectorOf, cageSelectorBytes, hcd]
        | rw [selectorOf, chopSelectorBytes, hcd]
        | rw [selectorOf, denySelectorBytes, hcd]
        | rw [selectorOf, digsSelectorBytes, hcd]
        | rw [selectorOf, fileIlkUintSelectorBytes, hcd]
        | rw [selectorOf, fileUintSelectorBytes, hcd]
        | rw [selectorOf, fileAddressSelectorBytes, hcd]
        | rw [selectorOf, fileIlkClipSelectorBytes, hcd]
        | rw [selectorOf, ilksSelectorBytes, hcd]
      all_goals native_decide)
    (hhit := by
      rw [selectorOf, liveSelectorBytes, hcd]
      native_decide)
    (hreceive := by rfl)

theorem dogDispatchRely {v : DogImmutables} {I : ExecutionEnv}
    (_hsel : selIs I (dogSelBytes 13)) :
    dispatchMsg (contract v) I.calldata = some relyTransition := by
  have hcd : I.calldata.extract 0 4 = dogSelBytes 13 := (byteArray_eq_of_beq _hsel).symm
  exact dispatchMsg_eq_some_of_split
    (contract := contract v)
    (pre :=
      [DirtTransition, HoleTransition, barkTransition v, cageTransition, chopTransition,
        denyTransition, digsTransition, fileIlkUintTransition, fileUintTransition,
        fileAddressTransition, fileIlkClipTransition, ilksTransition, liveTransition])
    (ti := relyTransition)
    (post := [vatTransition v, vowTransition, wardsTransition])
    (hfallback := by rfl)
    (htr := by rfl)
    (hpre := by
      intro t ht
      simp at ht
      rcases ht with
        rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      all_goals
        first
        | rw [selectorOf, dirtSelectorBytes, hcd]
        | rw [selectorOf, holeSelectorBytes, hcd]
        | rw [selectorOf, barkSelectorBytes v, hcd]
        | rw [selectorOf, cageSelectorBytes, hcd]
        | rw [selectorOf, chopSelectorBytes, hcd]
        | rw [selectorOf, denySelectorBytes, hcd]
        | rw [selectorOf, digsSelectorBytes, hcd]
        | rw [selectorOf, fileIlkUintSelectorBytes, hcd]
        | rw [selectorOf, fileUintSelectorBytes, hcd]
        | rw [selectorOf, fileAddressSelectorBytes, hcd]
        | rw [selectorOf, fileIlkClipSelectorBytes, hcd]
        | rw [selectorOf, ilksSelectorBytes, hcd]
        | rw [selectorOf, liveSelectorBytes, hcd]
      all_goals native_decide)
    (hhit := by
      rw [selectorOf, relySelectorBytes, hcd]
      native_decide)
    (hreceive := by rfl)

theorem dogDispatchVat {v : DogImmutables} {I : ExecutionEnv}
    (_hsel : selIs I (dogSelBytes 14)) :
    dispatchMsg (contract v) I.calldata = some (vatTransition v) := by
  have hcd : I.calldata.extract 0 4 = dogSelBytes 14 := (byteArray_eq_of_beq _hsel).symm
  exact dispatchMsg_eq_some_of_split
    (contract := contract v)
    (pre :=
      [DirtTransition, HoleTransition, barkTransition v, cageTransition, chopTransition,
        denyTransition, digsTransition, fileIlkUintTransition, fileUintTransition,
        fileAddressTransition, fileIlkClipTransition, ilksTransition, liveTransition,
        relyTransition])
    (ti := vatTransition v)
    (post := [vowTransition, wardsTransition])
    (hfallback := by rfl)
    (htr := by rfl)
    (hpre := by
      intro t ht
      simp at ht
      rcases ht with
        rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
          rfl
      all_goals
        first
        | rw [selectorOf, dirtSelectorBytes, hcd]
        | rw [selectorOf, holeSelectorBytes, hcd]
        | rw [selectorOf, barkSelectorBytes v, hcd]
        | rw [selectorOf, cageSelectorBytes, hcd]
        | rw [selectorOf, chopSelectorBytes, hcd]
        | rw [selectorOf, denySelectorBytes, hcd]
        | rw [selectorOf, digsSelectorBytes, hcd]
        | rw [selectorOf, fileIlkUintSelectorBytes, hcd]
        | rw [selectorOf, fileUintSelectorBytes, hcd]
        | rw [selectorOf, fileAddressSelectorBytes, hcd]
        | rw [selectorOf, fileIlkClipSelectorBytes, hcd]
        | rw [selectorOf, ilksSelectorBytes, hcd]
        | rw [selectorOf, liveSelectorBytes, hcd]
        | rw [selectorOf, relySelectorBytes, hcd]
      all_goals native_decide)
    (hhit := by
      rw [selectorOf, vatSelectorBytes v, hcd]
      native_decide)
    (hreceive := by rfl)

theorem dogDispatchVow {v : DogImmutables} {I : ExecutionEnv}
    (_hsel : selIs I (dogSelBytes 15)) :
    dispatchMsg (contract v) I.calldata = some vowTransition := by
  have hcd : I.calldata.extract 0 4 = dogSelBytes 15 := (byteArray_eq_of_beq _hsel).symm
  exact dispatchMsg_eq_some_of_split
    (contract := contract v)
    (pre :=
      [DirtTransition, HoleTransition, barkTransition v, cageTransition, chopTransition,
        denyTransition, digsTransition, fileIlkUintTransition, fileUintTransition,
        fileAddressTransition, fileIlkClipTransition, ilksTransition, liveTransition,
        relyTransition, vatTransition v])
    (ti := vowTransition)
    (post := [wardsTransition])
    (hfallback := by rfl)
    (htr := by rfl)
    (hpre := by
      intro t ht
      simp at ht
      rcases ht with
        rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
          rfl | rfl
      all_goals
        first
        | rw [selectorOf, dirtSelectorBytes, hcd]
        | rw [selectorOf, holeSelectorBytes, hcd]
        | rw [selectorOf, barkSelectorBytes v, hcd]
        | rw [selectorOf, cageSelectorBytes, hcd]
        | rw [selectorOf, chopSelectorBytes, hcd]
        | rw [selectorOf, denySelectorBytes, hcd]
        | rw [selectorOf, digsSelectorBytes, hcd]
        | rw [selectorOf, fileIlkUintSelectorBytes, hcd]
        | rw [selectorOf, fileUintSelectorBytes, hcd]
        | rw [selectorOf, fileAddressSelectorBytes, hcd]
        | rw [selectorOf, fileIlkClipSelectorBytes, hcd]
        | rw [selectorOf, ilksSelectorBytes, hcd]
        | rw [selectorOf, liveSelectorBytes, hcd]
        | rw [selectorOf, relySelectorBytes, hcd]
        | rw [selectorOf, vatSelectorBytes v, hcd]
      all_goals native_decide)
    (hhit := by
      rw [selectorOf, vowSelectorBytes, hcd]
      native_decide)
    (hreceive := by rfl)

theorem dogDispatchWards {v : DogImmutables} {I : ExecutionEnv}
    (_hsel : selIs I (dogSelBytes 16)) :
    dispatchMsg (contract v) I.calldata = some wardsTransition := by
  have hcd : I.calldata.extract 0 4 = dogSelBytes 16 := (byteArray_eq_of_beq _hsel).symm
  exact dispatchMsg_eq_some_of_split
    (contract := contract v)
    (pre :=
      [DirtTransition, HoleTransition, barkTransition v, cageTransition, chopTransition,
        denyTransition, digsTransition, fileIlkUintTransition, fileUintTransition,
        fileAddressTransition, fileIlkClipTransition, ilksTransition, liveTransition,
        relyTransition, vatTransition v, vowTransition])
    (ti := wardsTransition)
    (post := [])
    (hfallback := by rfl)
    (htr := by rfl)
    (hpre := by
      intro t ht
      simp at ht
      rcases ht with
        rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
          rfl | rfl | rfl
      all_goals
        first
        | rw [selectorOf, dirtSelectorBytes, hcd]
        | rw [selectorOf, holeSelectorBytes, hcd]
        | rw [selectorOf, barkSelectorBytes v, hcd]
        | rw [selectorOf, cageSelectorBytes, hcd]
        | rw [selectorOf, chopSelectorBytes, hcd]
        | rw [selectorOf, denySelectorBytes, hcd]
        | rw [selectorOf, digsSelectorBytes, hcd]
        | rw [selectorOf, fileIlkUintSelectorBytes, hcd]
        | rw [selectorOf, fileUintSelectorBytes, hcd]
        | rw [selectorOf, fileAddressSelectorBytes, hcd]
        | rw [selectorOf, fileIlkClipSelectorBytes, hcd]
        | rw [selectorOf, ilksSelectorBytes, hcd]
        | rw [selectorOf, liveSelectorBytes, hcd]
        | rw [selectorOf, relySelectorBytes, hcd]
        | rw [selectorOf, vatSelectorBytes v, hcd]
        | rw [selectorOf, vowSelectorBytes, hcd]
      all_goals native_decide)
    (hhit := by
      rw [selectorOf, wardsSelectorBytes, hcd]
      native_decide)
    (hreceive := by rfl)

theorem dogDispatch_none_short (v : DogImmutables) {cd : ByteArray} (_h : cd.size < 4) :
    dispatchMsg (contract v) cd = none := by
  rw [dispatchMsg_eq_dispatchList (contract v) cd (by rfl)]
  change dispatchList
    [DirtTransition, HoleTransition, barkTransition v, cageTransition, chopTransition,
      denyTransition, digsTransition, fileIlkUintTransition, fileUintTransition,
      fileAddressTransition, fileIlkClipTransition, ilksTransition, liveTransition,
      relyTransition, vatTransition v, vowTransition, wardsTransition] cd = none
  exact dispatchList_none_short _ (by
    intro t ht
    simp at ht
    rcases ht with
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
        rfl | rfl | rfl | rfl
    all_goals
      simp [selectorOf, dogSelBytes]
      native_decide) _h

theorem dogDispatch_none_nomatch (v : DogImmutables) {cd : ByteArray}
    (_hnm : ∀ i, i < 17 → (dogSelBytes i == cd.extract 0 4) = false) :
    dispatchMsg (contract v) cd = none := by
  apply dispatchMsg_none_of_all_ne (hfallback := by rfl)
  intro t ht
  simp [contract, transitions] at ht
  rcases ht with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl
  · rw [selectorOf, dirtSelectorBytes]
    simpa [dogSelBytes] using _hnm 0 (by omega)
  · rw [selectorOf, holeSelectorBytes]
    simpa [dogSelBytes] using _hnm 1 (by omega)
  · rw [selectorOf, barkSelectorBytes v]
    simpa [dogSelBytes] using _hnm 2 (by omega)
  · rw [selectorOf, cageSelectorBytes]
    simpa [dogSelBytes] using _hnm 3 (by omega)
  · rw [selectorOf, chopSelectorBytes]
    simpa [dogSelBytes] using _hnm 4 (by omega)
  · rw [selectorOf, denySelectorBytes]
    simpa [dogSelBytes] using _hnm 5 (by omega)
  · rw [selectorOf, digsSelectorBytes]
    simpa [dogSelBytes] using _hnm 6 (by omega)
  · rw [selectorOf, fileIlkUintSelectorBytes]
    simpa [dogSelBytes] using _hnm 7 (by omega)
  · rw [selectorOf, fileUintSelectorBytes]
    simpa [dogSelBytes] using _hnm 8 (by omega)
  · rw [selectorOf, fileAddressSelectorBytes]
    simpa [dogSelBytes] using _hnm 9 (by omega)
  · rw [selectorOf, fileIlkClipSelectorBytes]
    simpa [dogSelBytes] using _hnm 10 (by omega)
  · rw [selectorOf, ilksSelectorBytes]
    simpa [dogSelBytes] using _hnm 11 (by omega)
  · rw [selectorOf, liveSelectorBytes]
    simpa [dogSelBytes] using _hnm 12 (by omega)
  · rw [selectorOf, relySelectorBytes]
    simpa [dogSelBytes] using _hnm 13 (by omega)
  · rw [selectorOf, vatSelectorBytes v]
    simpa [dogSelBytes] using _hnm 14 (by omega)
  · rw [selectorOf, vowSelectorBytes]
    simpa [dogSelBytes] using _hnm 15 (by omega)
  · rw [selectorOf, wardsSelectorBytes]
    simpa [dogSelBytes] using _hnm 16 (by omega)

theorem dogBodyReverts_of_nonpayable {v : DogImmutables} {evm : EVM.State} {locals : Store}
    {rest : List Stmt} (h : evm.executionEnv.weiValue ≠ ⟨0⟩) :
    ExecTransitionBody (config v) (contract v) evm locals (nonpayable ++ rest) .reverted := by
  simpa only [nonpayable, List.singleton_append] using
    (bodyReverts_nonPayable (cfg := config v) (contract := contract v) (evm := evm)
      (locals := locals) (rest := rest) h)

theorem dogBodyReverts_nonPayable (v : DogImmutables) (t : TransitionDecl)
    (_ht : t ∈ (contract v).transitions) (evm : EVM.State) (locals : Store)
    (_h : evm.executionEnv.weiValue ≠ ⟨0⟩) :
    ExecTransitionBody (config v) (contract v) evm locals t.body .reverted := by
  simp [contract, transitions] at _ht
  rcases _ht with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl <;>
    (change ExecTransitionBody (config v) (contract v) evm locals (nonpayable ++ _) .reverted
     exact dogBodyReverts_of_nonpayable _h)

theorem dogX_callvalue_ne {v : DogImmutables} {code : ByteArray}
    {cA gh bl σ σ₀ A I} {g : Sat256}
    (hpatch : patchRuntime dogBytecode (patches v) = some code)
    (hcode : I.code = code) (hwv : I.weiValue ≠ ⟨0⟩) :
    RDrev code g (initState cA gh bl σ σ₀ g A I) := by
  have h0 := solcGuardPrologueRD (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀)
    (A := A) (g := g) hcode
    (by rw [dogDecodePatchedEqTemplate1405 (pc := ⟨0⟩) hpatch (by native_decide)];
        native_decide)
    (by rw [dogDecodePatchedEqTemplate1405 (pc := ⟨2⟩) hpatch (by native_decide)];
        native_decide)
    (by rw [dogDecodePatchedEqTemplate1405 (pc := ⟨4⟩) hpatch (by native_decide)];
        native_decide)
    (by rw [dogDecodePatchedEqTemplate1405 (pc := ⟨5⟩) hpatch (by native_decide)];
        native_decide)
    (by rw [dogDecodePatchedEqTemplate1405 (pc := ⟨6⟩) hpatch (by native_decide)];
        native_decide)
    (by rw [dogDecodePatchedEqTemplate1405 (pc := ⟨7⟩) hpatch (by native_decide)];
        native_decide)
  have h12 := h0.push2 ⟨16⟩
    (by rw [dogDecodePatchedEqTemplate1405 (pc := ⟨8⟩) hpatch (by native_decide)];
        native_decide)
    (by simp only [List.length]; omega)
    |>.jumpiNT
      (by
        change decode code (⟨11⟩ : UInt256) = some (.JUMPI, .none)
        rw [dogDecodePatchedEqTemplate1405 (pc := ⟨11⟩) hpatch (by native_decide)]
        native_decide)
      (isZero_eq_zero_of_ne hwv) (by simp only [List.length]; omega)
  exact RD.solcPush1Dup1Revert0 h12
    (by
      change decode code (⟨12⟩ : UInt256) = some (.Push .PUSH1, some (⟨0⟩, 1))
      rw [dogDecodePatchedEqTemplate1405 (pc := ⟨12⟩) hpatch (by native_decide)]
      native_decide)
    (by
      change decode code (⟨14⟩ : UInt256) = some (.DUP1, .none)
      rw [dogDecodePatchedEqTemplate1405 (pc := ⟨14⟩) hpatch (by native_decide)]
      native_decide)
    (by
      change decode code (⟨15⟩ : UInt256) = some (.REVERT, .none)
      rw [dogDecodePatchedEqTemplate1405 (pc := ⟨15⟩) hpatch (by native_decide)]
      native_decide)
    (by simp only [List.length]; omega)

theorem dogX_short {v : DogImmutables} {code : ByteArray}
    {cA gh bl σ σ₀ A I} {g : Sat256}
    (hpatch : patchRuntime dogBytecode (patches v) = some code)
    (hcode : I.code = code) (hwv : I.weiValue = ⟨0⟩) (hsz : I.calldata.size < 4) :
    RDrev code g (initState cA gh bl σ σ₀ g A I) := by
  have h0 := solcGuardPrologueRD (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀)
    (A := A) (g := g) hcode
    (by rw [dogDecodePatchedEqTemplate1405 (pc := ⟨0⟩) hpatch (by native_decide)];
        native_decide)
    (by rw [dogDecodePatchedEqTemplate1405 (pc := ⟨2⟩) hpatch (by native_decide)];
        native_decide)
    (by rw [dogDecodePatchedEqTemplate1405 (pc := ⟨4⟩) hpatch (by native_decide)];
        native_decide)
    (by rw [dogDecodePatchedEqTemplate1405 (pc := ⟨5⟩) hpatch (by native_decide)];
        native_decide)
    (by rw [dogDecodePatchedEqTemplate1405 (pc := ⟨6⟩) hpatch (by native_decide)];
        native_decide)
    (by rw [dogDecodePatchedEqTemplate1405 (pc := ⟨7⟩) hpatch (by native_decide)];
        native_decide)
  obtain ⟨_, _, h1⟩ := solcGuardCallvalueZero
    (ctgt := (⟨16⟩ : UInt256)) (opC := .PUSH2) (wC := 2) h0 hwv (by decide)
    (by rw [dogDecodePatchedEqTemplate1405 (pc := ⟨8⟩) hpatch (by native_decide)];
        native_decide)
    (by
      change decode code (⟨11⟩ : UInt256) = some (.JUMPI, .none)
      rw [dogDecodePatchedEqTemplate1405 (pc := ⟨11⟩) hpatch (by native_decide)]
      native_decide)
    (by
      rw [dogDecodePatchedEqTemplate1405 (pc := ⟨16⟩) hpatch (by native_decide)]
      native_decide)
    (by
      change decode code (⟨17⟩ : UInt256) = some (.POP, .none)
      rw [dogDecodePatchedEqTemplate1405 (pc := ⟨17⟩) hpatch (by native_decide)]
      native_decide)
    (dogPatchedDJumpPrefix1405 ⟨16⟩ hpatch (by native_decide))
  have h267 := h1.push1 ⟨4⟩
    (by
      change decode code (⟨18⟩ : UInt256) = some (.Push .PUSH1, some (⟨4⟩, 1))
      rw [dogDecodePatchedEqTemplate1405 (pc := ⟨18⟩) hpatch (by native_decide)]
      native_decide)
    (by simp only [List.length]; omega)
    |>.calldatasize
      (by
        change decode code (⟨20⟩ : UInt256) = some (.CALLDATASIZE, .none)
        rw [dogDecodePatchedEqTemplate1405 (pc := ⟨20⟩) hpatch (by native_decide)]
        native_decide)
      (by simp only [List.length]; omega)
    |>.lt
      (by
        change decode code (⟨21⟩ : UInt256) = some (.LT, .none)
        rw [dogDecodePatchedEqTemplate1405 (pc := ⟨21⟩) hpatch (by native_decide)]
        native_decide)
      (by simp only [List.length]; omega)
    |>.push2 ⟨267⟩
      (by
        change decode code (⟨22⟩ : UInt256) = some (.Push .PUSH2, some (⟨267⟩, 2))
        rw [dogDecodePatchedEqTemplate1405 (pc := ⟨22⟩) hpatch (by native_decide)]
        native_decide)
      (by simp only [List.length]; omega)
    |>.jumpiT
      (by
        change decode code (⟨25⟩ : UInt256) = some (.JUMPI, .none)
        rw [dogDecodePatchedEqTemplate1405 (pc := ⟨25⟩) hpatch (by native_decide)]
        native_decide)
      (lt_four_ne_zero_of_lt hsz)
      (dogPatchedDJumpPrefix1405 ⟨267⟩ hpatch (by native_decide))
      (by simp only [List.length]; omega)
    |>.jumpdest
      (by
        rw [dogDecodePatchedEqTemplate1405 (pc := ⟨267⟩) hpatch (by native_decide)]
        native_decide)
      (by simp only [List.length]; omega)
  exact RD.solcPush1Dup1Revert0 h267
    (by
      change decode code (⟨268⟩ : UInt256) = some (.Push .PUSH1, some (⟨0⟩, 1))
      rw [dogDecodePatchedEqTemplate1405 (pc := ⟨268⟩) hpatch (by native_decide)]
      native_decide)
    (by
      change decode code (⟨270⟩ : UInt256) = some (.DUP1, .none)
      rw [dogDecodePatchedEqTemplate1405 (pc := ⟨270⟩) hpatch (by native_decide)]
      native_decide)
    (by
      change decode code (⟨271⟩ : UInt256) = some (.REVERT, .none)
      rw [dogDecodePatchedEqTemplate1405 (pc := ⟨271⟩) hpatch (by native_decide)]
      native_decide)
    (by simp only [List.length]; omega)

theorem dogReachSelector {v : DogImmutables} {code : ByteArray}
    {cA gh bl σ σ₀ A I} {g : Sat256}
    (hpatch : patchRuntime dogBytecode (patches v) = some code)
    (hcode : I.code = code) (hwv : I.weiValue = ⟨0⟩)
    (hsz : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size) :
    ∃ k C, RD code I g (initState cA gh bl σ σ₀ g A I) ⟨32⟩
      [solcSelectorWord I] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
  exact solcLegacyDispatchReachSelector
    (bodyPc := (⟨18⟩ : UInt256)) (loadPc := (⟨26⟩ : UInt256))
    (firstPc := (⟨32⟩ : UInt256)) (guardTgt := (⟨16⟩ : UInt256))
    (revertTgt := (⟨267⟩ : UInt256)) (guardWidth := 2) (revertWidth := 2)
    (guardOp := .PUSH2) (revertOp := .PUSH2)
    hcode hwv hsz hsize
    (by rw [dogDecodePatchedEqTemplate1405 (pc := ⟨0⟩) hpatch (by native_decide)];
        native_decide)
    (by rw [dogDecodePatchedEqTemplate1405 (pc := ⟨2⟩) hpatch (by native_decide)];
        native_decide)
    (by rw [dogDecodePatchedEqTemplate1405 (pc := ⟨4⟩) hpatch (by native_decide)];
        native_decide)
    (by rw [dogDecodePatchedEqTemplate1405 (pc := ⟨5⟩) hpatch (by native_decide)];
        native_decide)
    (by rw [dogDecodePatchedEqTemplate1405 (pc := ⟨6⟩) hpatch (by native_decide)];
        native_decide)
    (by rw [dogDecodePatchedEqTemplate1405 (pc := ⟨7⟩) hpatch (by native_decide)];
        native_decide)
    (by decide)
    (by rw [dogDecodePatchedEqTemplate1405 (pc := ⟨8⟩) hpatch (by native_decide)];
        native_decide)
    (by
      change decode code (⟨11⟩ : UInt256) = some (.JUMPI, .none)
      rw [dogDecodePatchedEqTemplate1405 (pc := ⟨11⟩) hpatch (by native_decide)]
      native_decide)
    (by
      rw [dogDecodePatchedEqTemplate1405 (pc := ⟨16⟩) hpatch (by native_decide)]
      native_decide)
    (by
      change decode code (⟨17⟩ : UInt256) = some (.POP, .none)
      rw [dogDecodePatchedEqTemplate1405 (pc := ⟨17⟩) hpatch (by native_decide)]
      native_decide)
    (dogPatchedDJumpPrefix1405 ⟨16⟩ hpatch (by native_decide))
    (by decide)
    (by
      rw [dogDecodePatchedEqTemplate1405 (pc := ⟨18⟩) hpatch (by native_decide)]
      native_decide)
    (by
      change decode code (⟨20⟩ : UInt256) = some (.CALLDATASIZE, .none)
      rw [dogDecodePatchedEqTemplate1405 (pc := ⟨20⟩) hpatch (by native_decide)]
      native_decide)
    (by
      change decode code (⟨21⟩ : UInt256) = some (.LT, .none)
      rw [dogDecodePatchedEqTemplate1405 (pc := ⟨21⟩) hpatch (by native_decide)]
      native_decide)
    (by decide)
    (by
      change decode code (⟨22⟩ : UInt256) = some (.Push .PUSH2, some (⟨267⟩, 2))
      rw [dogDecodePatchedEqTemplate1405 (pc := ⟨22⟩) hpatch (by native_decide)]
      native_decide)
    (by
      change decode code (⟨25⟩ : UInt256) = some (.JUMPI, .none)
      rw [dogDecodePatchedEqTemplate1405 (pc := ⟨25⟩) hpatch (by native_decide)]
      native_decide)
    (by decide)
    (by
      rw [dogDecodePatchedEqTemplate1405 (pc := ⟨26⟩) hpatch (by native_decide)]
      native_decide)
    (by
      change decode code (⟨28⟩ : UInt256) = some (.CALLDATALOAD, .none)
      rw [dogDecodePatchedEqTemplate1405 (pc := ⟨28⟩) hpatch (by native_decide)]
      native_decide)
    (by
      change decode code (⟨29⟩ : UInt256) = some (.Push .PUSH1, some (⟨224⟩, 1))
      rw [dogDecodePatchedEqTemplate1405 (pc := ⟨29⟩) hpatch (by native_decide)]
      native_decide)
    (by
      change decode code (⟨31⟩ : UInt256) = some (.SHR, .none)
      rw [dogDecodePatchedEqTemplate1405 (pc := ⟨31⟩) hpatch (by native_decide)]
      native_decide)
    (by decide)

theorem dogRootSplitWellFormed {v : DogImmutables} {code : ByteArray}
    (hpatch : patchRuntime dogBytecode (patches v) = some code) :
    selectorSplitWellFormed code ⟨32⟩ := by
  have hsel : armSelNat code ⟨32⟩ = ⟨2944204465⟩ := by
    dsimp [armSelNat]
    rw [dogPushAtPatchedEqTemplate1405 (pc := selArmPush4Pc (⟨32⟩ : UInt256)) hpatch
      (by native_decide)]
    native_decide
  have hop : armTgtOp code ⟨32⟩ = .PUSH2 := by
    dsimp [armTgtOp]
    rw [dogPushAtPatchedEqTemplate1405 (pc := selArmPushTgtPc (⟨32⟩ : UInt256)) hpatch
      (by native_decide)]
    native_decide
  have htgt : armTgt code ⟨32⟩ = ⟨162⟩ := by
    dsimp [armTgt]
    rw [dogPushAtPatchedEqTemplate1405 (pc := selArmPushTgtPc (⟨32⟩ : UInt256)) hpatch
      (by native_decide)]
    native_decide
  have hw : armTgtWidth code ⟨32⟩ = 2 := by
    dsimp [armTgtWidth]
    rw [dogPushAtPatchedEqTemplate1405 (pc := selArmPushTgtPc (⟨32⟩ : UInt256)) hpatch
      (by native_decide)]
    native_decide
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [dogDecodePatchedEqTemplate1405 (pc := (⟨32⟩ : UInt256)) hpatch (by native_decide)]
    native_decide
  · rw [hsel, dogDecodePatchedEqTemplate1405 (pc := selArmPush4Pc (⟨32⟩ : UInt256))
      hpatch (by native_decide)]
    native_decide
  · rw [dogDecodePatchedEqTemplate1405 (pc := selArmEqPc (⟨32⟩ : UInt256)) hpatch
      (by native_decide)]
    native_decide
  · rw [hop]; decide
  · rw [hop, htgt, hw, dogDecodePatchedEqTemplate1405
      (pc := selArmPushTgtPc (⟨32⟩ : UInt256)) hpatch (by native_decide)]
    native_decide
  · rw [hw, dogDecodePatchedEqTemplate1405 (pc := selArmJumpiPc (⟨32⟩ : UInt256) 2)
      hpatch (by native_decide)]
    native_decide

theorem dogHighSplitWellFormed {v : DogImmutables} {code : ByteArray}
    (hpatch : patchRuntime dogBytecode (patches v) = some code) :
    selectorSplitWellFormed code ⟨43⟩ := by
  have hsel : armSelNat code ⟨43⟩ = ⟨3616695608⟩ := by
    dsimp [armSelNat]
    rw [dogPushAtPatchedEqTemplate1405 (pc := selArmPush4Pc (⟨43⟩ : UInt256)) hpatch
      (by native_decide)]
    native_decide
  have hop : armTgtOp code ⟨43⟩ = .PUSH2 := by
    dsimp [armTgtOp]
    rw [dogPushAtPatchedEqTemplate1405 (pc := selArmPushTgtPc (⟨43⟩ : UInt256)) hpatch
      (by native_decide)]
    native_decide
  have htgt : armTgt code ⟨43⟩ = ⟨113⟩ := by
    dsimp [armTgt]
    rw [dogPushAtPatchedEqTemplate1405 (pc := selArmPushTgtPc (⟨43⟩ : UInt256)) hpatch
      (by native_decide)]
    native_decide
  have hw : armTgtWidth code ⟨43⟩ = 2 := by
    dsimp [armTgtWidth]
    rw [dogPushAtPatchedEqTemplate1405 (pc := selArmPushTgtPc (⟨43⟩ : UInt256)) hpatch
      (by native_decide)]
    native_decide
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [dogDecodePatchedEqTemplate1405 (pc := (⟨43⟩ : UInt256)) hpatch (by native_decide)]
    native_decide
  · rw [hsel, dogDecodePatchedEqTemplate1405 (pc := selArmPush4Pc (⟨43⟩ : UInt256))
      hpatch (by native_decide)]
    native_decide
  · rw [dogDecodePatchedEqTemplate1405 (pc := selArmEqPc (⟨43⟩ : UInt256)) hpatch
      (by native_decide)]
    native_decide
  · rw [hop]; decide
  · rw [hop, htgt, hw, dogDecodePatchedEqTemplate1405
      (pc := selArmPushTgtPc (⟨43⟩ : UInt256)) hpatch (by native_decide)]
    native_decide
  · rw [hw, dogDecodePatchedEqTemplate1405 (pc := selArmJumpiPc (⟨43⟩ : UInt256) 2)
      hpatch (by native_decide)]
    native_decide

theorem dogLowSplitWellFormed {v : DogImmutables} {code : ByteArray}
    (hpatch : patchRuntime dogBytecode (patches v) = some code) :
    selectorSplitWellFormed code ⟨163⟩ := by
  have hsel : armSelNat code ⟨163⟩ = ⟨1710941022⟩ := by
    dsimp [armSelNat]
    rw [dogPushAtPatchedEqTemplate1405 (pc := selArmPush4Pc (⟨163⟩ : UInt256)) hpatch
      (by native_decide)]
    native_decide
  have hop : armTgtOp code ⟨163⟩ = .PUSH2 := by
    dsimp [armTgtOp]
    rw [dogPushAtPatchedEqTemplate1405 (pc := selArmPushTgtPc (⟨163⟩ : UInt256)) hpatch
      (by native_decide)]
    native_decide
  have htgt : armTgt code ⟨163⟩ = ⟨222⟩ := by
    dsimp [armTgt]
    rw [dogPushAtPatchedEqTemplate1405 (pc := selArmPushTgtPc (⟨163⟩ : UInt256)) hpatch
      (by native_decide)]
    native_decide
  have hw : armTgtWidth code ⟨163⟩ = 2 := by
    dsimp [armTgtWidth]
    rw [dogPushAtPatchedEqTemplate1405 (pc := selArmPushTgtPc (⟨163⟩ : UInt256)) hpatch
      (by native_decide)]
    native_decide
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [dogDecodePatchedEqTemplate1405 (pc := (⟨163⟩ : UInt256)) hpatch (by native_decide)]
    native_decide
  · rw [hsel, dogDecodePatchedEqTemplate1405 (pc := selArmPush4Pc (⟨163⟩ : UInt256))
      hpatch (by native_decide)]
    native_decide
  · rw [dogDecodePatchedEqTemplate1405 (pc := selArmEqPc (⟨163⟩ : UInt256)) hpatch
      (by native_decide)]
    native_decide
  · rw [hop]; decide
  · rw [hop, htgt, hw, dogDecodePatchedEqTemplate1405
      (pc := selArmPushTgtPc (⟨163⟩ : UInt256)) hpatch (by native_decide)]
    native_decide
  · rw [hw, dogDecodePatchedEqTemplate1405 (pc := selArmJumpiPc (⟨163⟩ : UInt256) 2)
      hpatch (by native_decide)]
    native_decide

theorem dogJumpToDispatchRevert {v : DogImmutables} {code : ByteArray}
    {cA gh bl σ σ₀ A I} {g : Sat256} {pc : UInt256} {k C : ℕ}
    (hpatch : patchRuntime dogBytecode (patches v) = some code)
    (h : RD code I g (initState cA gh bl σ σ₀ g A I) pc [solcSelectorWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C)
    (hpush : decode code pc = some (.Push .PUSH2, some (⟨267⟩, 2)))
    (hjump : decode code (pc + UInt256.ofNat 3) = some (.JUMP, .none)) :
    RDrev code g (initState cA gh bl σ σ₀ g A I) := by
  have h267 := h.push2 ⟨267⟩ hpush
    (by simp only [List.length_singleton]; omega)
    |>.jump hjump (dogPatchedDJumpPrefix1405 ⟨267⟩ hpatch (by native_decide))
      (by simp only [List.length_singleton]; omega)
    |>.jumpdest
      (by
        rw [dogDecodePatchedEqTemplate1405 (pc := ⟨267⟩) hpatch (by native_decide)]
        native_decide)
      (by simp only [List.length_singleton]; omega)
  exact RD.solcPush1Dup1Revert0 h267
    (by
      change decode code (⟨268⟩ : UInt256) = some (.Push .PUSH1, some (⟨0⟩, 1))
      rw [dogDecodePatchedEqTemplate1405 (pc := ⟨268⟩) hpatch (by native_decide)]
      native_decide)
    (by
      change decode code (⟨270⟩ : UInt256) = some (.DUP1, .none)
      rw [dogDecodePatchedEqTemplate1405 (pc := ⟨270⟩) hpatch (by native_decide)]
      native_decide)
    (by
      change decode code (⟨271⟩ : UInt256) = some (.REVERT, .none)
      rw [dogDecodePatchedEqTemplate1405 (pc := ⟨271⟩) hpatch (by native_decide)]
      native_decide)
    (by simp only [List.length_singleton]; omega)

theorem dogDispatchRevertAt {v : DogImmutables} {code : ByteArray}
    {cA gh bl σ σ₀ A I} {g : Sat256} {k C : ℕ}
    (hpatch : patchRuntime dogBytecode (patches v) = some code)
    (h : RD code I g (initState cA gh bl σ σ₀ g A I) ⟨267⟩ [solcSelectorWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    RDrev code g (initState cA gh bl σ σ₀ g A I) := by
  have h268 := h.jumpdest
    (by
      rw [dogDecodePatchedEqTemplate1405 (pc := ⟨267⟩) hpatch (by native_decide)]
      native_decide)
    (by simp only [List.length_singleton]; omega)
  exact RD.solcPush1Dup1Revert0 h268
    (by
      change decode code (⟨268⟩ : UInt256) = some (.Push .PUSH1, some (⟨0⟩, 1))
      rw [dogDecodePatchedEqTemplate1405 (pc := ⟨268⟩) hpatch (by native_decide)]
      native_decide)
    (by
      change decode code (⟨270⟩ : UInt256) = some (.DUP1, .none)
      rw [dogDecodePatchedEqTemplate1405 (pc := ⟨270⟩) hpatch (by native_decide)]
      native_decide)
    (by
      change decode code (⟨271⟩ : UInt256) = some (.REVERT, .none)
      rw [dogDecodePatchedEqTemplate1405 (pc := ⟨271⟩) hpatch (by native_decide)]
      native_decide)
    (by simp only [List.length_singleton]; omega)

theorem dogVeryHighNoMatchRevert {v : DogImmutables} {code : ByteArray}
    {cA gh bl σ σ₀ A I} {g : Sat256} {k C : ℕ}
    (hpatch : patchRuntime dogBytecode (patches v) = some code)
    (hsz : 4 ≤ I.calldata.size)
    (hnm : ∀ i, i < 17 → (dogSelBytes i == I.calldata.extract 0 4) = false)
    (h : RD code I g (initState cA gh bl σ σ₀ g A I) ⟨54⟩ [solcSelectorWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    RDrev code g (initState cA gh bl σ σ₀ g A I) := by
  have h65 : RD code I g (initState cA gh bl σ σ₀ g A I) ⟨65⟩ [solcSelectorWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) (k + 5) (C + 22) := by
    simpa [selArmNextPc] using
      h.selectorArmNotTaken (selNat := dogSelectorWord 4) (tgt := (⟨629⟩ : UInt256))
        (width := 2) (op := .PUSH2)
        (by
          change decode code (⟨54⟩ : UInt256) = some (.DUP1, .none)
          rw [dogDecodePatchedEqTemplate1405 (pc := ⟨54⟩) hpatch (by native_decide)]
          native_decide)
        (by
          change decode code (⟨55⟩ : UInt256) =
            some (.Push .PUSH4, some (dogSelectorWord 4, 4))
          rw [dogDecodePatchedEqTemplate1405 (pc := ⟨55⟩) hpatch (by native_decide)]
          native_decide)
        (by
          change decode code (⟨60⟩ : UInt256) = some (.EQ, .none)
          rw [dogDecodePatchedEqTemplate1405 (pc := ⟨60⟩) hpatch (by native_decide)]
          native_decide)
        (by decide)
        (by
          change decode code (⟨61⟩ : UInt256) =
            some (.Push .PUSH2, some ((⟨629⟩ : UInt256), 2))
          rw [dogDecodePatchedEqTemplate1405 (pc := ⟨61⟩) hpatch (by native_decide)]
          native_decide)
        (by
          change decode code (⟨64⟩ : UInt256) = some (.JUMPI, .none)
          rw [dogDecodePatchedEqTemplate1405 (pc := ⟨64⟩) hpatch (by native_decide)]
          native_decide)
        (dogSelectorEqZero I hsz hnm 4 (by omega))
        (by simp)
  have h76 : RD code I g (initState cA gh bl σ σ₀ g A I) ⟨76⟩ [solcSelectorWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) ((k + 5) + 5)
      ((C + 22) + 22) := by
    simpa [selArmNextPc] using
      h65.selectorArmNotTaken (selNat := dogSelectorWord 11) (tgt := (⟨658⟩ : UInt256))
        (width := 2) (op := .PUSH2)
        (by
          change decode code (⟨65⟩ : UInt256) = some (.DUP1, .none)
          rw [dogDecodePatchedEqTemplate1405 (pc := ⟨65⟩) hpatch (by native_decide)]
          native_decide)
        (by
          change decode code (⟨66⟩ : UInt256) =
            some (.Push .PUSH4, some (dogSelectorWord 11, 4))
          rw [dogDecodePatchedEqTemplate1405 (pc := ⟨66⟩) hpatch (by native_decide)]
          native_decide)
        (by
          change decode code (⟨71⟩ : UInt256) = some (.EQ, .none)
          rw [dogDecodePatchedEqTemplate1405 (pc := ⟨71⟩) hpatch (by native_decide)]
          native_decide)
        (by decide)
        (by
          change decode code (⟨72⟩ : UInt256) =
            some (.Push .PUSH2, some ((⟨658⟩ : UInt256), 2))
          rw [dogDecodePatchedEqTemplate1405 (pc := ⟨72⟩) hpatch (by native_decide)]
          native_decide)
        (by
          change decode code (⟨75⟩ : UInt256) = some (.JUMPI, .none)
          rw [dogDecodePatchedEqTemplate1405 (pc := ⟨75⟩) hpatch (by native_decide)]
          native_decide)
        (dogSelectorEqZero I hsz hnm 11 (by omega))
        (by simp)
  have h87 : RD code I g (initState cA gh bl σ σ₀ g A I) ⟨87⟩ [solcSelectorWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) (((k + 5) + 5) + 5)
      (((C + 22) + 22) + 22) := by
    simpa [selArmNextPc] using
      h76.selectorArmNotTaken (selNat := dogSelectorWord 10) (tgt := (⟨735⟩ : UInt256))
        (width := 2) (op := .PUSH2)
        (by
          change decode code (⟨76⟩ : UInt256) = some (.DUP1, .none)
          rw [dogDecodePatchedEqTemplate1405 (pc := ⟨76⟩) hpatch (by native_decide)]
          native_decide)
        (by
          change decode code (⟨77⟩ : UInt256) =
            some (.Push .PUSH4, some (dogSelectorWord 10, 4))
          rw [dogDecodePatchedEqTemplate1405 (pc := ⟨77⟩) hpatch (by native_decide)]
          native_decide)
        (by
          change decode code (⟨82⟩ : UInt256) = some (.EQ, .none)
          rw [dogDecodePatchedEqTemplate1405 (pc := ⟨82⟩) hpatch (by native_decide)]
          native_decide)
        (by decide)
        (by
          change decode code (⟨83⟩ : UInt256) =
            some (.Push .PUSH2, some ((⟨735⟩ : UInt256), 2))
          rw [dogDecodePatchedEqTemplate1405 (pc := ⟨83⟩) hpatch (by native_decide)]
          native_decide)
        (by
          change decode code (⟨86⟩ : UInt256) = some (.JUMPI, .none)
          rw [dogDecodePatchedEqTemplate1405 (pc := ⟨86⟩) hpatch (by native_decide)]
          native_decide)
        (dogSelectorEqZero I hsz hnm 10 (by omega))
        (by simp)
  have h98 : RD code I g (initState cA gh bl σ σ₀ g A I) ⟨98⟩ [solcSelectorWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) ((((k + 5) + 5) + 5) + 5)
      ((((C + 22) + 22) + 22) + 22) := by
    simpa [selArmNextPc] using
      h87.selectorArmNotTaken (selNat := dogSelectorWord 2) (tgt := (⟨785⟩ : UInt256))
        (width := 2) (op := .PUSH2)
        (by
          change decode code (⟨87⟩ : UInt256) = some (.DUP1, .none)
          rw [dogDecodePatchedEqTemplate1405 (pc := ⟨87⟩) hpatch (by native_decide)]
          native_decide)
        (by
          change decode code (⟨88⟩ : UInt256) =
            some (.Push .PUSH4, some (dogSelectorWord 2, 4))
          rw [dogDecodePatchedEqTemplate1405 (pc := ⟨88⟩) hpatch (by native_decide)]
          native_decide)
        (by
          change decode code (⟨93⟩ : UInt256) = some (.EQ, .none)
          rw [dogDecodePatchedEqTemplate1405 (pc := ⟨93⟩) hpatch (by native_decide)]
          native_decide)
        (by decide)
        (by
          change decode code (⟨94⟩ : UInt256) =
            some (.Push .PUSH2, some ((⟨785⟩ : UInt256), 2))
          rw [dogDecodePatchedEqTemplate1405 (pc := ⟨94⟩) hpatch (by native_decide)]
          native_decide)
        (by
          change decode code (⟨97⟩ : UInt256) = some (.JUMPI, .none)
          rw [dogDecodePatchedEqTemplate1405 (pc := ⟨97⟩) hpatch (by native_decide)]
          native_decide)
        (dogSelectorEqZero I hsz hnm 2 (by omega))
        (by simp)
  have h109 : RD code I g (initState cA gh bl σ σ₀ g A I) ⟨109⟩ [solcSelectorWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ)
      (((((k + 5) + 5) + 5) + 5) + 5) (((((C + 22) + 22) + 22) + 22) + 22) := by
    simpa [selArmNextPc] using
      h98.selectorArmNotTaken (selNat := dogSelectorWord 0) (tgt := (⟨837⟩ : UInt256))
        (width := 2) (op := .PUSH2)
        (by
          change decode code (⟨98⟩ : UInt256) = some (.DUP1, .none)
          rw [dogDecodePatchedEqTemplate1405 (pc := ⟨98⟩) hpatch (by native_decide)]
          native_decide)
        (by
          change decode code (⟨99⟩ : UInt256) =
            some (.Push .PUSH4, some (dogSelectorWord 0, 4))
          rw [dogDecodePatchedEqTemplate1405 (pc := ⟨99⟩) hpatch (by native_decide)]
          native_decide)
        (by
          change decode code (⟨104⟩ : UInt256) = some (.EQ, .none)
          rw [dogDecodePatchedEqTemplate1405 (pc := ⟨104⟩) hpatch (by native_decide)]
          native_decide)
        (by decide)
        (by
          change decode code (⟨105⟩ : UInt256) =
            some (.Push .PUSH2, some ((⟨837⟩ : UInt256), 2))
          rw [dogDecodePatchedEqTemplate1405 (pc := ⟨105⟩) hpatch (by native_decide)]
          native_decide)
        (by
          change decode code (⟨108⟩ : UInt256) = some (.JUMPI, .none)
          rw [dogDecodePatchedEqTemplate1405 (pc := ⟨108⟩) hpatch (by native_decide)]
          native_decide)
        (dogSelectorEqZero I hsz hnm 0 (by omega))
        (by simp)
  exact dogJumpToDispatchRevert hpatch h109
    (by
      change decode code (⟨109⟩ : UInt256) = some (.Push .PUSH2, some (⟨267⟩, 2))
      rw [dogDecodePatchedEqTemplate1405 (pc := ⟨109⟩) hpatch (by native_decide)]
      native_decide)
    (by
      change decode code ((⟨109⟩ : UInt256) + UInt256.ofNat 3) = some (.JUMP, .none)
      rw [dogDecodePatchedEqTemplate1405
        (pc := (⟨109⟩ : UInt256) + UInt256.ofNat 3) hpatch (by native_decide)]
      native_decide)

theorem dogMiddleNoMatchRevert {v : DogImmutables} {code : ByteArray}
    {cA gh bl σ σ₀ A I} {g : Sat256} {k C : ℕ}
    (hpatch : patchRuntime dogBytecode (patches v) = some code)
    (hsz : 4 ≤ I.calldata.size)
    (hnm : ∀ i, i < 17 → (dogSelBytes i == I.calldata.extract 0 4) = false)
    (h : RD code I g (initState cA gh bl σ σ₀ g A I) ⟨114⟩ [solcSelectorWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    RDrev code g (initState cA gh bl σ σ₀ g A I) := by
  have h125 : RD code I g (initState cA gh bl σ σ₀ g A I) ⟨125⟩ [solcSelectorWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) (k + 5) (C + 22) := by
    simpa [selArmNextPc] using
      h.selectorArmNotTaken (selNat := dogSelectorWord 1) (tgt := (⟨504⟩ : UInt256))
        (width := 2) (op := .PUSH2)
        (by
          change decode code (⟨114⟩ : UInt256) = some (.DUP1, .none)
          rw [dogDecodePatchedEqTemplate1405 (pc := ⟨114⟩) hpatch (by native_decide)]
          native_decide)
        (by
          change decode code (⟨115⟩ : UInt256) =
            some (.Push .PUSH4, some (dogSelectorWord 1, 4))
          rw [dogDecodePatchedEqTemplate1405 (pc := ⟨115⟩) hpatch (by native_decide)]
          native_decide)
        (by
          change decode code (⟨120⟩ : UInt256) = some (.EQ, .none)
          rw [dogDecodePatchedEqTemplate1405 (pc := ⟨120⟩) hpatch (by native_decide)]
          native_decide)
        (by decide)
        (by
          change decode code (⟨121⟩ : UInt256) =
            some (.Push .PUSH2, some ((⟨504⟩ : UInt256), 2))
          rw [dogDecodePatchedEqTemplate1405 (pc := ⟨121⟩) hpatch (by native_decide)]
          native_decide)
        (by
          change decode code (⟨124⟩ : UInt256) = some (.JUMPI, .none)
          rw [dogDecodePatchedEqTemplate1405 (pc := ⟨124⟩) hpatch (by native_decide)]
          native_decide)
        (dogSelectorEqZero I hsz hnm 1 (by omega))
        (by simp)
  have h136 : RD code I g (initState cA gh bl σ σ₀ g A I) ⟨136⟩ [solcSelectorWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) ((k + 5) + 5)
      ((C + 22) + 22) := by
    simpa [selArmNextPc] using
      h125.selectorArmNotTaken (selNat := dogSelectorWord 16) (tgt := (⟨512⟩ : UInt256))
        (width := 2) (op := .PUSH2)
        (by
          change decode code (⟨125⟩ : UInt256) = some (.DUP1, .none)
          rw [dogDecodePatchedEqTemplate1405 (pc := ⟨125⟩) hpatch (by native_decide)]
          native_decide)
        (by
          change decode code (⟨126⟩ : UInt256) =
            some (.Push .PUSH4, some (dogSelectorWord 16, 4))
          rw [dogDecodePatchedEqTemplate1405 (pc := ⟨126⟩) hpatch (by native_decide)]
          native_decide)
        (by
          change decode code (⟨131⟩ : UInt256) = some (.EQ, .none)
          rw [dogDecodePatchedEqTemplate1405 (pc := ⟨131⟩) hpatch (by native_decide)]
          native_decide)
        (by decide)
        (by
          change decode code (⟨132⟩ : UInt256) =
            some (.Push .PUSH2, some ((⟨512⟩ : UInt256), 2))
          rw [dogDecodePatchedEqTemplate1405 (pc := ⟨132⟩) hpatch (by native_decide)]
          native_decide)
        (by
          change decode code (⟨135⟩ : UInt256) = some (.JUMPI, .none)
          rw [dogDecodePatchedEqTemplate1405 (pc := ⟨135⟩) hpatch (by native_decide)]
          native_decide)
        (dogSelectorEqZero I hsz hnm 16 (by omega))
        (by simp)
  have h147 : RD code I g (initState cA gh bl σ σ₀ g A I) ⟨147⟩ [solcSelectorWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) (((k + 5) + 5) + 5)
      (((C + 22) + 22) + 22) := by
    simpa [selArmNextPc] using
      h136.selectorArmNotTaken (selNat := dogSelectorWord 6) (tgt := (⟨550⟩ : UInt256))
        (width := 2) (op := .PUSH2)
        (by
          change decode code (⟨136⟩ : UInt256) = some (.DUP1, .none)
          rw [dogDecodePatchedEqTemplate1405 (pc := ⟨136⟩) hpatch (by native_decide)]
          native_decide)
        (by
          change decode code (⟨137⟩ : UInt256) =
            some (.Push .PUSH4, some (dogSelectorWord 6, 4))
          rw [dogDecodePatchedEqTemplate1405 (pc := ⟨137⟩) hpatch (by native_decide)]
          native_decide)
        (by
          change decode code (⟨142⟩ : UInt256) = some (.EQ, .none)
          rw [dogDecodePatchedEqTemplate1405 (pc := ⟨142⟩) hpatch (by native_decide)]
          native_decide)
        (by decide)
        (by
          change decode code (⟨143⟩ : UInt256) =
            some (.Push .PUSH2, some ((⟨550⟩ : UInt256), 2))
          rw [dogDecodePatchedEqTemplate1405 (pc := ⟨143⟩) hpatch (by native_decide)]
          native_decide)
        (by
          change decode code (⟨146⟩ : UInt256) = some (.JUMPI, .none)
          rw [dogDecodePatchedEqTemplate1405 (pc := ⟨146⟩) hpatch (by native_decide)]
          native_decide)
        (dogSelectorEqZero I hsz hnm 6 (by omega))
        (by simp)
  have h158 : RD code I g (initState cA gh bl σ σ₀ g A I) ⟨158⟩ [solcSelectorWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) ((((k + 5) + 5) + 5) + 5)
      ((((C + 22) + 22) + 22) + 22) := by
    simpa [selArmNextPc] using
      h147.selectorArmNotTaken (selNat := dogSelectorWord 9) (tgt := (⟨585⟩ : UInt256))
        (width := 2) (op := .PUSH2)
        (by
          change decode code (⟨147⟩ : UInt256) = some (.DUP1, .none)
          rw [dogDecodePatchedEqTemplate1405 (pc := ⟨147⟩) hpatch (by native_decide)]
          native_decide)
        (by
          change decode code (⟨148⟩ : UInt256) =
            some (.Push .PUSH4, some (dogSelectorWord 9, 4))
          rw [dogDecodePatchedEqTemplate1405 (pc := ⟨148⟩) hpatch (by native_decide)]
          native_decide)
        (by
          change decode code (⟨153⟩ : UInt256) = some (.EQ, .none)
          rw [dogDecodePatchedEqTemplate1405 (pc := ⟨153⟩) hpatch (by native_decide)]
          native_decide)
        (by decide)
        (by
          change decode code (⟨154⟩ : UInt256) =
            some (.Push .PUSH2, some ((⟨585⟩ : UInt256), 2))
          rw [dogDecodePatchedEqTemplate1405 (pc := ⟨154⟩) hpatch (by native_decide)]
          native_decide)
        (by
          change decode code (⟨157⟩ : UInt256) = some (.JUMPI, .none)
          rw [dogDecodePatchedEqTemplate1405 (pc := ⟨157⟩) hpatch (by native_decide)]
          native_decide)
        (dogSelectorEqZero I hsz hnm 9 (by omega))
        (by simp)
  exact dogJumpToDispatchRevert hpatch h158
    (by
      change decode code (⟨158⟩ : UInt256) = some (.Push .PUSH2, some (⟨267⟩, 2))
      rw [dogDecodePatchedEqTemplate1405 (pc := ⟨158⟩) hpatch (by native_decide)]
      native_decide)
    (by
      change decode code ((⟨158⟩ : UInt256) + UInt256.ofNat 3) = some (.JUMP, .none)
      rw [dogDecodePatchedEqTemplate1405
        (pc := (⟨158⟩ : UInt256) + UInt256.ofNat 3) hpatch (by native_decide)]
      native_decide)

theorem dogLowHighNoMatchRevert {v : DogImmutables} {code : ByteArray}
    {cA gh bl σ σ₀ A I} {g : Sat256} {k C : ℕ}
    (hpatch : patchRuntime dogBytecode (patches v) = some code)
    (hsz : 4 ≤ I.calldata.size)
    (hnm : ∀ i, i < 17 → (dogSelBytes i == I.calldata.extract 0 4) = false)
    (h : RD code I g (initState cA gh bl σ σ₀ g A I) ⟨174⟩ [solcSelectorWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    RDrev code g (initState cA gh bl σ σ₀ g A I) := by
  have h185 : RD code I g (initState cA gh bl σ σ₀ g A I) ⟨185⟩ [solcSelectorWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) (k + 5) (C + 22) := by
    simpa [selArmNextPc] using
      h.selectorArmNotTaken (selNat := dogSelectorWord 13) (tgt := (⟨394⟩ : UInt256))
        (width := 2) (op := .PUSH2)
        (by
          change decode code (⟨174⟩ : UInt256) = some (.DUP1, .none)
          rw [dogDecodePatchedEqTemplate1405 (pc := ⟨174⟩) hpatch (by native_decide)]
          native_decide)
        (by
          change decode code (⟨175⟩ : UInt256) =
            some (.Push .PUSH4, some (dogSelectorWord 13, 4))
          rw [dogDecodePatchedEqTemplate1405 (pc := ⟨175⟩) hpatch (by native_decide)]
          native_decide)
        (by
          change decode code (⟨180⟩ : UInt256) = some (.EQ, .none)
          rw [dogDecodePatchedEqTemplate1405 (pc := ⟨180⟩) hpatch (by native_decide)]
          native_decide)
        (by decide)
        (by
          change decode code (⟨181⟩ : UInt256) =
            some (.Push .PUSH2, some ((⟨394⟩ : UInt256), 2))
          rw [dogDecodePatchedEqTemplate1405 (pc := ⟨181⟩) hpatch (by native_decide)]
          native_decide)
        (by
          change decode code (⟨184⟩ : UInt256) = some (.JUMPI, .none)
          rw [dogDecodePatchedEqTemplate1405 (pc := ⟨184⟩) hpatch (by native_decide)]
          native_decide)
        (dogSelectorEqZero I hsz hnm 13 (by omega))
        (by simp)
  have h196 : RD code I g (initState cA gh bl σ σ₀ g A I) ⟨196⟩ [solcSelectorWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) ((k + 5) + 5)
      ((C + 22) + 22) := by
    simpa [selArmNextPc] using
      h185.selectorArmNotTaken (selNat := dogSelectorWord 3) (tgt := (⟨432⟩ : UInt256))
        (width := 2) (op := .PUSH2)
        (by
          change decode code (⟨185⟩ : UInt256) = some (.DUP1, .none)
          rw [dogDecodePatchedEqTemplate1405 (pc := ⟨185⟩) hpatch (by native_decide)]
          native_decide)
        (by
          change decode code (⟨186⟩ : UInt256) =
            some (.Push .PUSH4, some (dogSelectorWord 3, 4))
          rw [dogDecodePatchedEqTemplate1405 (pc := ⟨186⟩) hpatch (by native_decide)]
          native_decide)
        (by
          change decode code (⟨191⟩ : UInt256) = some (.EQ, .none)
          rw [dogDecodePatchedEqTemplate1405 (pc := ⟨191⟩) hpatch (by native_decide)]
          native_decide)
        (by decide)
        (by
          change decode code (⟨192⟩ : UInt256) =
            some (.Push .PUSH2, some ((⟨432⟩ : UInt256), 2))
          rw [dogDecodePatchedEqTemplate1405 (pc := ⟨192⟩) hpatch (by native_decide)]
          native_decide)
        (by
          change decode code (⟨195⟩ : UInt256) = some (.JUMPI, .none)
          rw [dogDecodePatchedEqTemplate1405 (pc := ⟨195⟩) hpatch (by native_decide)]
          native_decide)
        (dogSelectorEqZero I hsz hnm 3 (by omega))
        (by simp)
  have h207 : RD code I g (initState cA gh bl σ σ₀ g A I) ⟨207⟩ [solcSelectorWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) (((k + 5) + 5) + 5)
      (((C + 22) + 22) + 22) := by
    simpa [selArmNextPc] using
      h196.selectorArmNotTaken (selNat := dogSelectorWord 12) (tgt := (⟨440⟩ : UInt256))
        (width := 2) (op := .PUSH2)
        (by
          change decode code (⟨196⟩ : UInt256) = some (.DUP1, .none)
          rw [dogDecodePatchedEqTemplate1405 (pc := ⟨196⟩) hpatch (by native_decide)]
          native_decide)
        (by
          change decode code (⟨197⟩ : UInt256) =
            some (.Push .PUSH4, some (dogSelectorWord 12, 4))
          rw [dogDecodePatchedEqTemplate1405 (pc := ⟨197⟩) hpatch (by native_decide)]
          native_decide)
        (by
          change decode code (⟨202⟩ : UInt256) = some (.EQ, .none)
          rw [dogDecodePatchedEqTemplate1405 (pc := ⟨202⟩) hpatch (by native_decide)]
          native_decide)
        (by decide)
        (by
          change decode code (⟨203⟩ : UInt256) =
            some (.Push .PUSH2, some ((⟨440⟩ : UInt256), 2))
          rw [dogDecodePatchedEqTemplate1405 (pc := ⟨203⟩) hpatch (by native_decide)]
          native_decide)
        (by
          change decode code (⟨206⟩ : UInt256) = some (.JUMPI, .none)
          rw [dogDecodePatchedEqTemplate1405 (pc := ⟨206⟩) hpatch (by native_decide)]
          native_decide)
        (dogSelectorEqZero I hsz hnm 12 (by omega))
        (by simp)
  have h218 : RD code I g (initState cA gh bl σ σ₀ g A I) ⟨218⟩ [solcSelectorWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) ((((k + 5) + 5) + 5) + 5)
      ((((C + 22) + 22) + 22) + 22) := by
    simpa [selArmNextPc] using
      h207.selectorArmNotTaken (selNat := dogSelectorWord 5) (tgt := (⟨466⟩ : UInt256))
        (width := 2) (op := .PUSH2)
        (by
          change decode code (⟨207⟩ : UInt256) = some (.DUP1, .none)
          rw [dogDecodePatchedEqTemplate1405 (pc := ⟨207⟩) hpatch (by native_decide)]
          native_decide)
        (by
          change decode code (⟨208⟩ : UInt256) =
            some (.Push .PUSH4, some (dogSelectorWord 5, 4))
          rw [dogDecodePatchedEqTemplate1405 (pc := ⟨208⟩) hpatch (by native_decide)]
          native_decide)
        (by
          change decode code (⟨213⟩ : UInt256) = some (.EQ, .none)
          rw [dogDecodePatchedEqTemplate1405 (pc := ⟨213⟩) hpatch (by native_decide)]
          native_decide)
        (by decide)
        (by
          change decode code (⟨214⟩ : UInt256) =
            some (.Push .PUSH2, some ((⟨466⟩ : UInt256), 2))
          rw [dogDecodePatchedEqTemplate1405 (pc := ⟨214⟩) hpatch (by native_decide)]
          native_decide)
        (by
          change decode code (⟨217⟩ : UInt256) = some (.JUMPI, .none)
          rw [dogDecodePatchedEqTemplate1405 (pc := ⟨217⟩) hpatch (by native_decide)]
          native_decide)
        (dogSelectorEqZero I hsz hnm 5 (by omega))
        (by simp)
  exact dogJumpToDispatchRevert hpatch h218
    (by
      change decode code (⟨218⟩ : UInt256) = some (.Push .PUSH2, some (⟨267⟩, 2))
      rw [dogDecodePatchedEqTemplate1405 (pc := ⟨218⟩) hpatch (by native_decide)]
      native_decide)
    (by
      change decode code ((⟨218⟩ : UInt256) + UInt256.ofNat 3) = some (.JUMP, .none)
      rw [dogDecodePatchedEqTemplate1405
        (pc := (⟨218⟩ : UInt256) + UInt256.ofNat 3) hpatch (by native_decide)]
      native_decide)

theorem dogLowLowNoMatchRevert {v : DogImmutables} {code : ByteArray}
    {cA gh bl σ σ₀ A I} {g : Sat256} {k C : ℕ}
    (hpatch : patchRuntime dogBytecode (patches v) = some code)
    (hsz : 4 ≤ I.calldata.size)
    (hnm : ∀ i, i < 17 → (dogSelBytes i == I.calldata.extract 0 4) = false)
    (h : RD code I g (initState cA gh bl σ σ₀ g A I) ⟨223⟩ [solcSelectorWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    RDrev code g (initState cA gh bl σ σ₀ g A I) := by
  have h234 : RD code I g (initState cA gh bl σ σ₀ g A I) ⟨234⟩ [solcSelectorWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) (k + 5) (C + 22) := by
    simpa [selArmNextPc] using
      h.selectorArmNotTaken (selNat := dogSelectorWord 7) (tgt := (⟨272⟩ : UInt256))
        (width := 2) (op := .PUSH2)
        (by
          change decode code (⟨223⟩ : UInt256) = some (.DUP1, .none)
          rw [dogDecodePatchedEqTemplate1405 (pc := ⟨223⟩) hpatch (by native_decide)]
          native_decide)
        (by
          change decode code (⟨224⟩ : UInt256) =
            some (.Push .PUSH4, some (dogSelectorWord 7, 4))
          rw [dogDecodePatchedEqTemplate1405 (pc := ⟨224⟩) hpatch (by native_decide)]
          native_decide)
        (by
          change decode code (⟨229⟩ : UInt256) = some (.EQ, .none)
          rw [dogDecodePatchedEqTemplate1405 (pc := ⟨229⟩) hpatch (by native_decide)]
          native_decide)
        (by decide)
        (by
          change decode code (⟨230⟩ : UInt256) =
            some (.Push .PUSH2, some ((⟨272⟩ : UInt256), 2))
          rw [dogDecodePatchedEqTemplate1405 (pc := ⟨230⟩) hpatch (by native_decide)]
          native_decide)
        (by
          change decode code (⟨233⟩ : UInt256) = some (.JUMPI, .none)
          rw [dogDecodePatchedEqTemplate1405 (pc := ⟨233⟩) hpatch (by native_decide)]
          native_decide)
        (dogSelectorEqZero I hsz hnm 7 (by omega))
        (by simp)
  have h245 : RD code I g (initState cA gh bl σ σ₀ g A I) ⟨245⟩ [solcSelectorWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) ((k + 5) + 5)
      ((C + 22) + 22) := by
    simpa [selArmNextPc] using
      h234.selectorArmNotTaken (selNat := dogSelectorWord 8) (tgt := (⟨315⟩ : UInt256))
        (width := 2) (op := .PUSH2)
        (by
          change decode code (⟨234⟩ : UInt256) = some (.DUP1, .none)
          rw [dogDecodePatchedEqTemplate1405 (pc := ⟨234⟩) hpatch (by native_decide)]
          native_decide)
        (by
          change decode code (⟨235⟩ : UInt256) =
            some (.Push .PUSH4, some (dogSelectorWord 8, 4))
          rw [dogDecodePatchedEqTemplate1405 (pc := ⟨235⟩) hpatch (by native_decide)]
          native_decide)
        (by
          change decode code (⟨240⟩ : UInt256) = some (.EQ, .none)
          rw [dogDecodePatchedEqTemplate1405 (pc := ⟨240⟩) hpatch (by native_decide)]
          native_decide)
        (by decide)
        (by
          change decode code (⟨241⟩ : UInt256) =
            some (.Push .PUSH2, some ((⟨315⟩ : UInt256), 2))
          rw [dogDecodePatchedEqTemplate1405 (pc := ⟨241⟩) hpatch (by native_decide)]
          native_decide)
        (by
          change decode code (⟨244⟩ : UInt256) = some (.JUMPI, .none)
          rw [dogDecodePatchedEqTemplate1405 (pc := ⟨244⟩) hpatch (by native_decide)]
          native_decide)
        (dogSelectorEqZero I hsz hnm 8 (by omega))
        (by simp)
  have h256 : RD code I g (initState cA gh bl σ σ₀ g A I) ⟨256⟩ [solcSelectorWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) (((k + 5) + 5) + 5)
      (((C + 22) + 22) + 22) := by
    simpa [selArmNextPc] using
      h245.selectorArmNotTaken (selNat := dogSelectorWord 14) (tgt := (⟨350⟩ : UInt256))
        (width := 2) (op := .PUSH2)
        (by
          change decode code (⟨245⟩ : UInt256) = some (.DUP1, .none)
          rw [dogDecodePatchedEqTemplate1405 (pc := ⟨245⟩) hpatch (by native_decide)]
          native_decide)
        (by
          change decode code (⟨246⟩ : UInt256) =
            some (.Push .PUSH4, some (dogSelectorWord 14, 4))
          rw [dogDecodePatchedEqTemplate1405 (pc := ⟨246⟩) hpatch (by native_decide)]
          native_decide)
        (by
          change decode code (⟨251⟩ : UInt256) = some (.EQ, .none)
          rw [dogDecodePatchedEqTemplate1405 (pc := ⟨251⟩) hpatch (by native_decide)]
          native_decide)
        (by decide)
        (by
          change decode code (⟨252⟩ : UInt256) =
            some (.Push .PUSH2, some ((⟨350⟩ : UInt256), 2))
          rw [dogDecodePatchedEqTemplate1405 (pc := ⟨252⟩) hpatch (by native_decide)]
          native_decide)
        (by
          change decode code (⟨255⟩ : UInt256) = some (.JUMPI, .none)
          rw [dogDecodePatchedEqTemplate1405 (pc := ⟨255⟩) hpatch (by native_decide)]
          native_decide)
        (dogSelectorEqZero I hsz hnm 14 (by omega))
        (by simp)
  have h267 : RD code I g (initState cA gh bl σ σ₀ g A I) ⟨267⟩ [solcSelectorWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) ((((k + 5) + 5) + 5) + 5)
      ((((C + 22) + 22) + 22) + 22) := by
    simpa [selArmNextPc] using
      h256.selectorArmNotTaken (selNat := dogSelectorWord 15) (tgt := (⟨386⟩ : UInt256))
        (width := 2) (op := .PUSH2)
        (by
          change decode code (⟨256⟩ : UInt256) = some (.DUP1, .none)
          rw [dogDecodePatchedEqTemplate1405 (pc := ⟨256⟩) hpatch (by native_decide)]
          native_decide)
        (by
          change decode code (⟨257⟩ : UInt256) =
            some (.Push .PUSH4, some (dogSelectorWord 15, 4))
          rw [dogDecodePatchedEqTemplate1405 (pc := ⟨257⟩) hpatch (by native_decide)]
          native_decide)
        (by
          change decode code (⟨262⟩ : UInt256) = some (.EQ, .none)
          rw [dogDecodePatchedEqTemplate1405 (pc := ⟨262⟩) hpatch (by native_decide)]
          native_decide)
        (by decide)
        (by
          change decode code (⟨263⟩ : UInt256) =
            some (.Push .PUSH2, some ((⟨386⟩ : UInt256), 2))
          rw [dogDecodePatchedEqTemplate1405 (pc := ⟨263⟩) hpatch (by native_decide)]
          native_decide)
        (by
          change decode code (⟨266⟩ : UInt256) = some (.JUMPI, .none)
          rw [dogDecodePatchedEqTemplate1405 (pc := ⟨266⟩) hpatch (by native_decide)]
          native_decide)
        (dogSelectorEqZero I hsz hnm 15 (by omega))
        (by simp)
  exact dogDispatchRevertAt hpatch h267

theorem dogX_noMatch {v : DogImmutables} {code : ByteArray}
    {cA gh bl σ σ₀ A I} {g : Sat256}
    (hpatch : patchRuntime dogBytecode (patches v) = some code)
    (hcode : I.code = code) (hwv : I.weiValue = ⟨0⟩)
    (hsz : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hnm : ∀ i, i < 17 → (dogSelBytes i == I.calldata.extract 0 4) = false) :
    RDrev code g (initState cA gh bl σ σ₀ g A I) := by
  obtain ⟨k32, C32, h32⟩ :=
    dogReachSelector (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀)
      (A := A) (I := I) (g := g) hpatch hcode hwv hsz hsize
  have hrootTgt : armTgt code (⟨32⟩ : UInt256) = ⟨162⟩ := by
    dsimp [armTgt]
    rw [dogPushAtPatchedEqTemplate1405 (pc := selArmPushTgtPc (⟨32⟩ : UInt256))
      hpatch (by native_decide)]
    native_decide
  have hrootWidth : armTgtWidth code (⟨32⟩ : UInt256) = 2 := by
    dsimp [armTgtWidth]
    rw [dogPushAtPatchedEqTemplate1405 (pc := selArmPushTgtPc (⟨32⟩ : UInt256))
      hpatch (by native_decide)]
    native_decide
  have hhighTgt : armTgt code (⟨43⟩ : UInt256) = ⟨113⟩ := by
    dsimp [armTgt]
    rw [dogPushAtPatchedEqTemplate1405 (pc := selArmPushTgtPc (⟨43⟩ : UInt256))
      hpatch (by native_decide)]
    native_decide
  have hhighWidth : armTgtWidth code (⟨43⟩ : UInt256) = 2 := by
    dsimp [armTgtWidth]
    rw [dogPushAtPatchedEqTemplate1405 (pc := selArmPushTgtPc (⟨43⟩ : UInt256))
      hpatch (by native_decide)]
    native_decide
  have hlowTgt : armTgt code (⟨163⟩ : UInt256) = ⟨222⟩ := by
    dsimp [armTgt]
    rw [dogPushAtPatchedEqTemplate1405 (pc := selArmPushTgtPc (⟨163⟩ : UInt256))
      hpatch (by native_decide)]
    native_decide
  have hlowWidth : armTgtWidth code (⟨163⟩ : UInt256) = 2 := by
    dsimp [armTgtWidth]
    rw [dogPushAtPatchedEqTemplate1405 (pc := selArmPushTgtPc (⟨163⟩ : UInt256))
      hpatch (by native_decide)]
    native_decide
  by_cases hroot :
      UInt256.gt (armSelNat code (⟨32⟩ : UInt256)) (solcSelectorWord I) = ⟨0⟩
  · have h43 : RD code I g (initState cA gh bl σ σ₀ g A I) ⟨43⟩
        [solcSelectorWord I] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty
        (cA, σ) (k32 + 5) (C32 + 22) := by
      simpa [selArmNextPc, hrootWidth] using
        RD.selectorSplitNotTakenAuto h32 (dogRootSplitWellFormed hpatch) hroot (by simp)
    by_cases hhigh :
        UInt256.gt (armSelNat code (⟨43⟩ : UInt256)) (solcSelectorWord I) = ⟨0⟩
    · have h54 : RD code I g (initState cA gh bl σ σ₀ g A I) ⟨54⟩
          [solcSelectorWord I] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty
          (cA, σ) (k32 + 5 + 5) (C32 + 22 + 22) := by
        simpa [selArmNextPc, hhighWidth] using
          RD.selectorSplitNotTakenAuto h43 (dogHighSplitWellFormed hpatch) hhigh (by simp)
      exact dogVeryHighNoMatchRevert hpatch hsz hnm h54
    · have h113 : RD code I g (initState cA gh bl σ σ₀ g A I) ⟨113⟩
          [solcSelectorWord I] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty
          (cA, σ) (k32 + 5 + 5) (C32 + 22 + 22) := by
        simpa [hhighTgt] using
          RD.selectorSplitTakenAuto h43 (dogHighSplitWellFormed hpatch) hhigh
            (by
              rw [hhighTgt]
              exact dogPatchedDJumpPrefix1405 ⟨113⟩ hpatch (by native_decide))
            (by simp)
      have h114 := h113.jumpdest
        (by
          rw [dogDecodePatchedEqTemplate1405 (pc := ⟨113⟩) hpatch (by native_decide)]
          native_decide)
        (by simp only [List.length_singleton]; omega)
      exact dogMiddleNoMatchRevert hpatch hsz hnm h114
  · have h162 : RD code I g (initState cA gh bl σ σ₀ g A I) ⟨162⟩
        [solcSelectorWord I] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty
        (cA, σ) (k32 + 5) (C32 + 22) := by
      simpa [hrootTgt] using
        RD.selectorSplitTakenAuto h32 (dogRootSplitWellFormed hpatch) hroot
          (by
            rw [hrootTgt]
            exact dogPatchedDJumpPrefix1405 ⟨162⟩ hpatch (by native_decide))
          (by simp)
    have h163 : RD code I g (initState cA gh bl σ σ₀ g A I) ⟨163⟩
        [solcSelectorWord I] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty
        (cA, σ) (k32 + 5 + 1) (C32 + 22 + 1) := by
      simpa using
        h162.jumpdest
          (by
            rw [dogDecodePatchedEqTemplate1405 (pc := ⟨162⟩) hpatch (by native_decide)]
            native_decide)
          (by simp only [List.length_singleton]; omega)
    by_cases hlow :
        UInt256.gt (armSelNat code (⟨163⟩ : UInt256)) (solcSelectorWord I) = ⟨0⟩
    · have h174 : RD code I g (initState cA gh bl σ σ₀ g A I) ⟨174⟩
          [solcSelectorWord I] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty
          (cA, σ) (k32 + 5 + 1 + 5) (C32 + 22 + 1 + 22) := by
        simpa [selArmNextPc, hlowWidth] using
          RD.selectorSplitNotTakenAuto h163 (dogLowSplitWellFormed hpatch) hlow (by simp)
      exact dogLowHighNoMatchRevert hpatch hsz hnm h174
    · have h222 : RD code I g (initState cA gh bl σ σ₀ g A I) ⟨222⟩
          [solcSelectorWord I] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty
          (cA, σ) (k32 + 5 + 1 + 5) (C32 + 22 + 1 + 22) := by
        simpa [hlowTgt] using
          RD.selectorSplitTakenAuto h163 (dogLowSplitWellFormed hpatch) hlow
            (by
              rw [hlowTgt]
              exact dogPatchedDJumpPrefix1405 ⟨222⟩ hpatch (by native_decide))
            (by simp)
      have h223 := h222.jumpdest
        (by
          rw [dogDecodePatchedEqTemplate1405 (pc := ⟨222⟩) hpatch (by native_decide)]
          native_decide)
        (by simp only [List.length_singleton]; omega)
      exact dogLowLowNoMatchRevert hpatch hsz hnm h223

theorem dogNonPayable {v : DogImmutables} {code : ByteArray}
    {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256}
    (_hpatch : patchRuntime dogBytecode (patches v) = some code)
    (_hcode : I.code = code) (_hwv : I.weiValue ≠ ⟨0⟩) :
    runtimeEquivalenceFor (config v) (contract v) cA gh bl σ_evm σ_solm σ₀ g A I := by
  exact (dogX_callvalue_ne (g := Sat256.ofUInt256 g) _hpatch _hcode _hwv).reEquivElim
    _hcode fun _ _ hrev => by
      by_cases hdisp : dispatchMsg (contract v) I.calldata = none
      · exact reEquiv_noDispatch hdisp hrev
      · obtain ⟨t, ht⟩ := Option.ne_none_iff_exists'.mp hdisp
        have htmem : t ∈ (contract v).transitions := by
          rw [dispatchMsg_eq_dispatchList (contract v) I.calldata (by rfl)] at ht
          exact dispatchList_some_mem ht
        by_cases hdec : decodeCalldataWithMode (config v).abiDecodeMode
            (t.params.map Param.name) (transitionSignature t).paramTypes I.calldata = none
        · exact reEquiv_decodingFailed ht hdec hrev
        · obtain ⟨callargs, hca⟩ := Option.ne_none_iff_exists'.mp hdec
          exact reEquiv_execution ht hca
            (dogBodyReverts_nonPayable v t htmem
              (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)
              callargs (by simp only [initState]; exact _hwv))
            (by rw [hrev]; exact execResultsEquiv.revert rfl rfl)

theorem dogNoDispatch {v : DogImmutables} {code : ByteArray}
    {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256}
    (_hpatch : patchRuntime dogBytecode (patches v) = some code)
    (_hcode : I.code = code)
    (_hsize : I.calldata.size < UInt256.size)
    (_hperm : I.perm = true)
    (_hwv : I.weiValue = ⟨0⟩)
    (_hnm : ∀ i, i < 17 → (dogSelBytes i == I.calldata.extract 0 4) = false)
    (_hAccounts : accountMapEquiv σ_evm σ_solm) :
    runtimeEquivalenceFor (config v) (contract v) cA gh bl σ_evm σ_solm σ₀ g A I := by
  by_cases hshort : I.calldata.size < 4
  · exact (dogX_short (g := Sat256.ofUInt256 g) _hpatch _hcode _hwv hshort)
      |>.reEquivNoDispatch _hcode (dogDispatch_none_short v hshort)
  · have _hsz : 4 ≤ I.calldata.size := by omega
    exact (dogX_noMatch (g := Sat256.ofUInt256 g) _hpatch _hcode _hwv _hsz _hsize _hnm)
      |>.reEquivNoDispatch _hcode (dogDispatch_none_nomatch v _hnm)

end Benchmarks.Dss.Dog
