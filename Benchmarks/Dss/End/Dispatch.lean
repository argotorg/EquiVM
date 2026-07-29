import Benchmarks.Dss.End.Trusted

/-!
# MakerDAO/Sky DSS End dispatcher proof boundary
-/

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

set_option maxRecDepth 2000000
set_option maxHeartbeats 0

namespace Benchmarks.Dss.End

attribute [local simp]
  endWardsSelectorBytes
  endVatSelectorBytes
  endCatSelectorBytes
  endDogSelectorBytes
  endVowSelectorBytes
  endPotSelectorBytes
  endSpotSelectorBytes
  endCureSelectorBytes
  endLiveSelectorBytes
  endWhenSelectorBytes
  endWaitSelectorBytes
  endDebtSelectorBytes
  endTagSelectorBytes
  endGapSelectorBytes
  endArtSelectorBytes
  endFixSelectorBytes
  endBagSelectorBytes
  endOutSelectorBytes
  endRelySelectorBytes
  endDenySelectorBytes
  endFileAddressSelectorBytes
  endFileUintSelectorBytes
  endCageSelectorBytes
  endCageIlkSelectorBytes
  endSnipSelectorBytes
  endSkipSelectorBytes
  endSkimSelectorBytes
  endFreeSelectorBytes
  endThawSelectorBytes
  endFlowSelectorBytes
  endPackSelectorBytes
  endCashSelectorBytes

theorem endDispatchWards {I : ExecutionEnv}
    (hsel : selIs I (selectorOf wardsTransition)) :
    dispatchMsg contract I.calldata = some wardsTransition := by
  have hsel' : selIs I (selectorBytes 0xbf 0x35 0x3d 0xbb) := by
    simpa [endWardsSelectorBytes] using hsel
  have hcd : I.calldata.extract 0 4 = selectorBytes 0xbf 0x35 0x3d 0xbb :=
    (byteArray_eq_of_beq hsel').symm
  rw [dispatchMsg_eq_dispatchList contract I.calldata (by rfl) (by rfl)]
  change dispatchList transitions I.calldata = some wardsTransition
  unfold transitions
  simp [dispatchList, hcd]
  native_decide

theorem endDispatchVat {I : ExecutionEnv}
    (hsel : selIs I (selectorOf vatTransition)) :
    dispatchMsg contract I.calldata = some vatTransition := by
  have hsel' : selIs I (selectorBytes 0x36 0x56 0x9e 0x77) := by
    simpa [endVatSelectorBytes] using hsel
  have hcd : I.calldata.extract 0 4 = selectorBytes 0x36 0x56 0x9e 0x77 :=
    (byteArray_eq_of_beq hsel').symm
  rw [dispatchMsg_eq_dispatchList contract I.calldata (by rfl) (by rfl)]
  change dispatchList transitions I.calldata = some vatTransition
  unfold transitions
  simp [dispatchList, hcd]
  native_decide

theorem endDispatchCat {I : ExecutionEnv}
    (hsel : selIs I (selectorOf catTransition)) :
    dispatchMsg contract I.calldata = some catTransition := by
  have hsel' : selIs I (selectorBytes 0xe4 0x88 0x18 0x13) := by
    simpa [endCatSelectorBytes] using hsel
  have hcd : I.calldata.extract 0 4 = selectorBytes 0xe4 0x88 0x18 0x13 :=
    (byteArray_eq_of_beq hsel').symm
  rw [dispatchMsg_eq_dispatchList contract I.calldata (by rfl) (by rfl)]
  change dispatchList transitions I.calldata = some catTransition
  unfold transitions
  simp [dispatchList, hcd]
  native_decide

theorem endDispatchDog {I : ExecutionEnv}
    (hsel : selIs I (selectorOf dogTransition)) :
    dispatchMsg contract I.calldata = some dogTransition := by
  have hsel' : selIs I (selectorBytes 0xc3 0xb3 0xad 0x7f) := by
    simpa [endDogSelectorBytes] using hsel
  have hcd : I.calldata.extract 0 4 = selectorBytes 0xc3 0xb3 0xad 0x7f :=
    (byteArray_eq_of_beq hsel').symm
  rw [dispatchMsg_eq_dispatchList contract I.calldata (by rfl) (by rfl)]
  change dispatchList transitions I.calldata = some dogTransition
  unfold transitions
  simp [dispatchList, hcd]
  native_decide

theorem endDispatchVow {I : ExecutionEnv}
    (hsel : selIs I (selectorOf vowTransition)) :
    dispatchMsg contract I.calldata = some vowTransition := by
  have hsel' : selIs I (selectorBytes 0x62 0x6c 0xb3 0xc5) := by
    simpa [endVowSelectorBytes] using hsel
  have hcd : I.calldata.extract 0 4 = selectorBytes 0x62 0x6c 0xb3 0xc5 :=
    (byteArray_eq_of_beq hsel').symm
  rw [dispatchMsg_eq_dispatchList contract I.calldata (by rfl) (by rfl)]
  change dispatchList transitions I.calldata = some vowTransition
  unfold transitions
  simp [dispatchList, hcd]
  native_decide

theorem endDispatchPot {I : ExecutionEnv}
    (hsel : selIs I (selectorOf potTransition)) :
    dispatchMsg contract I.calldata = some potTransition := by
  have hsel' : selIs I (selectorBytes 0x4b 0xa2 0x36 0x3a) := by
    simpa [endPotSelectorBytes] using hsel
  have hcd : I.calldata.extract 0 4 = selectorBytes 0x4b 0xa2 0x36 0x3a :=
    (byteArray_eq_of_beq hsel').symm
  rw [dispatchMsg_eq_dispatchList contract I.calldata (by rfl) (by rfl)]
  change dispatchList transitions I.calldata = some potTransition
  unfold transitions
  simp [dispatchList, hcd]
  native_decide

theorem endDispatchSpot {I : ExecutionEnv}
    (hsel : selIs I (selectorOf spotTransition)) :
    dispatchMsg contract I.calldata = some spotTransition := by
  have hsel' : selIs I (selectorBytes 0x6f 0x26 0x5b 0x93) := by
    simpa [endSpotSelectorBytes] using hsel
  have hcd : I.calldata.extract 0 4 = selectorBytes 0x6f 0x26 0x5b 0x93 :=
    (byteArray_eq_of_beq hsel').symm
  rw [dispatchMsg_eq_dispatchList contract I.calldata (by rfl) (by rfl)]
  change dispatchList transitions I.calldata = some spotTransition
  unfold transitions
  simp [dispatchList, hcd]
  native_decide

theorem endDispatchCure {I : ExecutionEnv}
    (hsel : selIs I (selectorOf cureTransition)) :
    dispatchMsg contract I.calldata = some cureTransition := by
  have hsel' : selIs I (selectorBytes 0x84 0x07 0x82 0xed) := by
    simpa [endCureSelectorBytes] using hsel
  have hcd : I.calldata.extract 0 4 = selectorBytes 0x84 0x07 0x82 0xed :=
    (byteArray_eq_of_beq hsel').symm
  rw [dispatchMsg_eq_dispatchList contract I.calldata (by rfl) (by rfl)]
  change dispatchList transitions I.calldata = some cureTransition
  unfold transitions
  simp [dispatchList, hcd]
  native_decide

theorem endDispatchLive {I : ExecutionEnv}
    (hsel : selIs I (selectorOf liveTransition)) :
    dispatchMsg contract I.calldata = some liveTransition := by
  have hsel' : selIs I (selectorBytes 0x95 0x7a 0xa5 0x8c) := by
    simpa [endLiveSelectorBytes] using hsel
  have hcd : I.calldata.extract 0 4 = selectorBytes 0x95 0x7a 0xa5 0x8c :=
    (byteArray_eq_of_beq hsel').symm
  rw [dispatchMsg_eq_dispatchList contract I.calldata (by rfl) (by rfl)]
  change dispatchList transitions I.calldata = some liveTransition
  unfold transitions
  simp [dispatchList, hcd]
  native_decide

theorem endDispatchWhen {I : ExecutionEnv}
    (hsel : selIs I (selectorOf whenTransition)) :
    dispatchMsg contract I.calldata = some whenTransition := by
  have hsel' : selIs I (selectorBytes 0xe2 0xb0 0xca 0xef) := by
    simpa [endWhenSelectorBytes] using hsel
  have hcd : I.calldata.extract 0 4 = selectorBytes 0xe2 0xb0 0xca 0xef :=
    (byteArray_eq_of_beq hsel').symm
  rw [dispatchMsg_eq_dispatchList contract I.calldata (by rfl) (by rfl)]
  change dispatchList transitions I.calldata = some whenTransition
  unfold transitions
  simp [dispatchList, hcd]
  native_decide

theorem endDispatchWait {I : ExecutionEnv}
    (hsel : selIs I (selectorOf waitTransition)) :
    dispatchMsg contract I.calldata = some waitTransition := by
  have hsel' : selIs I (selectorBytes 0x64 0xbd 0x70 0x13) := by
    simpa [endWaitSelectorBytes] using hsel
  have hcd : I.calldata.extract 0 4 = selectorBytes 0x64 0xbd 0x70 0x13 :=
    (byteArray_eq_of_beq hsel').symm
  rw [dispatchMsg_eq_dispatchList contract I.calldata (by rfl) (by rfl)]
  change dispatchList transitions I.calldata = some waitTransition
  unfold transitions
  simp [dispatchList, hcd]
  native_decide

theorem endDispatchDebt {I : ExecutionEnv}
    (hsel : selIs I (selectorOf debtTransition)) :
    dispatchMsg contract I.calldata = some debtTransition := by
  have hsel' : selIs I debtSelector := by
    simpa [endDebtSelectorBytes] using hsel
  have hcd : I.calldata.extract 0 4 = debtSelector := (byteArray_eq_of_beq hsel').symm
  rw [dispatchMsg_eq_dispatchList contract I.calldata (by rfl) (by rfl)]
  change dispatchList transitions I.calldata = some debtTransition
  unfold transitions
  simp [dispatchList, hcd, debtSelector, selectorBytes]
  native_decide

theorem endDispatchTag {I : ExecutionEnv}
    (hsel : selIs I (selectorOf tagTransition)) :
    dispatchMsg contract I.calldata = some tagTransition := by
  have hsel' : selIs I (selectorBytes 0xee 0x64 0x47 0xb5) := by
    simpa [endTagSelectorBytes] using hsel
  have hcd : I.calldata.extract 0 4 = selectorBytes 0xee 0x64 0x47 0xb5 :=
    (byteArray_eq_of_beq hsel').symm
  rw [dispatchMsg_eq_dispatchList contract I.calldata (by rfl) (by rfl)]
  change dispatchList transitions I.calldata = some tagTransition
  unfold transitions
  simp [dispatchList, hcd]
  native_decide

theorem endDispatchGap {I : ExecutionEnv}
    (hsel : selIs I (selectorOf gapTransition)) :
    dispatchMsg contract I.calldata = some gapTransition := by
  have hsel' : selIs I (selectorBytes 0xe6 0xee 0x62 0xaa) := by
    simpa [endGapSelectorBytes] using hsel
  have hcd : I.calldata.extract 0 4 = selectorBytes 0xe6 0xee 0x62 0xaa :=
    (byteArray_eq_of_beq hsel').symm
  rw [dispatchMsg_eq_dispatchList contract I.calldata (by rfl) (by rfl)]
  change dispatchList transitions I.calldata = some gapTransition
  unfold transitions
  simp [dispatchList, hcd]
  native_decide

theorem endDispatchArt {I : ExecutionEnv}
    (hsel : selIs I (selectorOf ArtTransition)) :
    dispatchMsg contract I.calldata = some ArtTransition := by
  have hsel' : selIs I (selectorBytes 0xe1 0x34 0x0a 0x3d) := by
    simpa [endArtSelectorBytes] using hsel
  have hcd : I.calldata.extract 0 4 = selectorBytes 0xe1 0x34 0x0a 0x3d :=
    (byteArray_eq_of_beq hsel').symm
  rw [dispatchMsg_eq_dispatchList contract I.calldata (by rfl) (by rfl)]
  change dispatchList transitions I.calldata = some ArtTransition
  unfold transitions
  simp [dispatchList, hcd]
  native_decide

theorem endDispatchFix {I : ExecutionEnv}
    (hsel : selIs I (selectorOf fixTransition)) :
    dispatchMsg contract I.calldata = some fixTransition := by
  have hsel' : selIs I (selectorBytes 0x63 0xfa 0xd8 0x5e) := by
    simpa [endFixSelectorBytes] using hsel
  have hcd : I.calldata.extract 0 4 = selectorBytes 0x63 0xfa 0xd8 0x5e :=
    (byteArray_eq_of_beq hsel').symm
  rw [dispatchMsg_eq_dispatchList contract I.calldata (by rfl) (by rfl)]
  change dispatchList transitions I.calldata = some fixTransition
  unfold transitions
  simp [dispatchList, hcd]
  native_decide

theorem endDispatchBag {I : ExecutionEnv}
    (hsel : selIs I (selectorOf bagTransition)) :
    dispatchMsg contract I.calldata = some bagTransition := by
  have hsel' : selIs I (selectorBytes 0x92 0x55 0xf8 0x09) := by
    simpa [endBagSelectorBytes] using hsel
  have hcd : I.calldata.extract 0 4 = selectorBytes 0x92 0x55 0xf8 0x09 :=
    (byteArray_eq_of_beq hsel').symm
  rw [dispatchMsg_eq_dispatchList contract I.calldata (by rfl) (by rfl)]
  change dispatchList transitions I.calldata = some bagTransition
  unfold transitions
  simp [dispatchList, hcd]
  native_decide

theorem endDispatchOut {I : ExecutionEnv}
    (hsel : selIs I (selectorOf outTransition)) :
    dispatchMsg contract I.calldata = some outTransition := by
  have hsel' : selIs I (selectorBytes 0xc9 0x39 0xeb 0xfc) := by
    simpa [endOutSelectorBytes] using hsel
  have hcd : I.calldata.extract 0 4 = selectorBytes 0xc9 0x39 0xeb 0xfc :=
    (byteArray_eq_of_beq hsel').symm
  rw [dispatchMsg_eq_dispatchList contract I.calldata (by rfl) (by rfl)]
  change dispatchList transitions I.calldata = some outTransition
  unfold transitions
  simp [dispatchList, hcd]
  native_decide

theorem endDispatchRely {I : ExecutionEnv}
    (hsel : selIs I (selectorOf relyTransition)) :
    dispatchMsg contract I.calldata = some relyTransition := by
  have hsel' : selIs I (selectorBytes 0x65 0xfa 0xe3 0x5e) := by
    simpa [endRelySelectorBytes] using hsel
  have hcd : I.calldata.extract 0 4 = selectorBytes 0x65 0xfa 0xe3 0x5e :=
    (byteArray_eq_of_beq hsel').symm
  rw [dispatchMsg_eq_dispatchList contract I.calldata (by rfl) (by rfl)]
  change dispatchList transitions I.calldata = some relyTransition
  unfold transitions
  simp [dispatchList, hcd]
  native_decide

theorem endDispatchDeny {I : ExecutionEnv}
    (hsel : selIs I (selectorOf denyTransition)) :
    dispatchMsg contract I.calldata = some denyTransition := by
  have hsel' : selIs I (selectorBytes 0x9c 0x52 0xa7 0xf1) := by
    simpa [endDenySelectorBytes] using hsel
  have hcd : I.calldata.extract 0 4 = selectorBytes 0x9c 0x52 0xa7 0xf1 :=
    (byteArray_eq_of_beq hsel').symm
  rw [dispatchMsg_eq_dispatchList contract I.calldata (by rfl) (by rfl)]
  change dispatchList transitions I.calldata = some denyTransition
  unfold transitions
  simp [dispatchList, hcd]
  native_decide

theorem endDispatchFileUint {I : ExecutionEnv}
    (hsel : selIs I (selectorOf fileUintTransition)) :
    dispatchMsg contract I.calldata = some fileUintTransition := by
  have hsel' : selIs I (selectorBytes 0x29 0xae 0x81 0x14) := by
    simpa [endFileUintSelectorBytes] using hsel
  have hcd : I.calldata.extract 0 4 = selectorBytes 0x29 0xae 0x81 0x14 :=
    (byteArray_eq_of_beq hsel').symm
  rw [dispatchMsg_eq_dispatchList contract I.calldata (by rfl) (by rfl)]
  change dispatchList transitions I.calldata = some fileUintTransition
  unfold transitions
  simp [dispatchList, hcd]
  native_decide

theorem endDispatchFileAddress {I : ExecutionEnv}
    (hsel : selIs I (selectorOf fileAddressTransition)) :
    dispatchMsg contract I.calldata = some fileAddressTransition := by
  have hsel' : selIs I (selectorBytes 0xd4 0xe8 0xbe 0x83) := by
    simpa [endFileAddressSelectorBytes] using hsel
  have hcd : I.calldata.extract 0 4 = selectorBytes 0xd4 0xe8 0xbe 0x83 :=
    (byteArray_eq_of_beq hsel').symm
  rw [dispatchMsg_eq_dispatchList contract I.calldata (by rfl) (by rfl)]
  change dispatchList transitions I.calldata = some fileAddressTransition
  unfold transitions
  simp [dispatchList, hcd]
  native_decide

theorem endDispatchCageIlk {I : ExecutionEnv}
    (hsel : selIs I (selectorOf cageIlkTransition)) :
    dispatchMsg contract I.calldata = some cageIlkTransition := by
  have hsel' : selIs I (selectorBytes 0xe2 0x70 0x2f 0xdc) := by
    simpa [endCageIlkSelectorBytes] using hsel
  have hcd : I.calldata.extract 0 4 = selectorBytes 0xe2 0x70 0x2f 0xdc :=
    (byteArray_eq_of_beq hsel').symm
  rw [dispatchMsg_eq_dispatchList contract I.calldata (by rfl) (by rfl)]
  change dispatchList transitions I.calldata = some cageIlkTransition
  unfold transitions
  simp [dispatchList, hcd]
  native_decide

theorem endDispatchSnip {I : ExecutionEnv}
    (hsel : selIs I (selectorOf snipTransition)) :
    dispatchMsg contract I.calldata = some snipTransition := by
  have hsel' : selIs I (selectorBytes 0x38 0xc6 0xde 0x40) := by
    simpa [endSnipSelectorBytes] using hsel
  have hcd : I.calldata.extract 0 4 = selectorBytes 0x38 0xc6 0xde 0x40 :=
    (byteArray_eq_of_beq hsel').symm
  rw [dispatchMsg_eq_dispatchList contract I.calldata (by rfl) (by rfl)]
  change dispatchList transitions I.calldata = some snipTransition
  unfold transitions
  simp [dispatchList, hcd]
  native_decide

theorem endDispatchSkip {I : ExecutionEnv}
    (hsel : selIs I (selectorOf skipTransition)) :
    dispatchMsg contract I.calldata = some skipTransition := by
  have hsel' : selIs I (selectorBytes 0x50 0x3e 0xcf 0x06) := by
    simpa [endSkipSelectorBytes] using hsel
  have hcd : I.calldata.extract 0 4 = selectorBytes 0x50 0x3e 0xcf 0x06 :=
    (byteArray_eq_of_beq hsel').symm
  rw [dispatchMsg_eq_dispatchList contract I.calldata (by rfl) (by rfl)]
  change dispatchList transitions I.calldata = some skipTransition
  unfold transitions
  simp [dispatchList, hcd]
  native_decide

theorem endDispatchSkim {I : ExecutionEnv}
    (hsel : selIs I (selectorOf skimTransition)) :
    dispatchMsg contract I.calldata = some skimTransition := by
  have hsel' : selIs I (selectorBytes 0x89 0xea 0x45 0xd3) := by
    simpa [endSkimSelectorBytes] using hsel
  have hcd : I.calldata.extract 0 4 = selectorBytes 0x89 0xea 0x45 0xd3 :=
    (byteArray_eq_of_beq hsel').symm
  rw [dispatchMsg_eq_dispatchList contract I.calldata (by rfl) (by rfl)]
  change dispatchList transitions I.calldata = some skimTransition
  unfold transitions
  simp [dispatchList, hcd]
  native_decide

theorem endDispatchThaw {I : ExecutionEnv}
    (hsel : selIs I (selectorOf thawTransition)) :
    dispatchMsg contract I.calldata = some thawTransition := by
  have hsel' : selIs I (selectorBytes 0x59 0x20 0x37 0x5c) := by
    simpa [endThawSelectorBytes] using hsel
  have hcd : I.calldata.extract 0 4 = selectorBytes 0x59 0x20 0x37 0x5c :=
    (byteArray_eq_of_beq hsel').symm
  rw [dispatchMsg_eq_dispatchList contract I.calldata (by rfl) (by rfl)]
  change dispatchList transitions I.calldata = some thawTransition
  unfold transitions
  simp [dispatchList, hcd]
  native_decide

theorem endDispatchFlow {I : ExecutionEnv}
    (hsel : selIs I (selectorOf flowTransition)) :
    dispatchMsg contract I.calldata = some flowTransition := by
  have hsel' : selIs I (selectorBytes 0x4a 0x10 0xea 0xa6) := by
    simpa [endFlowSelectorBytes] using hsel
  have hcd : I.calldata.extract 0 4 = selectorBytes 0x4a 0x10 0xea 0xa6 :=
    (byteArray_eq_of_beq hsel').symm
  rw [dispatchMsg_eq_dispatchList contract I.calldata (by rfl) (by rfl)]
  change dispatchList transitions I.calldata = some flowTransition
  unfold transitions
  simp [dispatchList, hcd]
  native_decide

theorem endDispatchCash {I : ExecutionEnv}
    (hsel : selIs I (selectorOf cashTransition)) :
    dispatchMsg contract I.calldata = some cashTransition := by
  have hsel' : selIs I (selectorBytes 0xfe 0x85 0x07 0xc6) := by
    simpa [endCashSelectorBytes] using hsel
  have hcd : I.calldata.extract 0 4 = selectorBytes 0xfe 0x85 0x07 0xc6 :=
    (byteArray_eq_of_beq hsel').symm
  rw [dispatchMsg_eq_dispatchList contract I.calldata (by rfl) (by rfl)]
  change dispatchList transitions I.calldata = some cashTransition
  unfold transitions
  simp [dispatchList, hcd]
  native_decide

theorem endSelWord_eq_of_beq (I : ExecutionEnv) (hsz : 4 ≤ I.calldata.size)
    (c0 c1 c2 c3 : UInt8) (sel : UInt256)
    (hsel : (fromBytesBigEndian [c0, c1, c2, c3] : ℕ) = sel.toNat)
    (hmatch : ((⟨#[c0, c1, c2, c3]⟩ : ByteArray) == I.calldata.extract 0 4) = true) :
    endSelWord I = sel := by
  simpa [endSelWord, solcSelectorWord] using
    solcSelectorWord_eq_of_beq I hsz c0 c1 c2 c3 sel hsel hmatch

/-! ## No-dispatch selector facts -/

def endSelBytes : ℕ → ByteArray
  | 0 => selectorBytes 0xbf 0x35 0x3d 0xbb
  | 1 => selectorBytes 0x36 0x56 0x9e 0x77
  | 2 => selectorBytes 0xe4 0x88 0x18 0x13
  | 3 => selectorBytes 0xc3 0xb3 0xad 0x7f
  | 4 => selectorBytes 0x62 0x6c 0xb3 0xc5
  | 5 => selectorBytes 0x4b 0xa2 0x36 0x3a
  | 6 => selectorBytes 0x6f 0x26 0x5b 0x93
  | 7 => selectorBytes 0x84 0x07 0x82 0xed
  | 8 => selectorBytes 0x95 0x7a 0xa5 0x8c
  | 9 => selectorBytes 0xe2 0xb0 0xca 0xef
  | 10 => selectorBytes 0x64 0xbd 0x70 0x13
  | 11 => debtSelector
  | 12 => selectorBytes 0xee 0x64 0x47 0xb5
  | 13 => selectorBytes 0xe6 0xee 0x62 0xaa
  | 14 => selectorBytes 0xe1 0x34 0x0a 0x3d
  | 15 => selectorBytes 0x63 0xfa 0xd8 0x5e
  | 16 => selectorBytes 0x92 0x55 0xf8 0x09
  | 17 => selectorBytes 0xc9 0x39 0xeb 0xfc
  | 18 => selectorBytes 0x65 0xfa 0xe3 0x5e
  | 19 => selectorBytes 0x9c 0x52 0xa7 0xf1
  | 20 => selectorBytes 0xd4 0xe8 0xbe 0x83
  | 21 => selectorBytes 0x29 0xae 0x81 0x14
  | 22 => selectorBytes 0x69 0x24 0x50 0x09
  | 23 => selectorBytes 0xe2 0x70 0x2f 0xdc
  | 24 => selectorBytes 0x38 0xc6 0xde 0x40
  | 25 => selectorBytes 0x50 0x3e 0xcf 0x06
  | 26 => selectorBytes 0x89 0xea 0x45 0xd3
  | 27 => selectorBytes 0xc8 0x30 0x62 0xc6
  | 28 => selectorBytes 0x59 0x20 0x37 0x5c
  | 29 => selectorBytes 0x4a 0x10 0xea 0xa6
  | 30 => selectorBytes 0x6e 0xa4 0x25 0x55
  | _ => selectorBytes 0xfe 0x85 0x07 0xc6

theorem endDispatch_none_short {cd : ByteArray} (h : cd.size < 4) :
    dispatchMsg contract cd = none := by
  have hmiss (sel : ByteArray) (hsel : sel.size = 4) :
      (sel == cd.extract 0 4) = false := by
    by_contra hc
    rw [Bool.not_eq_false] at hc
    have hsz := byteArray_size_eq_of_beq hc
    rw [ByteArray.size_extract, hsel] at hsz
    omega
  apply dispatchMsg_none_of_all_ne (hfallback := by rfl)
  intro t ht
  simp [contract, transitions] at ht
  rcases ht with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · rw [endWardsSelectorBytes]
    exact hmiss _ (by native_decide)
  · rw [endVatSelectorBytes]
    exact hmiss _ (by native_decide)
  · rw [endCatSelectorBytes]
    exact hmiss _ (by native_decide)
  · rw [endDogSelectorBytes]
    exact hmiss _ (by native_decide)
  · rw [endVowSelectorBytes]
    exact hmiss _ (by native_decide)
  · rw [endPotSelectorBytes]
    exact hmiss _ (by native_decide)
  · rw [endSpotSelectorBytes]
    exact hmiss _ (by native_decide)
  · rw [endCureSelectorBytes]
    exact hmiss _ (by native_decide)
  · rw [endLiveSelectorBytes]
    exact hmiss _ (by native_decide)
  · rw [endWhenSelectorBytes]
    exact hmiss _ (by native_decide)
  · rw [endWaitSelectorBytes]
    exact hmiss _ (by native_decide)
  · rw [endDebtSelectorBytes]
    exact hmiss _ (by native_decide)
  · rw [endTagSelectorBytes]
    exact hmiss _ (by native_decide)
  · rw [endGapSelectorBytes]
    exact hmiss _ (by native_decide)
  · rw [endArtSelectorBytes]
    exact hmiss _ (by native_decide)
  · rw [endFixSelectorBytes]
    exact hmiss _ (by native_decide)
  · rw [endBagSelectorBytes]
    exact hmiss _ (by native_decide)
  · rw [endOutSelectorBytes]
    exact hmiss _ (by native_decide)
  · rw [endRelySelectorBytes]
    exact hmiss _ (by native_decide)
  · rw [endDenySelectorBytes]
    exact hmiss _ (by native_decide)
  · rw [endFileAddressSelectorBytes]
    exact hmiss _ (by native_decide)
  · rw [endFileUintSelectorBytes]
    exact hmiss _ (by native_decide)
  · rw [endCageSelectorBytes]
    exact hmiss _ (by native_decide)
  · rw [endCageIlkSelectorBytes]
    exact hmiss _ (by native_decide)
  · rw [endSnipSelectorBytes]
    exact hmiss _ (by native_decide)
  · rw [endSkipSelectorBytes]
    exact hmiss _ (by native_decide)
  · rw [endSkimSelectorBytes]
    exact hmiss _ (by native_decide)
  · rw [endFreeSelectorBytes]
    exact hmiss _ (by native_decide)
  · rw [endThawSelectorBytes]
    exact hmiss _ (by native_decide)
  · rw [endFlowSelectorBytes]
    exact hmiss _ (by native_decide)
  · rw [endPackSelectorBytes]
    exact hmiss _ (by native_decide)
  · rw [endCashSelectorBytes]
    exact hmiss _ (by native_decide)

theorem endDispatch_none_nomatch {cd : ByteArray}
    (hnm : ∀ i, i < 32 → (endSelBytes i == cd.extract 0 4) = false) :
    dispatchMsg contract cd = none := by
  apply dispatchMsg_none_of_all_ne (hfallback := by rfl)
  intro t ht
  simp [contract, transitions] at ht
  rcases ht with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · rw [endWardsSelectorBytes]
    simpa [endSelBytes] using hnm 0 (by omega)
  · rw [endVatSelectorBytes]
    simpa [endSelBytes] using hnm 1 (by omega)
  · rw [endCatSelectorBytes]
    simpa [endSelBytes] using hnm 2 (by omega)
  · rw [endDogSelectorBytes]
    simpa [endSelBytes] using hnm 3 (by omega)
  · rw [endVowSelectorBytes]
    simpa [endSelBytes] using hnm 4 (by omega)
  · rw [endPotSelectorBytes]
    simpa [endSelBytes] using hnm 5 (by omega)
  · rw [endSpotSelectorBytes]
    simpa [endSelBytes] using hnm 6 (by omega)
  · rw [endCureSelectorBytes]
    simpa [endSelBytes] using hnm 7 (by omega)
  · rw [endLiveSelectorBytes]
    simpa [endSelBytes] using hnm 8 (by omega)
  · rw [endWhenSelectorBytes]
    simpa [endSelBytes] using hnm 9 (by omega)
  · rw [endWaitSelectorBytes]
    simpa [endSelBytes] using hnm 10 (by omega)
  · rw [endDebtSelectorBytes]
    simpa [endSelBytes] using hnm 11 (by omega)
  · rw [endTagSelectorBytes]
    simpa [endSelBytes] using hnm 12 (by omega)
  · rw [endGapSelectorBytes]
    simpa [endSelBytes] using hnm 13 (by omega)
  · rw [endArtSelectorBytes]
    simpa [endSelBytes] using hnm 14 (by omega)
  · rw [endFixSelectorBytes]
    simpa [endSelBytes] using hnm 15 (by omega)
  · rw [endBagSelectorBytes]
    simpa [endSelBytes] using hnm 16 (by omega)
  · rw [endOutSelectorBytes]
    simpa [endSelBytes] using hnm 17 (by omega)
  · rw [endRelySelectorBytes]
    simpa [endSelBytes] using hnm 18 (by omega)
  · rw [endDenySelectorBytes]
    simpa [endSelBytes] using hnm 19 (by omega)
  · rw [endFileAddressSelectorBytes]
    simpa [endSelBytes] using hnm 20 (by omega)
  · rw [endFileUintSelectorBytes]
    simpa [endSelBytes] using hnm 21 (by omega)
  · rw [endCageSelectorBytes]
    simpa [endSelBytes] using hnm 22 (by omega)
  · rw [endCageIlkSelectorBytes]
    simpa [endSelBytes] using hnm 23 (by omega)
  · rw [endSnipSelectorBytes]
    simpa [endSelBytes] using hnm 24 (by omega)
  · rw [endSkipSelectorBytes]
    simpa [endSelBytes] using hnm 25 (by omega)
  · rw [endSkimSelectorBytes]
    simpa [endSelBytes] using hnm 26 (by omega)
  · rw [endFreeSelectorBytes]
    simpa [endSelBytes] using hnm 27 (by omega)
  · rw [endThawSelectorBytes]
    simpa [endSelBytes] using hnm 28 (by omega)
  · rw [endFlowSelectorBytes]
    simpa [endSelBytes] using hnm 29 (by omega)
  · rw [endPackSelectorBytes]
    simpa [endSelBytes] using hnm 30 (by omega)
  · rw [endCashSelectorBytes]
    simpa [endSelBytes] using hnm 31 (by omega)

theorem endNoSelectorMatches {I : ExecutionEnv}
    (hwards : ¬ selIs I (selectorOf wardsTransition))
    (hvat : ¬ selIs I (selectorOf vatTransition))
    (hcat : ¬ selIs I (selectorOf catTransition))
    (hdog : ¬ selIs I (selectorOf dogTransition))
    (hvow : ¬ selIs I (selectorOf vowTransition))
    (hpot : ¬ selIs I (selectorOf potTransition))
    (hspot : ¬ selIs I (selectorOf spotTransition))
    (hcure : ¬ selIs I (selectorOf cureTransition))
    (hlive : ¬ selIs I (selectorOf liveTransition))
    (hwhen : ¬ selIs I (selectorOf whenTransition))
    (hwait : ¬ selIs I (selectorOf waitTransition))
    (hdebt : ¬ selIs I (selectorOf debtTransition))
    (htag : ¬ selIs I (selectorOf tagTransition))
    (hgap : ¬ selIs I (selectorOf gapTransition))
    (hArt : ¬ selIs I (selectorOf ArtTransition))
    (hfix : ¬ selIs I (selectorOf fixTransition))
    (hbag : ¬ selIs I (selectorOf bagTransition))
    (hout : ¬ selIs I (selectorOf outTransition))
    (hrely : ¬ selIs I (selectorOf relyTransition))
    (hdeny : ¬ selIs I (selectorOf denyTransition))
    (hfileAddress : ¬ selIs I (selectorOf fileAddressTransition))
    (hfileUint : ¬ selIs I (selectorOf fileUintTransition))
    (hcage : ¬ selIs I (selectorOf cageTransition))
    (hcageIlk : ¬ selIs I (selectorOf cageIlkTransition))
    (hsnip : ¬ selIs I (selectorOf snipTransition))
    (hskip : ¬ selIs I (selectorOf skipTransition))
    (hskim : ¬ selIs I (selectorOf skimTransition))
    (hfree : ¬ selIs I (selectorOf freeTransition))
    (hthaw : ¬ selIs I (selectorOf thawTransition))
    (hflow : ¬ selIs I (selectorOf flowTransition))
    (hpack : ¬ selIs I (selectorOf packTransition))
    (hcash : ¬ selIs I (selectorOf cashTransition)) :
    ∀ i, i < 32 → (endSelBytes i == I.calldata.extract 0 4) = false := by
  intro i hi
  interval_cases i
  · simpa [selIs, endSelBytes, endWardsSelectorBytes] using hwards
  · simpa [selIs, endSelBytes, endVatSelectorBytes] using hvat
  · simpa [selIs, endSelBytes, endCatSelectorBytes] using hcat
  · simpa [selIs, endSelBytes, endDogSelectorBytes] using hdog
  · simpa [selIs, endSelBytes, endVowSelectorBytes] using hvow
  · simpa [selIs, endSelBytes, endPotSelectorBytes] using hpot
  · simpa [selIs, endSelBytes, endSpotSelectorBytes] using hspot
  · simpa [selIs, endSelBytes, endCureSelectorBytes] using hcure
  · simpa [selIs, endSelBytes, endLiveSelectorBytes] using hlive
  · simpa [selIs, endSelBytes, endWhenSelectorBytes] using hwhen
  · simpa [selIs, endSelBytes, endWaitSelectorBytes] using hwait
  · simpa [selIs, endSelBytes, endDebtSelectorBytes] using hdebt
  · simpa [selIs, endSelBytes, endTagSelectorBytes] using htag
  · simpa [selIs, endSelBytes, endGapSelectorBytes] using hgap
  · simpa [selIs, endSelBytes, endArtSelectorBytes] using hArt
  · simpa [selIs, endSelBytes, endFixSelectorBytes] using hfix
  · simpa [selIs, endSelBytes, endBagSelectorBytes] using hbag
  · simpa [selIs, endSelBytes, endOutSelectorBytes] using hout
  · simpa [selIs, endSelBytes, endRelySelectorBytes] using hrely
  · simpa [selIs, endSelBytes, endDenySelectorBytes] using hdeny
  · simpa [selIs, endSelBytes, endFileAddressSelectorBytes] using hfileAddress
  · simpa [selIs, endSelBytes, endFileUintSelectorBytes] using hfileUint
  · simpa [selIs, endSelBytes, endCageSelectorBytes] using hcage
  · simpa [selIs, endSelBytes, endCageIlkSelectorBytes] using hcageIlk
  · simpa [selIs, endSelBytes, endSnipSelectorBytes] using hsnip
  · simpa [selIs, endSelBytes, endSkipSelectorBytes] using hskip
  · simpa [selIs, endSelBytes, endSkimSelectorBytes] using hskim
  · simpa [selIs, endSelBytes, endFreeSelectorBytes] using hfree
  · simpa [selIs, endSelBytes, endThawSelectorBytes] using hthaw
  · simpa [selIs, endSelBytes, endFlowSelectorBytes] using hflow
  · simpa [selIs, endSelBytes, endPackSelectorBytes] using hpack
  · simpa [selIs, endSelBytes, endCashSelectorBytes] using hcash

/-! ## Runtime dispatcher PCs

These constants are read from `runtime.hex`; keep them synchronized with `endBytecode`.
-/

abbrev endRootSplitPc : UInt256 := ⟨32⟩
abbrev endHighSplitPc : UInt256 := ⟨43⟩
abbrev endHigh2SplitPc : UInt256 := ⟨54⟩
abbrev endGroup65FirstArmPc : UInt256 := ⟨65⟩
abbrev endGroup114JumpdestPc : UInt256 := ⟨113⟩
abbrev endGroup114FirstArmPc : UInt256 := ⟨114⟩
abbrev endHighJumpdestPc : UInt256 := ⟨162⟩
abbrev endHighMidSplitPc : UInt256 := ⟨163⟩
abbrev endGroup174FirstArmPc : UInt256 := ⟨174⟩
abbrev endGroup223JumpdestPc : UInt256 := ⟨222⟩
abbrev endGroup223FirstArmPc : UInt256 := ⟨223⟩
abbrev endLow1JumpdestPc : UInt256 := ⟨271⟩
abbrev endLow1SplitPc : UInt256 := ⟨272⟩
abbrev endLowHighSplitPc : UInt256 := ⟨283⟩
abbrev endGroup294FirstArmPc : UInt256 := ⟨294⟩
abbrev endGroup343JumpdestPc : UInt256 := ⟨342⟩
abbrev endGroup343FirstArmPc : UInt256 := ⟨343⟩
abbrev endLow2JumpdestPc : UInt256 := ⟨391⟩
abbrev endLow2SplitPc : UInt256 := ⟨392⟩
abbrev endGroup403FirstArmPc : UInt256 := ⟨403⟩
abbrev endVeryLowJumpdestPc : UInt256 := ⟨451⟩
abbrev endDebtFirstArmPc : UInt256 := ⟨452⟩
abbrev endDebtEntryPc : UInt256 := ⟨501⟩
abbrev endWordReturnPc : UInt256 := ⟨509⟩
abbrev endDebtRoutinePc : UInt256 := ⟨1309⟩
abbrev endDispatchBodyPc : UInt256 := ⟨18⟩
abbrev endSelectorLoadPc : UInt256 := ⟨26⟩
abbrev endDispatchRevertPc : UInt256 := ⟨496⟩

theorem endRootSplitWellFormed :
    selectorSplitWellFormed endBytecode endRootSplitPc := by
  dsimp [selectorSplitWellFormed]
  repeat' first | apply And.intro | native_decide

theorem endHighSplitWellFormed :
    selectorSplitWellFormed endBytecode endHighSplitPc := by
  dsimp [selectorSplitWellFormed]
  repeat' first | apply And.intro | native_decide

theorem endHigh2SplitWellFormed :
    selectorSplitWellFormed endBytecode endHigh2SplitPc := by
  dsimp [selectorSplitWellFormed]
  repeat' first | apply And.intro | native_decide

theorem endHighMidSplitWellFormed :
    selectorSplitWellFormed endBytecode endHighMidSplitPc := by
  dsimp [selectorSplitWellFormed]
  repeat' first | apply And.intro | native_decide

theorem endLow1SplitWellFormed :
    selectorSplitWellFormed endBytecode endLow1SplitPc := by
  dsimp [selectorSplitWellFormed]
  repeat' first | apply And.intro | native_decide

theorem endLowHighSplitWellFormed :
    selectorSplitWellFormed endBytecode endLowHighSplitPc := by
  dsimp [selectorSplitWellFormed]
  repeat' first | apply And.intro | native_decide

theorem endLow2SplitWellFormed :
    selectorSplitWellFormed endBytecode endLow2SplitPc := by
  dsimp [selectorSplitWellFormed]
  repeat' first | apply And.intro | native_decide

theorem endRootSplitTaken {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {selWord : UInt256} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap} {k C : ℕ}
    {rest : List UInt256}
    (h : RD endBytecode ee g s0 endRootSplitPc (selWord :: rest) mem aw rdata acc k C)
    (hb : UInt256.gt (armSelNat endBytecode endRootSplitPc) selWord ≠ ⟨0⟩)
    (hov : rest.length + 3 ≤ 1024) :
    RD endBytecode ee g s0 endLow1JumpdestPc (selWord :: rest) mem aw rdata acc
      (k + 5) (C + 22) := by
  exact RD.selectorSplitTakenResolved (tgt := endLow1JumpdestPc) (width := 2)
    (op := .PUSH2) h endRootSplitWellFormed (by native_decide) (by native_decide)
    (by native_decide) hb (by jump_dest) hov

theorem endRootSplitNotTaken {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {selWord : UInt256} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap} {k C : ℕ}
    {rest : List UInt256}
    (h : RD endBytecode ee g s0 endRootSplitPc (selWord :: rest) mem aw rdata acc k C)
    (hb : UInt256.gt (armSelNat endBytecode endRootSplitPc) selWord = ⟨0⟩)
    (hov : rest.length + 3 ≤ 1024) :
    RD endBytecode ee g s0 endHighSplitPc (selWord :: rest) mem aw rdata acc
      (k + 5) (C + 22) := by
  exact RD.selectorSplitNotTakenResolved (tgt := endLow1JumpdestPc) (nextPc := endHighSplitPc)
    (width := 2) (op := .PUSH2) h endRootSplitWellFormed (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) hb hov

theorem endHighSplitTaken {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {selWord : UInt256} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap} {k C : ℕ}
    {rest : List UInt256}
    (h : RD endBytecode ee g s0 endHighSplitPc (selWord :: rest) mem aw rdata acc k C)
    (hb : UInt256.gt (armSelNat endBytecode endHighSplitPc) selWord ≠ ⟨0⟩)
    (hov : rest.length + 3 ≤ 1024) :
    RD endBytecode ee g s0 endHighJumpdestPc (selWord :: rest) mem aw rdata acc
      (k + 5) (C + 22) := by
  exact RD.selectorSplitTakenResolved (tgt := endHighJumpdestPc) (width := 2)
    (op := .PUSH2) h endHighSplitWellFormed (by native_decide) (by native_decide)
    (by native_decide) hb (by jump_dest) hov

theorem endHighSplitNotTaken {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {selWord : UInt256} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap} {k C : ℕ}
    {rest : List UInt256}
    (h : RD endBytecode ee g s0 endHighSplitPc (selWord :: rest) mem aw rdata acc k C)
    (hb : UInt256.gt (armSelNat endBytecode endHighSplitPc) selWord = ⟨0⟩)
    (hov : rest.length + 3 ≤ 1024) :
    RD endBytecode ee g s0 endHigh2SplitPc (selWord :: rest) mem aw rdata acc
      (k + 5) (C + 22) := by
  exact RD.selectorSplitNotTakenResolved (tgt := endHighJumpdestPc) (nextPc := endHigh2SplitPc)
    (width := 2) (op := .PUSH2) h endHighSplitWellFormed (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) hb hov

theorem endHigh2SplitTaken {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {selWord : UInt256} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap} {k C : ℕ}
    {rest : List UInt256}
    (h : RD endBytecode ee g s0 endHigh2SplitPc (selWord :: rest) mem aw rdata acc k C)
    (hb : UInt256.gt (armSelNat endBytecode endHigh2SplitPc) selWord ≠ ⟨0⟩)
    (hov : rest.length + 3 ≤ 1024) :
    RD endBytecode ee g s0 endGroup114JumpdestPc (selWord :: rest) mem aw rdata acc
      (k + 5) (C + 22) := by
  exact RD.selectorSplitTakenResolved (tgt := endGroup114JumpdestPc) (width := 2)
    (op := .PUSH2) h endHigh2SplitWellFormed (by native_decide) (by native_decide)
    (by native_decide) hb (by jump_dest) hov

theorem endHigh2SplitNotTaken {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {selWord : UInt256} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap} {k C : ℕ}
    {rest : List UInt256}
    (h : RD endBytecode ee g s0 endHigh2SplitPc (selWord :: rest) mem aw rdata acc k C)
    (hb : UInt256.gt (armSelNat endBytecode endHigh2SplitPc) selWord = ⟨0⟩)
    (hov : rest.length + 3 ≤ 1024) :
    RD endBytecode ee g s0 endGroup65FirstArmPc (selWord :: rest) mem aw rdata acc
      (k + 5) (C + 22) := by
  exact RD.selectorSplitNotTakenResolved (tgt := endGroup114JumpdestPc)
    (nextPc := endGroup65FirstArmPc) (width := 2) (op := .PUSH2) h
    endHigh2SplitWellFormed (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) hb hov

theorem endHighMidSplitTaken {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {selWord : UInt256} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap} {k C : ℕ}
    {rest : List UInt256}
    (h : RD endBytecode ee g s0 endHighMidSplitPc (selWord :: rest) mem aw rdata acc k C)
    (hb : UInt256.gt (armSelNat endBytecode endHighMidSplitPc) selWord ≠ ⟨0⟩)
    (hov : rest.length + 3 ≤ 1024) :
    RD endBytecode ee g s0 endGroup223JumpdestPc (selWord :: rest) mem aw rdata acc
      (k + 5) (C + 22) := by
  exact RD.selectorSplitTakenResolved (tgt := endGroup223JumpdestPc) (width := 2)
    (op := .PUSH2) h endHighMidSplitWellFormed (by native_decide) (by native_decide)
    (by native_decide) hb (by jump_dest) hov

theorem endHighMidSplitNotTaken {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {selWord : UInt256} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap} {k C : ℕ}
    {rest : List UInt256}
    (h : RD endBytecode ee g s0 endHighMidSplitPc (selWord :: rest) mem aw rdata acc k C)
    (hb : UInt256.gt (armSelNat endBytecode endHighMidSplitPc) selWord = ⟨0⟩)
    (hov : rest.length + 3 ≤ 1024) :
    RD endBytecode ee g s0 endGroup174FirstArmPc (selWord :: rest) mem aw rdata acc
      (k + 5) (C + 22) := by
  exact RD.selectorSplitNotTakenResolved (tgt := endGroup223JumpdestPc)
    (nextPc := endGroup174FirstArmPc) (width := 2) (op := .PUSH2) h
    endHighMidSplitWellFormed (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) hb hov

theorem endLow1SplitTaken {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {selWord : UInt256} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap} {k C : ℕ}
    {rest : List UInt256}
    (h : RD endBytecode ee g s0 endLow1SplitPc (selWord :: rest) mem aw rdata acc k C)
    (hb : UInt256.gt (armSelNat endBytecode endLow1SplitPc) selWord ≠ ⟨0⟩)
    (hov : rest.length + 3 ≤ 1024) :
    RD endBytecode ee g s0 endLow2JumpdestPc (selWord :: rest) mem aw rdata acc
      (k + 5) (C + 22) := by
  exact RD.selectorSplitTakenResolved (tgt := endLow2JumpdestPc) (width := 2)
    (op := .PUSH2) h endLow1SplitWellFormed (by native_decide) (by native_decide)
    (by native_decide) hb (by jump_dest) hov

theorem endLow1SplitNotTaken {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {selWord : UInt256} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap} {k C : ℕ}
    {rest : List UInt256}
    (h : RD endBytecode ee g s0 endLow1SplitPc (selWord :: rest) mem aw rdata acc k C)
    (hb : UInt256.gt (armSelNat endBytecode endLow1SplitPc) selWord = ⟨0⟩)
    (hov : rest.length + 3 ≤ 1024) :
    RD endBytecode ee g s0 endLowHighSplitPc (selWord :: rest) mem aw rdata acc
      (k + 5) (C + 22) := by
  exact RD.selectorSplitNotTakenResolved (tgt := endLow2JumpdestPc)
    (nextPc := endLowHighSplitPc) (width := 2) (op := .PUSH2) h endLow1SplitWellFormed
    (by native_decide) (by native_decide) (by native_decide) (by native_decide) hb hov

theorem endLowHighSplitTaken {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {selWord : UInt256} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap} {k C : ℕ}
    {rest : List UInt256}
    (h : RD endBytecode ee g s0 endLowHighSplitPc (selWord :: rest) mem aw rdata acc k C)
    (hb : UInt256.gt (armSelNat endBytecode endLowHighSplitPc) selWord ≠ ⟨0⟩)
    (hov : rest.length + 3 ≤ 1024) :
    RD endBytecode ee g s0 endGroup343JumpdestPc (selWord :: rest) mem aw rdata acc
      (k + 5) (C + 22) := by
  exact RD.selectorSplitTakenResolved (tgt := endGroup343JumpdestPc) (width := 2)
    (op := .PUSH2) h endLowHighSplitWellFormed (by native_decide) (by native_decide)
    (by native_decide) hb (by jump_dest) hov

theorem endLowHighSplitNotTaken {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {selWord : UInt256} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap} {k C : ℕ}
    {rest : List UInt256}
    (h : RD endBytecode ee g s0 endLowHighSplitPc (selWord :: rest) mem aw rdata acc k C)
    (hb : UInt256.gt (armSelNat endBytecode endLowHighSplitPc) selWord = ⟨0⟩)
    (hov : rest.length + 3 ≤ 1024) :
    RD endBytecode ee g s0 endGroup294FirstArmPc (selWord :: rest) mem aw rdata acc
      (k + 5) (C + 22) := by
  exact RD.selectorSplitNotTakenResolved (tgt := endGroup343JumpdestPc)
    (nextPc := endGroup294FirstArmPc) (width := 2) (op := .PUSH2) h
    endLowHighSplitWellFormed (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) hb hov

theorem endLow2SplitTaken {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {selWord : UInt256} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap} {k C : ℕ}
    {rest : List UInt256}
    (h : RD endBytecode ee g s0 endLow2SplitPc (selWord :: rest) mem aw rdata acc k C)
    (hb : UInt256.gt (armSelNat endBytecode endLow2SplitPc) selWord ≠ ⟨0⟩)
    (hov : rest.length + 3 ≤ 1024) :
    RD endBytecode ee g s0 endVeryLowJumpdestPc (selWord :: rest) mem aw rdata acc
      (k + 5) (C + 22) := by
  exact RD.selectorSplitTakenResolved (tgt := endVeryLowJumpdestPc) (width := 2)
    (op := .PUSH2) h endLow2SplitWellFormed (by native_decide) (by native_decide)
    (by native_decide) hb (by jump_dest) hov

theorem endLow2SplitNotTaken {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {selWord : UInt256} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap} {k C : ℕ}
    {rest : List UInt256}
    (h : RD endBytecode ee g s0 endLow2SplitPc (selWord :: rest) mem aw rdata acc k C)
    (hb : UInt256.gt (armSelNat endBytecode endLow2SplitPc) selWord = ⟨0⟩)
    (hov : rest.length + 3 ≤ 1024) :
    RD endBytecode ee g s0 endGroup403FirstArmPc (selWord :: rest) mem aw rdata acc
      (k + 5) (C + 22) := by
  exact RD.selectorSplitNotTakenResolved (tgt := endVeryLowJumpdestPc)
    (nextPc := endGroup403FirstArmPc) (width := 2) (op := .PUSH2) h endLow2SplitWellFormed
    (by native_decide) (by native_decide) (by native_decide) (by native_decide) hb hov

set_option maxHeartbeats 1000000 in
theorem endGroup65ArmsWellFormed :
    ∀ j, j ≤ 3 → armWellFormed endBytecode (nthArmPc endBytecode endGroup65FirstArmPc j) := by
  intro j hj
  interval_cases j <;>
    (dsimp [armWellFormed]
     repeat' first | apply And.intro | native_decide)

set_option maxHeartbeats 1000000 in
theorem endGroup114ArmsWellFormed :
    ∀ j, j ≤ 3 → armWellFormed endBytecode (nthArmPc endBytecode endGroup114FirstArmPc j) := by
  intro j hj
  interval_cases j <;>
    (dsimp [armWellFormed]
     repeat' first | apply And.intro | native_decide)

set_option maxHeartbeats 1000000 in
theorem endGroup174ArmsWellFormed :
    ∀ j, j ≤ 3 → armWellFormed endBytecode (nthArmPc endBytecode endGroup174FirstArmPc j) := by
  intro j hj
  interval_cases j <;>
    (dsimp [armWellFormed]
     repeat' first | apply And.intro | native_decide)

set_option maxHeartbeats 1000000 in
theorem endGroup223ArmsWellFormed :
    ∀ j, j ≤ 3 → armWellFormed endBytecode (nthArmPc endBytecode endGroup223FirstArmPc j) := by
  intro j hj
  interval_cases j <;>
    (dsimp [armWellFormed]
     repeat' first | apply And.intro | native_decide)

set_option maxHeartbeats 1000000 in
theorem endGroup294ArmsWellFormed :
    ∀ j, j ≤ 3 → armWellFormed endBytecode (nthArmPc endBytecode endGroup294FirstArmPc j) := by
  intro j hj
  interval_cases j <;>
    (dsimp [armWellFormed]
     repeat' first | apply And.intro | native_decide)

set_option maxHeartbeats 1000000 in
theorem endGroup343ArmsWellFormed :
    ∀ j, j ≤ 3 → armWellFormed endBytecode (nthArmPc endBytecode endGroup343FirstArmPc j) := by
  intro j hj
  interval_cases j <;>
    (dsimp [armWellFormed]
     repeat' first | apply And.intro | native_decide)

set_option maxHeartbeats 1000000 in
theorem endGroup403ArmsWellFormed :
    ∀ j, j ≤ 3 → armWellFormed endBytecode (nthArmPc endBytecode endGroup403FirstArmPc j) := by
  intro j hj
  interval_cases j <;>
    (dsimp [armWellFormed]
     repeat' first | apply And.intro | native_decide)

set_option maxHeartbeats 1000000 in
theorem endGroup452ArmsWellFormed :
    ∀ j, j ≤ 3 → armWellFormed endBytecode (nthArmPc endBytecode endDebtFirstArmPc j) := by
  intro j hj
  interval_cases j <;>
    (dsimp [armWellFormed]
     repeat' first | apply And.intro | native_decide)

set_option maxHeartbeats 1000000 in
theorem endDebtArmsWellFormed :
    ∀ j, j ≤ 0 → armWellFormed endBytecode (nthArmPc endBytecode endDebtFirstArmPc j) := by
  intro j hj
  interval_cases j
  dsimp [armWellFormed]
  repeat' first | apply And.intro | native_decide

def endGroup65SelBytes : ℕ → ByteArray
  | 0 => selectorBytes 0xe4 0x88 0x18 0x13
  | 1 => selectorBytes 0xe6 0xee 0x62 0xaa
  | 2 => selectorBytes 0xee 0x64 0x47 0xb5
  | _ => selectorBytes 0xfe 0x85 0x07 0xc6

def endGroup114SelBytes : ℕ → ByteArray
  | 0 => selectorBytes 0xd4 0xe8 0xbe 0x83
  | 1 => selectorBytes 0xe1 0x34 0x0a 0x3d
  | 2 => selectorBytes 0xe2 0x70 0x2f 0xdc
  | _ => selectorBytes 0xe2 0xb0 0xca 0xef

def endGroup174SelBytes : ℕ → ByteArray
  | 0 => selectorBytes 0xbf 0x35 0x3d 0xbb
  | 1 => selectorBytes 0xc3 0xb3 0xad 0x7f
  | 2 => selectorBytes 0xc8 0x30 0x62 0xc6
  | _ => selectorBytes 0xc9 0x39 0xeb 0xfc

def endGroup223SelBytes : ℕ → ByteArray
  | 0 => selectorBytes 0x89 0xea 0x45 0xd3
  | 1 => selectorBytes 0x92 0x55 0xf8 0x09
  | 2 => selectorBytes 0x95 0x7a 0xa5 0x8c
  | _ => selectorBytes 0x9c 0x52 0xa7 0xf1

def endGroup294SelBytes : ℕ → ByteArray
  | 0 => selectorBytes 0x69 0x24 0x50 0x09
  | 1 => selectorBytes 0x6e 0xa4 0x25 0x55
  | 2 => selectorBytes 0x6f 0x26 0x5b 0x93
  | _ => selectorBytes 0x84 0x07 0x82 0xed

def endGroup343SelBytes : ℕ → ByteArray
  | 0 => selectorBytes 0x62 0x6c 0xb3 0xc5
  | 1 => selectorBytes 0x63 0xfa 0xd8 0x5e
  | 2 => selectorBytes 0x64 0xbd 0x70 0x13
  | _ => selectorBytes 0x65 0xfa 0xe3 0x5e

def endGroup403SelBytes : ℕ → ByteArray
  | 0 => selectorBytes 0x4a 0x10 0xea 0xa6
  | 1 => selectorBytes 0x4b 0xa2 0x36 0x3a
  | 2 => selectorBytes 0x50 0x3e 0xcf 0x06
  | _ => selectorBytes 0x59 0x20 0x37 0x5c

def endGroup452SelBytes : ℕ → ByteArray
  | 0 => debtSelector
  | 1 => selectorBytes 0x29 0xae 0x81 0x14
  | 2 => selectorBytes 0x36 0x56 0x9e 0x77
  | _ => selectorBytes 0x38 0xc6 0xde 0x40

theorem endGroup65ArmEq (I : ExecutionEnv) (hsz : 4 ≤ I.calldata.size)
    (j : ℕ) (hj : j < 4) :
    UInt256.eq
        (armSelNat endBytecode (nthArmPc endBytecode endGroup65FirstArmPc j))
        (endSelWord I) =
      if (endGroup65SelBytes j == I.calldata.extract 0 4) then ⟨1⟩ else ⟨0⟩ := by
  interval_cases j <;> exact evmSelectorDecode hsz _ _ _ _ _ (by native_decide)

theorem endGroup114ArmEq (I : ExecutionEnv) (hsz : 4 ≤ I.calldata.size)
    (j : ℕ) (hj : j < 4) :
    UInt256.eq
        (armSelNat endBytecode (nthArmPc endBytecode endGroup114FirstArmPc j))
        (endSelWord I) =
      if (endGroup114SelBytes j == I.calldata.extract 0 4) then ⟨1⟩ else ⟨0⟩ := by
  interval_cases j <;> exact evmSelectorDecode hsz _ _ _ _ _ (by native_decide)

theorem endGroup174ArmEq (I : ExecutionEnv) (hsz : 4 ≤ I.calldata.size)
    (j : ℕ) (hj : j < 4) :
    UInt256.eq
        (armSelNat endBytecode (nthArmPc endBytecode endGroup174FirstArmPc j))
        (endSelWord I) =
      if (endGroup174SelBytes j == I.calldata.extract 0 4) then ⟨1⟩ else ⟨0⟩ := by
  interval_cases j <;> exact evmSelectorDecode hsz _ _ _ _ _ (by native_decide)

theorem endGroup223ArmEq (I : ExecutionEnv) (hsz : 4 ≤ I.calldata.size)
    (j : ℕ) (hj : j < 4) :
    UInt256.eq
        (armSelNat endBytecode (nthArmPc endBytecode endGroup223FirstArmPc j))
        (endSelWord I) =
      if (endGroup223SelBytes j == I.calldata.extract 0 4) then ⟨1⟩ else ⟨0⟩ := by
  interval_cases j <;> exact evmSelectorDecode hsz _ _ _ _ _ (by native_decide)

theorem endGroup294ArmEq (I : ExecutionEnv) (hsz : 4 ≤ I.calldata.size)
    (j : ℕ) (hj : j < 4) :
    UInt256.eq
        (armSelNat endBytecode (nthArmPc endBytecode endGroup294FirstArmPc j))
        (endSelWord I) =
      if (endGroup294SelBytes j == I.calldata.extract 0 4) then ⟨1⟩ else ⟨0⟩ := by
  interval_cases j <;> exact evmSelectorDecode hsz _ _ _ _ _ (by native_decide)

theorem endGroup343ArmEq (I : ExecutionEnv) (hsz : 4 ≤ I.calldata.size)
    (j : ℕ) (hj : j < 4) :
    UInt256.eq
        (armSelNat endBytecode (nthArmPc endBytecode endGroup343FirstArmPc j))
        (endSelWord I) =
      if (endGroup343SelBytes j == I.calldata.extract 0 4) then ⟨1⟩ else ⟨0⟩ := by
  interval_cases j <;> exact evmSelectorDecode hsz _ _ _ _ _ (by native_decide)

theorem endGroup403ArmEq (I : ExecutionEnv) (hsz : 4 ≤ I.calldata.size)
    (j : ℕ) (hj : j < 4) :
    UInt256.eq
        (armSelNat endBytecode (nthArmPc endBytecode endGroup403FirstArmPc j))
        (endSelWord I) =
      if (endGroup403SelBytes j == I.calldata.extract 0 4) then ⟨1⟩ else ⟨0⟩ := by
  interval_cases j <;> exact evmSelectorDecode hsz _ _ _ _ _ (by native_decide)

theorem endGroup452ArmEq (I : ExecutionEnv) (hsz : 4 ≤ I.calldata.size)
    (j : ℕ) (hj : j < 4) :
    UInt256.eq
        (armSelNat endBytecode (nthArmPc endBytecode endDebtFirstArmPc j))
        (endSelWord I) =
      if (endGroup452SelBytes j == I.calldata.extract 0 4) then ⟨1⟩ else ⟨0⟩ := by
  interval_cases j <;> exact evmSelectorDecode hsz _ _ _ _ _ (by native_decide)

theorem endReachRootSplit {cA gh bl σ σ₀ A I} {g : Sat256}
    (hcode : I.code = endBytecode) (hwv : I.weiValue = ⟨0⟩)
    (hsz : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size) :
    ∃ k C, RD endBytecode I g (initState cA gh bl σ σ₀ g A I)
        endRootSplitPc [endSelWord I] solcFreePtrMem (UInt256.ofNat 3)
        ByteArray.empty (cA, σ) k C := by
  simpa [endRootSplitPc, endSelWord] using
    solcLegacyDispatchReachSelector (cA := cA) (gh := gh) (bl := bl) (σ := σ)
      (σ₀ := σ₀) (A := A) (g := g) (code := endBytecode)
      (bodyPc := endDispatchBodyPc) (loadPc := endSelectorLoadPc)
      (firstPc := endRootSplitPc) (guardTgt := (⟨16⟩ : UInt256))
      (revertTgt := endDispatchRevertPc) (guardWidth := 2) (revertWidth := 2)
      (guardOp := .PUSH2) (revertOp := .PUSH2)
      hcode hwv hsz hsize
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
      (by native_decide) (by native_decide)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
      (by native_decide) (by jump_dest) (by native_decide)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)

theorem endReachDebtFirstArm {cA gh bl σ σ₀ A I} {g : Sat256}
    (hcode : I.code = endBytecode) (hwv : I.weiValue = ⟨0⟩)
    (hsz : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hroot : UInt256.gt (armSelNat endBytecode endRootSplitPc) (endSelWord I) ≠ ⟨0⟩)
    (hlow1 : UInt256.gt (armSelNat endBytecode endLow1SplitPc) (endSelWord I) ≠ ⟨0⟩)
    (hlow2 : UInt256.gt (armSelNat endBytecode endLow2SplitPc) (endSelWord I) ≠ ⟨0⟩) :
    ∃ k C, RD endBytecode I g (initState cA gh bl σ σ₀ g A I)
        endDebtFirstArmPc [endSelWord I] solcFreePtrMem (UInt256.ofNat 3)
        ByteArray.empty (cA, σ) k C := by
  obtain ⟨k32, C32, h32⟩ :=
    endReachRootSplit (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀)
      (A := A) (I := I) (g := g) hcode hwv hsz hsize
  have h271 : RD endBytecode I g (initState cA gh bl σ σ₀ g A I)
      endLow1JumpdestPc [endSelWord I] solcFreePtrMem (UInt256.ofNat 3)
      ByteArray.empty (cA, σ) (k32 + 5) (C32 + 22) := by
    exact endRootSplitTaken h32 hroot (by simp)
  have h272 : RD endBytecode I g (initState cA gh bl σ σ₀ g A I)
      endLow1SplitPc [endSelWord I] solcFreePtrMem (UInt256.ofNat 3)
      ByteArray.empty (cA, σ) (k32 + 5 + 1) (C32 + 22 + 1) := by
    simpa [endLow1SplitPc] using h271.jumpdest (by native_decide) (by simp)
  have h391 : RD endBytecode I g (initState cA gh bl σ σ₀ g A I)
      endLow2JumpdestPc [endSelWord I] solcFreePtrMem (UInt256.ofNat 3)
      ByteArray.empty (cA, σ) (k32 + 5 + 1 + 5) (C32 + 22 + 1 + 22) := by
    exact endLow1SplitTaken h272 hlow1 (by simp)
  have h392 : RD endBytecode I g (initState cA gh bl σ σ₀ g A I)
      endLow2SplitPc [endSelWord I] solcFreePtrMem (UInt256.ofNat 3)
      ByteArray.empty (cA, σ) (k32 + 5 + 1 + 5 + 1) (C32 + 22 + 1 + 22 + 1) := by
    simpa [endLow2SplitPc] using h391.jumpdest (by native_decide) (by simp)
  have h451 : RD endBytecode I g (initState cA gh bl σ σ₀ g A I)
      endVeryLowJumpdestPc [endSelWord I] solcFreePtrMem (UInt256.ofNat 3)
      ByteArray.empty (cA, σ) (k32 + 5 + 1 + 5 + 1 + 5)
        (C32 + 22 + 1 + 22 + 1 + 22) := by
    exact endLow2SplitTaken h392 hlow2 (by simp)
  have h452 : RD endBytecode I g (initState cA gh bl σ σ₀ g A I)
      endDebtFirstArmPc [endSelWord I] solcFreePtrMem (UInt256.ofNat 3)
      ByteArray.empty (cA, σ) (k32 + 5 + 1 + 5 + 1 + 5 + 1)
        (C32 + 22 + 1 + 22 + 1 + 22 + 1) := by
    simpa [endDebtFirstArmPc] using h451.jumpdest (by native_decide) (by simp)
  exact ⟨_, _, h452⟩

theorem endReachDebtBody {cA gh bl σ σ₀ A I} {g : Sat256}
    (hcode : I.code = endBytecode) (hwv : I.weiValue = ⟨0⟩)
    (hsz : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hsel : selIs I debtSelector) :
    ∃ k C, RD endBytecode I g (initState cA gh bl σ σ₀ g A I)
        endDebtEntryPc [endSelWord I] solcFreePtrMem (UInt256.ofNat 3)
        ByteArray.empty (cA, σ) k C := by
  have hword : endSelWord I = ⟨0x0dca59c1⟩ :=
    endSelWord_eq_of_beq I hsz 0x0d 0xca 0x59 0xc1 ⟨0x0dca59c1⟩
      (by native_decide) (by simpa [selIs, debtSelector, selectorBytes] using hsel)
  obtain ⟨_, _, hfirst⟩ :=
    endReachDebtFirstArm (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀)
      (A := A) (I := I) (g := g) hcode hwv hsz hsize
      (by rw [hword]; native_decide)
      (by rw [hword]; native_decide)
      (by rw [hword]; native_decide)
  exact RD.dispatchTo endDebtEntryPc 0 hfirst
    (fun j hj => endDebtArmsWellFormed j (by omega))
    (by intro j hj; omega)
    (by rw [hword]; native_decide)
    (by jump_dest)
    (by native_decide)
    (by simp)

theorem endReachGroup65FirstArm {cA gh bl σ σ₀ A I} {g : Sat256}
    (hcode : I.code = endBytecode) (hwv : I.weiValue = ⟨0⟩)
    (hsz : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hroot : UInt256.gt (armSelNat endBytecode endRootSplitPc) (endSelWord I) = ⟨0⟩)
    (hhigh : UInt256.gt (armSelNat endBytecode endHighSplitPc) (endSelWord I) = ⟨0⟩)
    (hhigh2 : UInt256.gt (armSelNat endBytecode endHigh2SplitPc) (endSelWord I) = ⟨0⟩) :
    ∃ k C, RD endBytecode I g (initState cA gh bl σ σ₀ g A I)
        endGroup65FirstArmPc [endSelWord I] solcFreePtrMem (UInt256.ofNat 3)
        ByteArray.empty (cA, σ) k C := by
  obtain ⟨k32, C32, h32⟩ :=
    endReachRootSplit (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀)
      (A := A) (I := I) (g := g) hcode hwv hsz hsize
  have h43 : RD endBytecode I g (initState cA gh bl σ σ₀ g A I)
      endHighSplitPc [endSelWord I] solcFreePtrMem (UInt256.ofNat 3)
      ByteArray.empty (cA, σ) (k32 + 5) (C32 + 22) := by
    exact endRootSplitNotTaken h32 hroot (by simp)
  have h54 : RD endBytecode I g (initState cA gh bl σ σ₀ g A I)
      endHigh2SplitPc [endSelWord I] solcFreePtrMem (UInt256.ofNat 3)
      ByteArray.empty (cA, σ) (k32 + 5 + 5) (C32 + 22 + 22) := by
    exact endHighSplitNotTaken h43 hhigh (by simp)
  have h65 : RD endBytecode I g (initState cA gh bl σ σ₀ g A I)
      endGroup65FirstArmPc [endSelWord I] solcFreePtrMem (UInt256.ofNat 3)
      ByteArray.empty (cA, σ) (k32 + 5 + 5 + 5) (C32 + 22 + 22 + 22) := by
    exact endHigh2SplitNotTaken h54 hhigh2 (by simp)
  exact ⟨_, _, h65⟩

theorem endReachGroup114FirstArm {cA gh bl σ σ₀ A I} {g : Sat256}
    (hcode : I.code = endBytecode) (hwv : I.weiValue = ⟨0⟩)
    (hsz : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hroot : UInt256.gt (armSelNat endBytecode endRootSplitPc) (endSelWord I) = ⟨0⟩)
    (hhigh : UInt256.gt (armSelNat endBytecode endHighSplitPc) (endSelWord I) = ⟨0⟩)
    (hhigh2 : UInt256.gt (armSelNat endBytecode endHigh2SplitPc) (endSelWord I) ≠ ⟨0⟩) :
    ∃ k C, RD endBytecode I g (initState cA gh bl σ σ₀ g A I)
        endGroup114FirstArmPc [endSelWord I] solcFreePtrMem (UInt256.ofNat 3)
        ByteArray.empty (cA, σ) k C := by
  obtain ⟨k32, C32, h32⟩ :=
    endReachRootSplit (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀)
      (A := A) (I := I) (g := g) hcode hwv hsz hsize
  have h43 : RD endBytecode I g (initState cA gh bl σ σ₀ g A I)
      endHighSplitPc [endSelWord I] solcFreePtrMem (UInt256.ofNat 3)
      ByteArray.empty (cA, σ) (k32 + 5) (C32 + 22) := by
    exact endRootSplitNotTaken h32 hroot (by simp)
  have h54 : RD endBytecode I g (initState cA gh bl σ σ₀ g A I)
      endHigh2SplitPc [endSelWord I] solcFreePtrMem (UInt256.ofNat 3)
      ByteArray.empty (cA, σ) (k32 + 5 + 5) (C32 + 22 + 22) := by
    exact endHighSplitNotTaken h43 hhigh (by simp)
  have h113 : RD endBytecode I g (initState cA gh bl σ σ₀ g A I)
      endGroup114JumpdestPc [endSelWord I] solcFreePtrMem (UInt256.ofNat 3)
      ByteArray.empty (cA, σ) (k32 + 5 + 5 + 5) (C32 + 22 + 22 + 22) := by
    exact endHigh2SplitTaken h54 hhigh2 (by simp)
  have h114 : RD endBytecode I g (initState cA gh bl σ σ₀ g A I)
      endGroup114FirstArmPc [endSelWord I] solcFreePtrMem (UInt256.ofNat 3)
      ByteArray.empty (cA, σ) (k32 + 5 + 5 + 5 + 1) (C32 + 22 + 22 + 22 + 1) := by
    simpa [endGroup114FirstArmPc] using h113.jumpdest (by native_decide) (by simp)
  exact ⟨_, _, h114⟩

theorem endReachGroup174FirstArm {cA gh bl σ σ₀ A I} {g : Sat256}
    (hcode : I.code = endBytecode) (hwv : I.weiValue = ⟨0⟩)
    (hsz : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hroot : UInt256.gt (armSelNat endBytecode endRootSplitPc) (endSelWord I) = ⟨0⟩)
    (hhigh : UInt256.gt (armSelNat endBytecode endHighSplitPc) (endSelWord I) ≠ ⟨0⟩)
    (hmid : UInt256.gt (armSelNat endBytecode endHighMidSplitPc) (endSelWord I) = ⟨0⟩) :
    ∃ k C, RD endBytecode I g (initState cA gh bl σ σ₀ g A I)
        endGroup174FirstArmPc [endSelWord I] solcFreePtrMem (UInt256.ofNat 3)
        ByteArray.empty (cA, σ) k C := by
  obtain ⟨k32, C32, h32⟩ :=
    endReachRootSplit (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀)
      (A := A) (I := I) (g := g) hcode hwv hsz hsize
  have h43 : RD endBytecode I g (initState cA gh bl σ σ₀ g A I)
      endHighSplitPc [endSelWord I] solcFreePtrMem (UInt256.ofNat 3)
      ByteArray.empty (cA, σ) (k32 + 5) (C32 + 22) := by
    exact endRootSplitNotTaken h32 hroot (by simp)
  have h162 : RD endBytecode I g (initState cA gh bl σ σ₀ g A I)
      endHighJumpdestPc [endSelWord I] solcFreePtrMem (UInt256.ofNat 3)
      ByteArray.empty (cA, σ) (k32 + 5 + 5) (C32 + 22 + 22) := by
    exact endHighSplitTaken h43 hhigh (by simp)
  have h163 : RD endBytecode I g (initState cA gh bl σ σ₀ g A I)
      endHighMidSplitPc [endSelWord I] solcFreePtrMem (UInt256.ofNat 3)
      ByteArray.empty (cA, σ) (k32 + 5 + 5 + 1) (C32 + 22 + 22 + 1) := by
    simpa [endHighMidSplitPc] using h162.jumpdest (by native_decide) (by simp)
  have h174 : RD endBytecode I g (initState cA gh bl σ σ₀ g A I)
      endGroup174FirstArmPc [endSelWord I] solcFreePtrMem (UInt256.ofNat 3)
      ByteArray.empty (cA, σ) (k32 + 5 + 5 + 1 + 5) (C32 + 22 + 22 + 1 + 22) := by
    exact endHighMidSplitNotTaken h163 hmid (by simp)
  exact ⟨_, _, h174⟩

theorem endReachGroup223FirstArm {cA gh bl σ σ₀ A I} {g : Sat256}
    (hcode : I.code = endBytecode) (hwv : I.weiValue = ⟨0⟩)
    (hsz : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hroot : UInt256.gt (armSelNat endBytecode endRootSplitPc) (endSelWord I) = ⟨0⟩)
    (hhigh : UInt256.gt (armSelNat endBytecode endHighSplitPc) (endSelWord I) ≠ ⟨0⟩)
    (hmid : UInt256.gt (armSelNat endBytecode endHighMidSplitPc) (endSelWord I) ≠ ⟨0⟩) :
    ∃ k C, RD endBytecode I g (initState cA gh bl σ σ₀ g A I)
        endGroup223FirstArmPc [endSelWord I] solcFreePtrMem (UInt256.ofNat 3)
        ByteArray.empty (cA, σ) k C := by
  obtain ⟨k32, C32, h32⟩ :=
    endReachRootSplit (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀)
      (A := A) (I := I) (g := g) hcode hwv hsz hsize
  have h43 : RD endBytecode I g (initState cA gh bl σ σ₀ g A I)
      endHighSplitPc [endSelWord I] solcFreePtrMem (UInt256.ofNat 3)
      ByteArray.empty (cA, σ) (k32 + 5) (C32 + 22) := by
    exact endRootSplitNotTaken h32 hroot (by simp)
  have h162 : RD endBytecode I g (initState cA gh bl σ σ₀ g A I)
      endHighJumpdestPc [endSelWord I] solcFreePtrMem (UInt256.ofNat 3)
      ByteArray.empty (cA, σ) (k32 + 5 + 5) (C32 + 22 + 22) := by
    exact endHighSplitTaken h43 hhigh (by simp)
  have h163 : RD endBytecode I g (initState cA gh bl σ σ₀ g A I)
      endHighMidSplitPc [endSelWord I] solcFreePtrMem (UInt256.ofNat 3)
      ByteArray.empty (cA, σ) (k32 + 5 + 5 + 1) (C32 + 22 + 22 + 1) := by
    simpa [endHighMidSplitPc] using h162.jumpdest (by native_decide) (by simp)
  have h222 : RD endBytecode I g (initState cA gh bl σ σ₀ g A I)
      endGroup223JumpdestPc [endSelWord I] solcFreePtrMem (UInt256.ofNat 3)
      ByteArray.empty (cA, σ) (k32 + 5 + 5 + 1 + 5) (C32 + 22 + 22 + 1 + 22) := by
    exact endHighMidSplitTaken h163 hmid (by simp)
  have h223 : RD endBytecode I g (initState cA gh bl σ σ₀ g A I)
      endGroup223FirstArmPc [endSelWord I] solcFreePtrMem (UInt256.ofNat 3)
      ByteArray.empty (cA, σ) (k32 + 5 + 5 + 1 + 5 + 1)
        (C32 + 22 + 22 + 1 + 22 + 1) := by
    simpa [endGroup223FirstArmPc] using h222.jumpdest (by native_decide) (by simp)
  exact ⟨_, _, h223⟩

theorem endReachGroup294FirstArm {cA gh bl σ σ₀ A I} {g : Sat256}
    (hcode : I.code = endBytecode) (hwv : I.weiValue = ⟨0⟩)
    (hsz : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hroot : UInt256.gt (armSelNat endBytecode endRootSplitPc) (endSelWord I) ≠ ⟨0⟩)
    (hlow1 : UInt256.gt (armSelNat endBytecode endLow1SplitPc) (endSelWord I) = ⟨0⟩)
    (hlowHigh : UInt256.gt (armSelNat endBytecode endLowHighSplitPc) (endSelWord I) = ⟨0⟩) :
    ∃ k C, RD endBytecode I g (initState cA gh bl σ σ₀ g A I)
        endGroup294FirstArmPc [endSelWord I] solcFreePtrMem (UInt256.ofNat 3)
        ByteArray.empty (cA, σ) k C := by
  obtain ⟨k32, C32, h32⟩ :=
    endReachRootSplit (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀)
      (A := A) (I := I) (g := g) hcode hwv hsz hsize
  have h271 : RD endBytecode I g (initState cA gh bl σ σ₀ g A I)
      endLow1JumpdestPc [endSelWord I] solcFreePtrMem (UInt256.ofNat 3)
      ByteArray.empty (cA, σ) (k32 + 5) (C32 + 22) := by
    exact endRootSplitTaken h32 hroot (by simp)
  have h272 : RD endBytecode I g (initState cA gh bl σ σ₀ g A I)
      endLow1SplitPc [endSelWord I] solcFreePtrMem (UInt256.ofNat 3)
      ByteArray.empty (cA, σ) (k32 + 5 + 1) (C32 + 22 + 1) := by
    simpa [endLow1SplitPc] using h271.jumpdest (by native_decide) (by simp)
  have h283 : RD endBytecode I g (initState cA gh bl σ σ₀ g A I)
      endLowHighSplitPc [endSelWord I] solcFreePtrMem (UInt256.ofNat 3)
      ByteArray.empty (cA, σ) (k32 + 5 + 1 + 5) (C32 + 22 + 1 + 22) := by
    exact endLow1SplitNotTaken h272 hlow1 (by simp)
  have h294 : RD endBytecode I g (initState cA gh bl σ σ₀ g A I)
      endGroup294FirstArmPc [endSelWord I] solcFreePtrMem (UInt256.ofNat 3)
      ByteArray.empty (cA, σ) (k32 + 5 + 1 + 5 + 5) (C32 + 22 + 1 + 22 + 22) := by
    exact endLowHighSplitNotTaken h283 hlowHigh (by simp)
  exact ⟨_, _, h294⟩

theorem endReachGroup343FirstArm {cA gh bl σ σ₀ A I} {g : Sat256}
    (hcode : I.code = endBytecode) (hwv : I.weiValue = ⟨0⟩)
    (hsz : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hroot : UInt256.gt (armSelNat endBytecode endRootSplitPc) (endSelWord I) ≠ ⟨0⟩)
    (hlow1 : UInt256.gt (armSelNat endBytecode endLow1SplitPc) (endSelWord I) = ⟨0⟩)
    (hlowHigh : UInt256.gt (armSelNat endBytecode endLowHighSplitPc) (endSelWord I) ≠ ⟨0⟩) :
    ∃ k C, RD endBytecode I g (initState cA gh bl σ σ₀ g A I)
        endGroup343FirstArmPc [endSelWord I] solcFreePtrMem (UInt256.ofNat 3)
        ByteArray.empty (cA, σ) k C := by
  obtain ⟨k32, C32, h32⟩ :=
    endReachRootSplit (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀)
      (A := A) (I := I) (g := g) hcode hwv hsz hsize
  have h271 : RD endBytecode I g (initState cA gh bl σ σ₀ g A I)
      endLow1JumpdestPc [endSelWord I] solcFreePtrMem (UInt256.ofNat 3)
      ByteArray.empty (cA, σ) (k32 + 5) (C32 + 22) := by
    exact endRootSplitTaken h32 hroot (by simp)
  have h272 : RD endBytecode I g (initState cA gh bl σ σ₀ g A I)
      endLow1SplitPc [endSelWord I] solcFreePtrMem (UInt256.ofNat 3)
      ByteArray.empty (cA, σ) (k32 + 5 + 1) (C32 + 22 + 1) := by
    simpa [endLow1SplitPc] using h271.jumpdest (by native_decide) (by simp)
  have h283 : RD endBytecode I g (initState cA gh bl σ σ₀ g A I)
      endLowHighSplitPc [endSelWord I] solcFreePtrMem (UInt256.ofNat 3)
      ByteArray.empty (cA, σ) (k32 + 5 + 1 + 5) (C32 + 22 + 1 + 22) := by
    exact endLow1SplitNotTaken h272 hlow1 (by simp)
  have h342 : RD endBytecode I g (initState cA gh bl σ σ₀ g A I)
      endGroup343JumpdestPc [endSelWord I] solcFreePtrMem (UInt256.ofNat 3)
      ByteArray.empty (cA, σ) (k32 + 5 + 1 + 5 + 5) (C32 + 22 + 1 + 22 + 22) := by
    exact endLowHighSplitTaken h283 hlowHigh (by simp)
  have h343 : RD endBytecode I g (initState cA gh bl σ σ₀ g A I)
      endGroup343FirstArmPc [endSelWord I] solcFreePtrMem (UInt256.ofNat 3)
      ByteArray.empty (cA, σ) (k32 + 5 + 1 + 5 + 5 + 1)
        (C32 + 22 + 1 + 22 + 22 + 1) := by
    simpa [endGroup343FirstArmPc] using h342.jumpdest (by native_decide) (by simp)
  exact ⟨_, _, h343⟩

theorem endReachGroup403FirstArm {cA gh bl σ σ₀ A I} {g : Sat256}
    (hcode : I.code = endBytecode) (hwv : I.weiValue = ⟨0⟩)
    (hsz : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hroot : UInt256.gt (armSelNat endBytecode endRootSplitPc) (endSelWord I) ≠ ⟨0⟩)
    (hlow1 : UInt256.gt (armSelNat endBytecode endLow1SplitPc) (endSelWord I) ≠ ⟨0⟩)
    (hlow2 : UInt256.gt (armSelNat endBytecode endLow2SplitPc) (endSelWord I) = ⟨0⟩) :
    ∃ k C, RD endBytecode I g (initState cA gh bl σ σ₀ g A I)
        endGroup403FirstArmPc [endSelWord I] solcFreePtrMem (UInt256.ofNat 3)
        ByteArray.empty (cA, σ) k C := by
  obtain ⟨k32, C32, h32⟩ :=
    endReachRootSplit (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀)
      (A := A) (I := I) (g := g) hcode hwv hsz hsize
  have h271 : RD endBytecode I g (initState cA gh bl σ σ₀ g A I)
      endLow1JumpdestPc [endSelWord I] solcFreePtrMem (UInt256.ofNat 3)
      ByteArray.empty (cA, σ) (k32 + 5) (C32 + 22) := by
    exact endRootSplitTaken h32 hroot (by simp)
  have h272 : RD endBytecode I g (initState cA gh bl σ σ₀ g A I)
      endLow1SplitPc [endSelWord I] solcFreePtrMem (UInt256.ofNat 3)
      ByteArray.empty (cA, σ) (k32 + 5 + 1) (C32 + 22 + 1) := by
    simpa [endLow1SplitPc] using h271.jumpdest (by native_decide) (by simp)
  have h391 : RD endBytecode I g (initState cA gh bl σ σ₀ g A I)
      endLow2JumpdestPc [endSelWord I] solcFreePtrMem (UInt256.ofNat 3)
      ByteArray.empty (cA, σ) (k32 + 5 + 1 + 5) (C32 + 22 + 1 + 22) := by
    exact endLow1SplitTaken h272 hlow1 (by simp)
  have h392 : RD endBytecode I g (initState cA gh bl σ σ₀ g A I)
      endLow2SplitPc [endSelWord I] solcFreePtrMem (UInt256.ofNat 3)
      ByteArray.empty (cA, σ) (k32 + 5 + 1 + 5 + 1) (C32 + 22 + 1 + 22 + 1) := by
    simpa [endLow2SplitPc] using h391.jumpdest (by native_decide) (by simp)
  have h403 : RD endBytecode I g (initState cA gh bl σ σ₀ g A I)
      endGroup403FirstArmPc [endSelWord I] solcFreePtrMem (UInt256.ofNat 3)
      ByteArray.empty (cA, σ) (k32 + 5 + 1 + 5 + 1 + 5)
        (C32 + 22 + 1 + 22 + 1 + 22) := by
    exact endLow2SplitNotTaken h392 hlow2 (by simp)
  exact ⟨_, _, h403⟩

theorem endJumpToNoMatchRevert {cA gh bl σ σ₀ A I} {g : Sat256} {pc : UInt256}
    {k C : ℕ}
    (h : RD endBytecode I g (initState cA gh bl σ σ₀ g A I) pc
      [endSelWord I] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C)
    (hpush : decode endBytecode pc = some (.Push .PUSH2, some (endDispatchRevertPc, 2)))
    (hjump : decode endBytecode (pc + UInt256.ofNat 3) = some (.JUMP, .none)) :
    RDrev endBytecode g (initState cA gh bl σ σ₀ g A I) := by
  have h496 := h.push2 endDispatchRevertPc hpush (by simp only [List.length_singleton]; omega)
    |>.jump hjump (by jump_dest) (by simp only [List.length_singleton]; omega)
    |>.jumpdest (by native_decide) (by simp only [List.length_singleton]; omega)
  exact RD.solcPush1Dup1Revert0 h496 (by native_decide) (by native_decide)
    (by native_decide) (by simp only [List.length_singleton]; omega)

theorem endGroup65NoMatchRevert {cA gh bl σ σ₀ A I} {g : Sat256} {k C : ℕ}
    (h : RD endBytecode I g (initState cA gh bl σ σ₀ g A I) endGroup65FirstArmPc
      [endSelWord I] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C)
    (heq0 : ∀ j, j < 4 →
      UInt256.eq (armSelNat endBytecode (nthArmPc endBytecode endGroup65FirstArmPc j))
        (endSelWord I) = ⟨0⟩) :
    RDrev endBytecode g (initState cA gh bl σ σ₀ g A I) := by
  have h109 := h
    |>.selectorArmNotTakenAuto (endGroup65ArmsWellFormed 0 (by omega))
        (heq0 0 (by omega)) (by simp)
    |>.selectorArmNotTakenAuto (endGroup65ArmsWellFormed 1 (by omega))
        (heq0 1 (by omega)) (by simp)
    |>.selectorArmNotTakenAuto (endGroup65ArmsWellFormed 2 (by omega))
        (heq0 2 (by omega)) (by simp)
    |>.selectorArmNotTakenAuto (endGroup65ArmsWellFormed 3 (by omega))
        (heq0 3 (by omega)) (by simp)
  exact endJumpToNoMatchRevert h109 (by native_decide) (by native_decide)

theorem endGroup114NoMatchRevert {cA gh bl σ σ₀ A I} {g : Sat256} {k C : ℕ}
    (h : RD endBytecode I g (initState cA gh bl σ σ₀ g A I) endGroup114FirstArmPc
      [endSelWord I] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C)
    (heq0 : ∀ j, j < 4 →
      UInt256.eq (armSelNat endBytecode (nthArmPc endBytecode endGroup114FirstArmPc j))
        (endSelWord I) = ⟨0⟩) :
    RDrev endBytecode g (initState cA gh bl σ σ₀ g A I) := by
  have h158 := h
    |>.selectorArmNotTakenAuto (endGroup114ArmsWellFormed 0 (by omega))
        (heq0 0 (by omega)) (by simp)
    |>.selectorArmNotTakenAuto (endGroup114ArmsWellFormed 1 (by omega))
        (heq0 1 (by omega)) (by simp)
    |>.selectorArmNotTakenAuto (endGroup114ArmsWellFormed 2 (by omega))
        (heq0 2 (by omega)) (by simp)
    |>.selectorArmNotTakenAuto (endGroup114ArmsWellFormed 3 (by omega))
        (heq0 3 (by omega)) (by simp)
  exact endJumpToNoMatchRevert h158 (by native_decide) (by native_decide)

theorem endGroup174NoMatchRevert {cA gh bl σ σ₀ A I} {g : Sat256} {k C : ℕ}
    (h : RD endBytecode I g (initState cA gh bl σ σ₀ g A I) endGroup174FirstArmPc
      [endSelWord I] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C)
    (heq0 : ∀ j, j < 4 →
      UInt256.eq (armSelNat endBytecode (nthArmPc endBytecode endGroup174FirstArmPc j))
        (endSelWord I) = ⟨0⟩) :
    RDrev endBytecode g (initState cA gh bl σ σ₀ g A I) := by
  have h218 := h
    |>.selectorArmNotTakenAuto (endGroup174ArmsWellFormed 0 (by omega))
        (heq0 0 (by omega)) (by simp)
    |>.selectorArmNotTakenAuto (endGroup174ArmsWellFormed 1 (by omega))
        (heq0 1 (by omega)) (by simp)
    |>.selectorArmNotTakenAuto (endGroup174ArmsWellFormed 2 (by omega))
        (heq0 2 (by omega)) (by simp)
    |>.selectorArmNotTakenAuto (endGroup174ArmsWellFormed 3 (by omega))
        (heq0 3 (by omega)) (by simp)
  exact endJumpToNoMatchRevert h218 (by native_decide) (by native_decide)

theorem endGroup223NoMatchRevert {cA gh bl σ σ₀ A I} {g : Sat256} {k C : ℕ}
    (h : RD endBytecode I g (initState cA gh bl σ σ₀ g A I) endGroup223FirstArmPc
      [endSelWord I] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C)
    (heq0 : ∀ j, j < 4 →
      UInt256.eq (armSelNat endBytecode (nthArmPc endBytecode endGroup223FirstArmPc j))
        (endSelWord I) = ⟨0⟩) :
    RDrev endBytecode g (initState cA gh bl σ σ₀ g A I) := by
  have h267 := h
    |>.selectorArmNotTakenAuto (endGroup223ArmsWellFormed 0 (by omega))
        (heq0 0 (by omega)) (by simp)
    |>.selectorArmNotTakenAuto (endGroup223ArmsWellFormed 1 (by omega))
        (heq0 1 (by omega)) (by simp)
    |>.selectorArmNotTakenAuto (endGroup223ArmsWellFormed 2 (by omega))
        (heq0 2 (by omega)) (by simp)
    |>.selectorArmNotTakenAuto (endGroup223ArmsWellFormed 3 (by omega))
        (heq0 3 (by omega)) (by simp)
  exact endJumpToNoMatchRevert h267 (by native_decide) (by native_decide)

theorem endGroup294NoMatchRevert {cA gh bl σ σ₀ A I} {g : Sat256} {k C : ℕ}
    (h : RD endBytecode I g (initState cA gh bl σ σ₀ g A I) endGroup294FirstArmPc
      [endSelWord I] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C)
    (heq0 : ∀ j, j < 4 →
      UInt256.eq (armSelNat endBytecode (nthArmPc endBytecode endGroup294FirstArmPc j))
        (endSelWord I) = ⟨0⟩) :
    RDrev endBytecode g (initState cA gh bl σ σ₀ g A I) := by
  have h338 := h
    |>.selectorArmNotTakenAuto (endGroup294ArmsWellFormed 0 (by omega))
        (heq0 0 (by omega)) (by simp)
    |>.selectorArmNotTakenAuto (endGroup294ArmsWellFormed 1 (by omega))
        (heq0 1 (by omega)) (by simp)
    |>.selectorArmNotTakenAuto (endGroup294ArmsWellFormed 2 (by omega))
        (heq0 2 (by omega)) (by simp)
    |>.selectorArmNotTakenAuto (endGroup294ArmsWellFormed 3 (by omega))
        (heq0 3 (by omega)) (by simp)
  exact endJumpToNoMatchRevert h338 (by native_decide) (by native_decide)

theorem endGroup343NoMatchRevert {cA gh bl σ σ₀ A I} {g : Sat256} {k C : ℕ}
    (h : RD endBytecode I g (initState cA gh bl σ σ₀ g A I) endGroup343FirstArmPc
      [endSelWord I] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C)
    (heq0 : ∀ j, j < 4 →
      UInt256.eq (armSelNat endBytecode (nthArmPc endBytecode endGroup343FirstArmPc j))
        (endSelWord I) = ⟨0⟩) :
    RDrev endBytecode g (initState cA gh bl σ σ₀ g A I) := by
  have h387 := h
    |>.selectorArmNotTakenAuto (endGroup343ArmsWellFormed 0 (by omega))
        (heq0 0 (by omega)) (by simp)
    |>.selectorArmNotTakenAuto (endGroup343ArmsWellFormed 1 (by omega))
        (heq0 1 (by omega)) (by simp)
    |>.selectorArmNotTakenAuto (endGroup343ArmsWellFormed 2 (by omega))
        (heq0 2 (by omega)) (by simp)
    |>.selectorArmNotTakenAuto (endGroup343ArmsWellFormed 3 (by omega))
        (heq0 3 (by omega)) (by simp)
  exact endJumpToNoMatchRevert h387 (by native_decide) (by native_decide)

theorem endGroup403NoMatchRevert {cA gh bl σ σ₀ A I} {g : Sat256} {k C : ℕ}
    (h : RD endBytecode I g (initState cA gh bl σ σ₀ g A I) endGroup403FirstArmPc
      [endSelWord I] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C)
    (heq0 : ∀ j, j < 4 →
      UInt256.eq (armSelNat endBytecode (nthArmPc endBytecode endGroup403FirstArmPc j))
        (endSelWord I) = ⟨0⟩) :
    RDrev endBytecode g (initState cA gh bl σ σ₀ g A I) := by
  have h447 := h
    |>.selectorArmNotTakenAuto (endGroup403ArmsWellFormed 0 (by omega))
        (heq0 0 (by omega)) (by simp)
    |>.selectorArmNotTakenAuto (endGroup403ArmsWellFormed 1 (by omega))
        (heq0 1 (by omega)) (by simp)
    |>.selectorArmNotTakenAuto (endGroup403ArmsWellFormed 2 (by omega))
        (heq0 2 (by omega)) (by simp)
    |>.selectorArmNotTakenAuto (endGroup403ArmsWellFormed 3 (by omega))
        (heq0 3 (by omega)) (by simp)
  exact endJumpToNoMatchRevert h447 (by native_decide) (by native_decide)

theorem endGroup452NoMatchRevert {cA gh bl σ σ₀ A I} {g : Sat256} {k C : ℕ}
    (h : RD endBytecode I g (initState cA gh bl σ σ₀ g A I) endDebtFirstArmPc
      [endSelWord I] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C)
    (heq0 : ∀ j, j < 4 →
      UInt256.eq (armSelNat endBytecode (nthArmPc endBytecode endDebtFirstArmPc j))
        (endSelWord I) = ⟨0⟩) :
    RDrev endBytecode g (initState cA gh bl σ σ₀ g A I) := by
  have h496 := h
    |>.selectorArmNotTakenAuto (endGroup452ArmsWellFormed 0 (by omega))
        (heq0 0 (by omega)) (by simp)
    |>.selectorArmNotTakenAuto (endGroup452ArmsWellFormed 1 (by omega))
        (heq0 1 (by omega)) (by simp)
    |>.selectorArmNotTakenAuto (endGroup452ArmsWellFormed 2 (by omega))
        (heq0 2 (by omega)) (by simp)
    |>.selectorArmNotTakenAuto (endGroup452ArmsWellFormed 3 (by omega))
        (heq0 3 (by omega)) (by simp)
    |>.jumpdest (by native_decide) (by simp only [List.length_singleton]; omega)
  exact RD.solcPush1Dup1Revert0 h496 (by native_decide) (by native_decide)
    (by native_decide) (by simp only [List.length_singleton]; omega)

theorem endBodyReverts_nonPayable (t : TransitionDecl) (ht : t ∈ contract.transitions)
    (evm : EVM.State) (locals : Store) (h : evm.executionEnv.weiValue ≠ ⟨0⟩) :
    ExecTransitionBody config contract evm locals t.body .reverted := by
  simp [contract, transitions] at ht
  rcases ht with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl
  all_goals exact bodyReverts_nonPayable h

theorem endX_callvalue_ne {cA gh bl σ σ₀ A I} {g : Sat256}
    (hcode : I.code = endBytecode) (hwv : I.weiValue ≠ ⟨0⟩) :
    RDrev endBytecode g (initState cA gh bl σ σ₀ g A I) := by
  have h0 := solcGuardPrologueRD (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀)
    (A := A) (g := g) hcode (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide)
  have h12 := h0.push2 ⟨16⟩ (by native_decide) (by simp only [List.length]; omega)
    |>.jumpiNT (by native_decide) (isZero_eq_zero_of_ne hwv)
      (by simp only [List.length]; omega)
  exact RD.solcPush1Dup1Revert0 h12 (by native_decide) (by native_decide)
    (by native_decide) (by simp only [List.length]; omega)

theorem endX_short {cA gh bl σ σ₀ A I} {g : Sat256}
    (hcode : I.code = endBytecode) (hwv : I.weiValue = ⟨0⟩)
    (hsz : I.calldata.size < 4) :
    RDrev endBytecode g (initState cA gh bl σ σ₀ g A I) := by
  have h0 := solcGuardPrologueRD (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀)
    (A := A) (g := g) hcode (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide)
  obtain ⟨_, _, h1⟩ := solcGuardCallvalueZero
    (ctgt := solcGuardTgt endBytecode)
    (opC := solcGuardTgtOp endBytecode)
    (wC := solcGuardTgtWidth endBytecode) h0 hwv
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by jump_dest)
  have h496 := h1.push1 ⟨4⟩ (by native_decide) (by simp only [List.length]; omega)
    |>.calldatasize (by native_decide) (by simp only [List.length]; omega)
    |>.lt (by native_decide) (by simp only [List.length]; omega)
    |>.push2 endDispatchRevertPc (by native_decide) (by simp only [List.length]; omega)
    |>.jumpiT (by native_decide) (lt_four_ne_zero_of_lt hsz) (by jump_dest)
      (by simp only [List.length]; omega)
    |>.jumpdest (by native_decide) (by simp only [List.length]; omega)
  exact RD.solcPush1Dup1Revert0 h496 (by native_decide) (by native_decide)
    (by native_decide) (by simp only [List.length]; omega)

theorem endX_noMatch {cA gh bl σ σ₀ A I} {g : Sat256}
    (hcode : I.code = endBytecode) (hwv : I.weiValue = ⟨0⟩)
    (hsz : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hnm : ∀ i, i < 32 → (endSelBytes i == I.calldata.extract 0 4) = false) :
    RDrev endBytecode g (initState cA gh bl σ σ₀ g A I) := by
  have heq65 : ∀ j, j < 4 →
      UInt256.eq
        (armSelNat endBytecode (nthArmPc endBytecode endGroup65FirstArmPc j))
        (endSelWord I) = ⟨0⟩ := by
    intro j hj
    interval_cases j
    · rw [endGroup65ArmEq I hsz 0 (by omega)]
      have hfalse : (endGroup65SelBytes 0 == I.calldata.extract 0 4) = false := by
        simpa [endGroup65SelBytes, endSelBytes] using hnm 2 (by omega)
      rw [hfalse]; rfl
    · rw [endGroup65ArmEq I hsz 1 (by omega)]
      have hfalse : (endGroup65SelBytes 1 == I.calldata.extract 0 4) = false := by
        simpa [endGroup65SelBytes, endSelBytes] using hnm 13 (by omega)
      rw [hfalse]; rfl
    · rw [endGroup65ArmEq I hsz 2 (by omega)]
      have hfalse : (endGroup65SelBytes 2 == I.calldata.extract 0 4) = false := by
        simpa [endGroup65SelBytes, endSelBytes] using hnm 12 (by omega)
      rw [hfalse]; rfl
    · rw [endGroup65ArmEq I hsz 3 (by omega)]
      have hfalse : (endGroup65SelBytes 3 == I.calldata.extract 0 4) = false := by
        simpa [endGroup65SelBytes, endSelBytes] using hnm 31 (by omega)
      rw [hfalse]; rfl
  have heq114 : ∀ j, j < 4 →
      UInt256.eq
        (armSelNat endBytecode (nthArmPc endBytecode endGroup114FirstArmPc j))
        (endSelWord I) = ⟨0⟩ := by
    intro j hj
    interval_cases j
    · rw [endGroup114ArmEq I hsz 0 (by omega)]
      have hfalse : (endGroup114SelBytes 0 == I.calldata.extract 0 4) = false := by
        simpa [endGroup114SelBytes, endSelBytes] using hnm 20 (by omega)
      rw [hfalse]; rfl
    · rw [endGroup114ArmEq I hsz 1 (by omega)]
      have hfalse : (endGroup114SelBytes 1 == I.calldata.extract 0 4) = false := by
        simpa [endGroup114SelBytes, endSelBytes] using hnm 14 (by omega)
      rw [hfalse]; rfl
    · rw [endGroup114ArmEq I hsz 2 (by omega)]
      have hfalse : (endGroup114SelBytes 2 == I.calldata.extract 0 4) = false := by
        simpa [endGroup114SelBytes, endSelBytes] using hnm 23 (by omega)
      rw [hfalse]; rfl
    · rw [endGroup114ArmEq I hsz 3 (by omega)]
      have hfalse : (endGroup114SelBytes 3 == I.calldata.extract 0 4) = false := by
        simpa [endGroup114SelBytes, endSelBytes] using hnm 9 (by omega)
      rw [hfalse]; rfl
  have heq174 : ∀ j, j < 4 →
      UInt256.eq
        (armSelNat endBytecode (nthArmPc endBytecode endGroup174FirstArmPc j))
        (endSelWord I) = ⟨0⟩ := by
    intro j hj
    interval_cases j
    · rw [endGroup174ArmEq I hsz 0 (by omega)]
      have hfalse : (endGroup174SelBytes 0 == I.calldata.extract 0 4) = false := by
        simpa [endGroup174SelBytes, endSelBytes] using hnm 0 (by omega)
      rw [hfalse]; rfl
    · rw [endGroup174ArmEq I hsz 1 (by omega)]
      have hfalse : (endGroup174SelBytes 1 == I.calldata.extract 0 4) = false := by
        simpa [endGroup174SelBytes, endSelBytes] using hnm 3 (by omega)
      rw [hfalse]; rfl
    · rw [endGroup174ArmEq I hsz 2 (by omega)]
      have hfalse : (endGroup174SelBytes 2 == I.calldata.extract 0 4) = false := by
        simpa [endGroup174SelBytes, endSelBytes] using hnm 27 (by omega)
      rw [hfalse]; rfl
    · rw [endGroup174ArmEq I hsz 3 (by omega)]
      have hfalse : (endGroup174SelBytes 3 == I.calldata.extract 0 4) = false := by
        simpa [endGroup174SelBytes, endSelBytes] using hnm 17 (by omega)
      rw [hfalse]; rfl
  have heq223 : ∀ j, j < 4 →
      UInt256.eq
        (armSelNat endBytecode (nthArmPc endBytecode endGroup223FirstArmPc j))
        (endSelWord I) = ⟨0⟩ := by
    intro j hj
    interval_cases j
    · rw [endGroup223ArmEq I hsz 0 (by omega)]
      have hfalse : (endGroup223SelBytes 0 == I.calldata.extract 0 4) = false := by
        simpa [endGroup223SelBytes, endSelBytes] using hnm 26 (by omega)
      rw [hfalse]; rfl
    · rw [endGroup223ArmEq I hsz 1 (by omega)]
      have hfalse : (endGroup223SelBytes 1 == I.calldata.extract 0 4) = false := by
        simpa [endGroup223SelBytes, endSelBytes] using hnm 16 (by omega)
      rw [hfalse]; rfl
    · rw [endGroup223ArmEq I hsz 2 (by omega)]
      have hfalse : (endGroup223SelBytes 2 == I.calldata.extract 0 4) = false := by
        simpa [endGroup223SelBytes, endSelBytes] using hnm 8 (by omega)
      rw [hfalse]; rfl
    · rw [endGroup223ArmEq I hsz 3 (by omega)]
      have hfalse : (endGroup223SelBytes 3 == I.calldata.extract 0 4) = false := by
        simpa [endGroup223SelBytes, endSelBytes] using hnm 19 (by omega)
      rw [hfalse]; rfl
  have heq294 : ∀ j, j < 4 →
      UInt256.eq
        (armSelNat endBytecode (nthArmPc endBytecode endGroup294FirstArmPc j))
        (endSelWord I) = ⟨0⟩ := by
    intro j hj
    interval_cases j
    · rw [endGroup294ArmEq I hsz 0 (by omega)]
      have hfalse : (endGroup294SelBytes 0 == I.calldata.extract 0 4) = false := by
        simpa [endGroup294SelBytes, endSelBytes] using hnm 22 (by omega)
      rw [hfalse]; rfl
    · rw [endGroup294ArmEq I hsz 1 (by omega)]
      have hfalse : (endGroup294SelBytes 1 == I.calldata.extract 0 4) = false := by
        simpa [endGroup294SelBytes, endSelBytes] using hnm 30 (by omega)
      rw [hfalse]; rfl
    · rw [endGroup294ArmEq I hsz 2 (by omega)]
      have hfalse : (endGroup294SelBytes 2 == I.calldata.extract 0 4) = false := by
        simpa [endGroup294SelBytes, endSelBytes] using hnm 6 (by omega)
      rw [hfalse]; rfl
    · rw [endGroup294ArmEq I hsz 3 (by omega)]
      have hfalse : (endGroup294SelBytes 3 == I.calldata.extract 0 4) = false := by
        simpa [endGroup294SelBytes, endSelBytes] using hnm 7 (by omega)
      rw [hfalse]; rfl
  have heq343 : ∀ j, j < 4 →
      UInt256.eq
        (armSelNat endBytecode (nthArmPc endBytecode endGroup343FirstArmPc j))
        (endSelWord I) = ⟨0⟩ := by
    intro j hj
    interval_cases j
    · rw [endGroup343ArmEq I hsz 0 (by omega)]
      have hfalse : (endGroup343SelBytes 0 == I.calldata.extract 0 4) = false := by
        simpa [endGroup343SelBytes, endSelBytes] using hnm 4 (by omega)
      rw [hfalse]; rfl
    · rw [endGroup343ArmEq I hsz 1 (by omega)]
      have hfalse : (endGroup343SelBytes 1 == I.calldata.extract 0 4) = false := by
        simpa [endGroup343SelBytes, endSelBytes] using hnm 15 (by omega)
      rw [hfalse]; rfl
    · rw [endGroup343ArmEq I hsz 2 (by omega)]
      have hfalse : (endGroup343SelBytes 2 == I.calldata.extract 0 4) = false := by
        simpa [endGroup343SelBytes, endSelBytes] using hnm 10 (by omega)
      rw [hfalse]; rfl
    · rw [endGroup343ArmEq I hsz 3 (by omega)]
      have hfalse : (endGroup343SelBytes 3 == I.calldata.extract 0 4) = false := by
        simpa [endGroup343SelBytes, endSelBytes] using hnm 18 (by omega)
      rw [hfalse]; rfl
  have heq403 : ∀ j, j < 4 →
      UInt256.eq
        (armSelNat endBytecode (nthArmPc endBytecode endGroup403FirstArmPc j))
        (endSelWord I) = ⟨0⟩ := by
    intro j hj
    interval_cases j
    · rw [endGroup403ArmEq I hsz 0 (by omega)]
      have hfalse : (endGroup403SelBytes 0 == I.calldata.extract 0 4) = false := by
        simpa [endGroup403SelBytes, endSelBytes] using hnm 29 (by omega)
      rw [hfalse]; rfl
    · rw [endGroup403ArmEq I hsz 1 (by omega)]
      have hfalse : (endGroup403SelBytes 1 == I.calldata.extract 0 4) = false := by
        simpa [endGroup403SelBytes, endSelBytes] using hnm 5 (by omega)
      rw [hfalse]; rfl
    · rw [endGroup403ArmEq I hsz 2 (by omega)]
      have hfalse : (endGroup403SelBytes 2 == I.calldata.extract 0 4) = false := by
        simpa [endGroup403SelBytes, endSelBytes] using hnm 25 (by omega)
      rw [hfalse]; rfl
    · rw [endGroup403ArmEq I hsz 3 (by omega)]
      have hfalse : (endGroup403SelBytes 3 == I.calldata.extract 0 4) = false := by
        simpa [endGroup403SelBytes, endSelBytes] using hnm 28 (by omega)
      rw [hfalse]; rfl
  have heq452 : ∀ j, j < 4 →
      UInt256.eq
        (armSelNat endBytecode (nthArmPc endBytecode endDebtFirstArmPc j))
        (endSelWord I) = ⟨0⟩ := by
    intro j hj
    interval_cases j
    · rw [endGroup452ArmEq I hsz 0 (by omega)]
      have hfalse : (endGroup452SelBytes 0 == I.calldata.extract 0 4) = false := by
        simpa [endGroup452SelBytes, endSelBytes] using hnm 11 (by omega)
      rw [hfalse]; rfl
    · rw [endGroup452ArmEq I hsz 1 (by omega)]
      have hfalse : (endGroup452SelBytes 1 == I.calldata.extract 0 4) = false := by
        simpa [endGroup452SelBytes, endSelBytes] using hnm 21 (by omega)
      rw [hfalse]; rfl
    · rw [endGroup452ArmEq I hsz 2 (by omega)]
      have hfalse : (endGroup452SelBytes 2 == I.calldata.extract 0 4) = false := by
        simpa [endGroup452SelBytes, endSelBytes] using hnm 1 (by omega)
      rw [hfalse]; rfl
    · rw [endGroup452ArmEq I hsz 3 (by omega)]
      have hfalse : (endGroup452SelBytes 3 == I.calldata.extract 0 4) = false := by
        simpa [endGroup452SelBytes, endSelBytes] using hnm 24 (by omega)
      rw [hfalse]; rfl
  by_cases hroot : UInt256.gt (armSelNat endBytecode endRootSplitPc) (endSelWord I) ≠ ⟨0⟩
  · by_cases hlow1 : UInt256.gt (armSelNat endBytecode endLow1SplitPc) (endSelWord I) ≠ ⟨0⟩
    · by_cases hlow2 : UInt256.gt (armSelNat endBytecode endLow2SplitPc) (endSelWord I) ≠ ⟨0⟩
      · obtain ⟨_, _, hfirst⟩ :=
          endReachDebtFirstArm (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀)
            (A := A) (I := I) (g := g) hcode hwv hsz hsize hroot hlow1 hlow2
        exact endGroup452NoMatchRevert hfirst heq452
      · have hlow20 :
            UInt256.gt (armSelNat endBytecode endLow2SplitPc) (endSelWord I) = ⟨0⟩ := by
          by_contra hne
          exact hlow2 hne
        obtain ⟨_, _, hfirst⟩ :=
          endReachGroup403FirstArm (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀)
            (A := A) (I := I) (g := g) hcode hwv hsz hsize hroot hlow1 hlow20
        exact endGroup403NoMatchRevert hfirst heq403
    · have hlow10 :
          UInt256.gt (armSelNat endBytecode endLow1SplitPc) (endSelWord I) = ⟨0⟩ := by
        by_contra hne
        exact hlow1 hne
      by_cases hlowHigh :
          UInt256.gt (armSelNat endBytecode endLowHighSplitPc) (endSelWord I) ≠ ⟨0⟩
      · obtain ⟨_, _, hfirst⟩ :=
          endReachGroup343FirstArm (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀)
            (A := A) (I := I) (g := g) hcode hwv hsz hsize hroot hlow10 hlowHigh
        exact endGroup343NoMatchRevert hfirst heq343
      · have hlowHigh0 :
            UInt256.gt (armSelNat endBytecode endLowHighSplitPc) (endSelWord I) = ⟨0⟩ := by
          by_contra hne
          exact hlowHigh hne
        obtain ⟨_, _, hfirst⟩ :=
          endReachGroup294FirstArm (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀)
            (A := A) (I := I) (g := g) hcode hwv hsz hsize hroot hlow10 hlowHigh0
        exact endGroup294NoMatchRevert hfirst heq294
  · have hroot0 :
        UInt256.gt (armSelNat endBytecode endRootSplitPc) (endSelWord I) = ⟨0⟩ := by
      by_contra hne
      exact hroot hne
    by_cases hhigh : UInt256.gt (armSelNat endBytecode endHighSplitPc) (endSelWord I) ≠ ⟨0⟩
    · by_cases hmid :
          UInt256.gt (armSelNat endBytecode endHighMidSplitPc) (endSelWord I) ≠ ⟨0⟩
      · obtain ⟨_, _, hfirst⟩ :=
          endReachGroup223FirstArm (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀)
            (A := A) (I := I) (g := g) hcode hwv hsz hsize hroot0 hhigh hmid
        exact endGroup223NoMatchRevert hfirst heq223
      · have hmid0 :
            UInt256.gt (armSelNat endBytecode endHighMidSplitPc) (endSelWord I) = ⟨0⟩ := by
          by_contra hne
          exact hmid hne
        obtain ⟨_, _, hfirst⟩ :=
          endReachGroup174FirstArm (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀)
            (A := A) (I := I) (g := g) hcode hwv hsz hsize hroot0 hhigh hmid0
        exact endGroup174NoMatchRevert hfirst heq174
    · have hhigh0 :
          UInt256.gt (armSelNat endBytecode endHighSplitPc) (endSelWord I) = ⟨0⟩ := by
        by_contra hne
        exact hhigh hne
      by_cases hhigh2 :
          UInt256.gt (armSelNat endBytecode endHigh2SplitPc) (endSelWord I) ≠ ⟨0⟩
      · obtain ⟨_, _, hfirst⟩ :=
          endReachGroup114FirstArm (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀)
            (A := A) (I := I) (g := g) hcode hwv hsz hsize hroot0 hhigh0 hhigh2
        exact endGroup114NoMatchRevert hfirst heq114
      · have hhigh20 :
            UInt256.gt (armSelNat endBytecode endHigh2SplitPc) (endSelWord I) = ⟨0⟩ := by
          by_contra hne
          exact hhigh2 hne
        obtain ⟨_, _, hfirst⟩ :=
          endReachGroup65FirstArm (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀)
            (A := A) (I := I) (g := g) hcode hwv hsz hsize hroot0 hhigh0 hhigh20
        exact endGroup65NoMatchRevert hfirst heq65

theorem endNonPayable {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256}
    (hcode : I.code = endBytecode) (hwv : I.weiValue ≠ ⟨0⟩) :
    runtimeEquivalenceFor config contract cA gh bl σ_evm σ_solm σ₀ g A I := by
  exact (endX_callvalue_ne (g := Sat256.ofUInt256 g) hcode hwv).reEquivElim hcode
    fun _ _ hrev => by
      by_cases hdisp : dispatchMsg contract I.calldata = none
      · exact reEquiv_noDispatch hdisp hrev
      · obtain ⟨t, ht⟩ := Option.ne_none_iff_exists'.mp hdisp
        have htmem : t ∈ contract.transitions := by
          rw [dispatchMsg_eq_dispatchList contract I.calldata (by rfl)] at ht
          exact dispatchList_some_mem ht
        by_cases hdec : decodeCalldataWithMode config.abiDecodeMode (t.params.map Param.name)
            (transitionSignature t).paramTypes I.calldata = none
        · exact reEquiv_decodingFailed ht hdec hrev
        · obtain ⟨callargs, hca⟩ := Option.ne_none_iff_exists'.mp hdec
          exact reEquiv_execution ht hca
            (endBodyReverts_nonPayable t htmem
              (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I) callargs
              (by simp only [initState]; exact hwv))
            (by rw [hrev]; exact .revert rfl rfl)

theorem endNoDispatch {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256}
    (hcode : I.code = endBytecode)
    (hsize : I.calldata.size < UInt256.size)
    (hperm : I.perm = true)
    (hwv : I.weiValue = ⟨0⟩)
    (hwards : ¬ selIs I (selectorOf wardsTransition))
    (hvat : ¬ selIs I (selectorOf vatTransition))
    (hcat : ¬ selIs I (selectorOf catTransition))
    (hdog : ¬ selIs I (selectorOf dogTransition))
    (hvow : ¬ selIs I (selectorOf vowTransition))
    (hpot : ¬ selIs I (selectorOf potTransition))
    (hspot : ¬ selIs I (selectorOf spotTransition))
    (hcure : ¬ selIs I (selectorOf cureTransition))
    (hlive : ¬ selIs I (selectorOf liveTransition))
    (hwhen : ¬ selIs I (selectorOf whenTransition))
    (hwait : ¬ selIs I (selectorOf waitTransition))
    (hdebt : ¬ selIs I (selectorOf debtTransition))
    (htag : ¬ selIs I (selectorOf tagTransition))
    (hgap : ¬ selIs I (selectorOf gapTransition))
    (hArt : ¬ selIs I (selectorOf ArtTransition))
    (hfix : ¬ selIs I (selectorOf fixTransition))
    (hbag : ¬ selIs I (selectorOf bagTransition))
    (hout : ¬ selIs I (selectorOf outTransition))
    (hrely : ¬ selIs I (selectorOf relyTransition))
    (hdeny : ¬ selIs I (selectorOf denyTransition))
    (hfileAddress : ¬ selIs I (selectorOf fileAddressTransition))
    (hfileUint : ¬ selIs I (selectorOf fileUintTransition))
    (hcage : ¬ selIs I (selectorOf cageTransition))
    (hcageIlk : ¬ selIs I (selectorOf cageIlkTransition))
    (hsnip : ¬ selIs I (selectorOf snipTransition))
    (hskip : ¬ selIs I (selectorOf skipTransition))
    (hskim : ¬ selIs I (selectorOf skimTransition))
    (hfree : ¬ selIs I (selectorOf freeTransition))
    (hthaw : ¬ selIs I (selectorOf thawTransition))
    (hflow : ¬ selIs I (selectorOf flowTransition))
    (hpack : ¬ selIs I (selectorOf packTransition))
    (hcash : ¬ selIs I (selectorOf cashTransition))
    (hAccounts : accountMapEquiv σ_evm σ_solm) :
    runtimeEquivalenceFor config contract cA gh bl σ_evm σ_solm σ₀ g A I := by
  have hnm := endNoSelectorMatches hwards hvat hcat hdog hvow hpot hspot hcure hlive hwhen
    hwait hdebt htag hgap hArt hfix hbag hout hrely hdeny hfileAddress hfileUint hcage
    hcageIlk hsnip hskip hskim hfree hthaw hflow hpack hcash
  by_cases hsz : 4 ≤ I.calldata.size
  · exact (endX_noMatch (g := Sat256.ofUInt256 g) hcode hwv hsz hsize hnm)
      |>.reEquivNoDispatch hcode (endDispatch_none_nomatch hnm)
  · have hshort : I.calldata.size < 4 := by omega
    exact (endX_short (g := Sat256.ofUInt256 g) hcode hwv hshort)
      |>.reEquivNoDispatch hcode (endDispatch_none_short hshort)

end Benchmarks.Dss.End
