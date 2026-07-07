import Benchmarks.Dss.End.Cash
import Benchmarks.Dss.End.Pack
import Benchmarks.Dss.End.Flow
import Benchmarks.Dss.End.Thaw
import Benchmarks.Dss.End.Free
import Benchmarks.Dss.End.Skim
import Benchmarks.Dss.End.Skip
import Benchmarks.Dss.End.Snip
import Benchmarks.Dss.End.CageIlk
import Benchmarks.Dss.End.Cage
import Benchmarks.Dss.End.FileUint
import Benchmarks.Dss.End.FileAddress
import Benchmarks.Dss.End.Deny
import Benchmarks.Dss.End.Rely
import Benchmarks.Dss.End.Out
import Benchmarks.Dss.End.Bag
import Benchmarks.Dss.End.Fix
import Benchmarks.Dss.End.Art
import Benchmarks.Dss.End.Gap
import Benchmarks.Dss.End.Tag
import Benchmarks.Dss.End.Debt
import Benchmarks.Dss.End.Wait
import Benchmarks.Dss.End.When
import Benchmarks.Dss.End.Live
import Benchmarks.Dss.End.Cure
import Benchmarks.Dss.End.Spot
import Benchmarks.Dss.End.Pot
import Benchmarks.Dss.End.Vow
import Benchmarks.Dss.End.Dog
import Benchmarks.Dss.End.Cat
import Benchmarks.Dss.End.Vat
import Benchmarks.Dss.End.Wards

/-!
# MakerDAO/Sky DSS End dispatcher scaffold

Dispatcher-level obligations shared by `Correct.lean`. The non-payable and no-dispatch EVM traces
are left as leaves while the top-level routing is made explicit.
-/

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach Reasoning.Refinement

set_option maxRecDepth 2000000

namespace Benchmarks.Dss.End

abbrev endDispatchRevertPc : UInt256 := ⟨496⟩

attribute [local simp]
  wardsSelectorBytes
  vatSelectorBytes
  catSelectorBytes
  dogSelectorBytes
  vowSelectorBytes
  potSelectorBytes
  spotSelectorBytes
  cureSelectorBytes
  liveSelectorBytes
  whenSelectorBytes
  waitSelectorBytes
  debtSelectorBytes
  tagSelectorBytes
  gapSelectorBytes
  ArtSelectorBytes
  fixSelectorBytes
  bagSelectorBytes
  outSelectorBytes
  relySelectorBytes
  denySelectorBytes
  fileAddressSelectorBytes
  fileUintSelectorBytes
  cageSelectorBytes
  cageIlkSelectorBytes
  snipSelectorBytes
  skipSelectorBytes
  skimSelectorBytes
  freeSelectorBytes
  thawSelectorBytes
  flowSelectorBytes
  packSelectorBytes
  cashSelectorBytes

theorem endDispatchWards {I : ExecutionEnv} (hsel : selIs I (endSelBytes 0)) :
    dispatchMsg contract I.calldata = some wardsTransition := by
  have hcd : I.calldata.extract 0 4 = endSelBytes 0 := (byteArray_eq_of_beq hsel).symm
  rw [dispatchMsg_eq_dispatchList contract I.calldata (by rfl) (by rfl)]
  change dispatchList transitions I.calldata = some wardsTransition
  unfold transitions
  simp [dispatchList, selectorOf, hcd]
  native_decide

theorem endDispatchVat {I : ExecutionEnv} (hsel : selIs I (endSelBytes 1)) :
    dispatchMsg contract I.calldata = some vatTransition := by
  have hcd : I.calldata.extract 0 4 = endSelBytes 1 := (byteArray_eq_of_beq hsel).symm
  rw [dispatchMsg_eq_dispatchList contract I.calldata (by rfl) (by rfl)]
  change dispatchList transitions I.calldata = some vatTransition
  unfold transitions
  simp [dispatchList, selectorOf, hcd]
  native_decide

theorem endDispatchCat {I : ExecutionEnv} (hsel : selIs I (endSelBytes 2)) :
    dispatchMsg contract I.calldata = some catTransition := by
  have hcd : I.calldata.extract 0 4 = endSelBytes 2 := (byteArray_eq_of_beq hsel).symm
  rw [dispatchMsg_eq_dispatchList contract I.calldata (by rfl) (by rfl)]
  change dispatchList transitions I.calldata = some catTransition
  unfold transitions
  simp [dispatchList, selectorOf, hcd]
  native_decide

theorem endDispatchDog {I : ExecutionEnv} (hsel : selIs I (endSelBytes 3)) :
    dispatchMsg contract I.calldata = some dogTransition := by
  have hcd : I.calldata.extract 0 4 = endSelBytes 3 := (byteArray_eq_of_beq hsel).symm
  rw [dispatchMsg_eq_dispatchList contract I.calldata (by rfl) (by rfl)]
  change dispatchList transitions I.calldata = some dogTransition
  unfold transitions
  simp [dispatchList, selectorOf, hcd]
  native_decide

theorem endDispatchVow {I : ExecutionEnv} (hsel : selIs I (endSelBytes 4)) :
    dispatchMsg contract I.calldata = some vowTransition := by
  have hcd : I.calldata.extract 0 4 = endSelBytes 4 := (byteArray_eq_of_beq hsel).symm
  rw [dispatchMsg_eq_dispatchList contract I.calldata (by rfl) (by rfl)]
  change dispatchList transitions I.calldata = some vowTransition
  unfold transitions
  simp [dispatchList, selectorOf, hcd]
  native_decide

theorem endDispatchPot {I : ExecutionEnv} (hsel : selIs I (endSelBytes 5)) :
    dispatchMsg contract I.calldata = some potTransition := by
  have hcd : I.calldata.extract 0 4 = endSelBytes 5 := (byteArray_eq_of_beq hsel).symm
  rw [dispatchMsg_eq_dispatchList contract I.calldata (by rfl) (by rfl)]
  change dispatchList transitions I.calldata = some potTransition
  unfold transitions
  simp [dispatchList, selectorOf, hcd]
  native_decide

theorem endDispatchSpot {I : ExecutionEnv} (hsel : selIs I (endSelBytes 6)) :
    dispatchMsg contract I.calldata = some spotTransition := by
  have hcd : I.calldata.extract 0 4 = endSelBytes 6 := (byteArray_eq_of_beq hsel).symm
  rw [dispatchMsg_eq_dispatchList contract I.calldata (by rfl) (by rfl)]
  change dispatchList transitions I.calldata = some spotTransition
  unfold transitions
  simp [dispatchList, selectorOf, hcd]
  native_decide

theorem endDispatchCure {I : ExecutionEnv} (hsel : selIs I (endSelBytes 7)) :
    dispatchMsg contract I.calldata = some cureTransition := by
  have hcd : I.calldata.extract 0 4 = endSelBytes 7 := (byteArray_eq_of_beq hsel).symm
  rw [dispatchMsg_eq_dispatchList contract I.calldata (by rfl) (by rfl)]
  change dispatchList transitions I.calldata = some cureTransition
  unfold transitions
  simp [dispatchList, selectorOf, hcd]
  native_decide

theorem endDispatchLive {I : ExecutionEnv} (hsel : selIs I (endSelBytes 8)) :
    dispatchMsg contract I.calldata = some liveTransition := by
  have hcd : I.calldata.extract 0 4 = endSelBytes 8 := (byteArray_eq_of_beq hsel).symm
  rw [dispatchMsg_eq_dispatchList contract I.calldata (by rfl) (by rfl)]
  change dispatchList transitions I.calldata = some liveTransition
  unfold transitions
  simp [dispatchList, selectorOf, hcd]
  native_decide

theorem endDispatchWhen {I : ExecutionEnv} (hsel : selIs I (endSelBytes 9)) :
    dispatchMsg contract I.calldata = some whenTransition := by
  have hcd : I.calldata.extract 0 4 = endSelBytes 9 := (byteArray_eq_of_beq hsel).symm
  rw [dispatchMsg_eq_dispatchList contract I.calldata (by rfl) (by rfl)]
  change dispatchList transitions I.calldata = some whenTransition
  unfold transitions
  simp [dispatchList, selectorOf, hcd]
  native_decide

theorem endDispatchWait {I : ExecutionEnv} (hsel : selIs I (endSelBytes 10)) :
    dispatchMsg contract I.calldata = some waitTransition := by
  have hcd : I.calldata.extract 0 4 = endSelBytes 10 := (byteArray_eq_of_beq hsel).symm
  rw [dispatchMsg_eq_dispatchList contract I.calldata (by rfl) (by rfl)]
  change dispatchList transitions I.calldata = some waitTransition
  unfold transitions
  simp [dispatchList, selectorOf, hcd]
  native_decide

theorem endDispatchDebt {I : ExecutionEnv} (hsel : selIs I (endSelBytes 11)) :
    dispatchMsg contract I.calldata = some debtTransition := by
  have hcd : I.calldata.extract 0 4 = endSelBytes 11 := (byteArray_eq_of_beq hsel).symm
  rw [dispatchMsg_eq_dispatchList contract I.calldata (by rfl) (by rfl)]
  change dispatchList transitions I.calldata = some debtTransition
  unfold transitions
  simp [dispatchList, selectorOf, hcd]
  native_decide

theorem endDispatchTag {I : ExecutionEnv} (hsel : selIs I (endSelBytes 12)) :
    dispatchMsg contract I.calldata = some tagTransition := by
  have hcd : I.calldata.extract 0 4 = endSelBytes 12 := (byteArray_eq_of_beq hsel).symm
  rw [dispatchMsg_eq_dispatchList contract I.calldata (by rfl) (by rfl)]
  change dispatchList transitions I.calldata = some tagTransition
  unfold transitions
  simp [dispatchList, selectorOf, hcd]
  native_decide

theorem endDispatchGap {I : ExecutionEnv} (hsel : selIs I (endSelBytes 13)) :
    dispatchMsg contract I.calldata = some gapTransition := by
  have hcd : I.calldata.extract 0 4 = endSelBytes 13 := (byteArray_eq_of_beq hsel).symm
  rw [dispatchMsg_eq_dispatchList contract I.calldata (by rfl) (by rfl)]
  change dispatchList transitions I.calldata = some gapTransition
  unfold transitions
  simp [dispatchList, selectorOf, hcd]
  native_decide

theorem endDispatchArt {I : ExecutionEnv} (hsel : selIs I (endSelBytes 14)) :
    dispatchMsg contract I.calldata = some ArtTransition := by
  have hcd : I.calldata.extract 0 4 = endSelBytes 14 := (byteArray_eq_of_beq hsel).symm
  rw [dispatchMsg_eq_dispatchList contract I.calldata (by rfl) (by rfl)]
  change dispatchList transitions I.calldata = some ArtTransition
  unfold transitions
  simp [dispatchList, selectorOf, hcd]
  native_decide

theorem endDispatchFix {I : ExecutionEnv} (hsel : selIs I (endSelBytes 15)) :
    dispatchMsg contract I.calldata = some fixTransition := by
  have hcd : I.calldata.extract 0 4 = endSelBytes 15 := (byteArray_eq_of_beq hsel).symm
  rw [dispatchMsg_eq_dispatchList contract I.calldata (by rfl) (by rfl)]
  change dispatchList transitions I.calldata = some fixTransition
  unfold transitions
  simp [dispatchList, selectorOf, hcd]
  native_decide

theorem endDispatchBag {I : ExecutionEnv} (hsel : selIs I (endSelBytes 16)) :
    dispatchMsg contract I.calldata = some bagTransition := by
  have hcd : I.calldata.extract 0 4 = endSelBytes 16 := (byteArray_eq_of_beq hsel).symm
  rw [dispatchMsg_eq_dispatchList contract I.calldata (by rfl) (by rfl)]
  change dispatchList transitions I.calldata = some bagTransition
  unfold transitions
  simp [dispatchList, selectorOf, hcd]
  native_decide

theorem endDispatchOut {I : ExecutionEnv} (hsel : selIs I (endSelBytes 17)) :
    dispatchMsg contract I.calldata = some outTransition := by
  have hcd : I.calldata.extract 0 4 = endSelBytes 17 := (byteArray_eq_of_beq hsel).symm
  rw [dispatchMsg_eq_dispatchList contract I.calldata (by rfl) (by rfl)]
  change dispatchList transitions I.calldata = some outTransition
  unfold transitions
  simp [dispatchList, selectorOf, hcd]
  native_decide

theorem endDispatchRely {I : ExecutionEnv} (hsel : selIs I (endSelBytes 18)) :
    dispatchMsg contract I.calldata = some relyTransition := by
  have hcd : I.calldata.extract 0 4 = endSelBytes 18 := (byteArray_eq_of_beq hsel).symm
  rw [dispatchMsg_eq_dispatchList contract I.calldata (by rfl) (by rfl)]
  change dispatchList transitions I.calldata = some relyTransition
  unfold transitions
  simp [dispatchList, selectorOf, hcd]
  native_decide

theorem endDispatchDeny {I : ExecutionEnv} (hsel : selIs I (endSelBytes 19)) :
    dispatchMsg contract I.calldata = some denyTransition := by
  have hcd : I.calldata.extract 0 4 = endSelBytes 19 := (byteArray_eq_of_beq hsel).symm
  rw [dispatchMsg_eq_dispatchList contract I.calldata (by rfl) (by rfl)]
  change dispatchList transitions I.calldata = some denyTransition
  unfold transitions
  simp [dispatchList, selectorOf, hcd]
  native_decide

theorem endDispatchFileAddress {I : ExecutionEnv} (hsel : selIs I (endSelBytes 20)) :
    dispatchMsg contract I.calldata = some fileAddressTransition := by
  have hcd : I.calldata.extract 0 4 = endSelBytes 20 := (byteArray_eq_of_beq hsel).symm
  rw [dispatchMsg_eq_dispatchList contract I.calldata (by rfl) (by rfl)]
  change dispatchList transitions I.calldata = some fileAddressTransition
  unfold transitions
  simp [dispatchList, selectorOf, hcd]
  native_decide

theorem endDispatchFileUint {I : ExecutionEnv} (hsel : selIs I (endSelBytes 21)) :
    dispatchMsg contract I.calldata = some fileUintTransition := by
  have hcd : I.calldata.extract 0 4 = endSelBytes 21 := (byteArray_eq_of_beq hsel).symm
  rw [dispatchMsg_eq_dispatchList contract I.calldata (by rfl) (by rfl)]
  change dispatchList transitions I.calldata = some fileUintTransition
  unfold transitions
  simp [dispatchList, selectorOf, hcd]
  native_decide

theorem endDispatchCage {I : ExecutionEnv} (hsel : selIs I (endSelBytes 22)) :
    dispatchMsg contract I.calldata = some cageTransition := by
  have hcd : I.calldata.extract 0 4 = endSelBytes 22 := (byteArray_eq_of_beq hsel).symm
  rw [dispatchMsg_eq_dispatchList contract I.calldata (by rfl) (by rfl)]
  change dispatchList transitions I.calldata = some cageTransition
  unfold transitions
  simp [dispatchList, selectorOf, hcd]
  native_decide

theorem endDispatchCageIlk {I : ExecutionEnv} (hsel : selIs I (endSelBytes 23)) :
    dispatchMsg contract I.calldata = some cageIlkTransition := by
  have hcd : I.calldata.extract 0 4 = endSelBytes 23 := (byteArray_eq_of_beq hsel).symm
  rw [dispatchMsg_eq_dispatchList contract I.calldata (by rfl) (by rfl)]
  change dispatchList transitions I.calldata = some cageIlkTransition
  unfold transitions
  simp [dispatchList, selectorOf, hcd]
  native_decide

theorem endDispatchSnip {I : ExecutionEnv} (hsel : selIs I (endSelBytes 24)) :
    dispatchMsg contract I.calldata = some snipTransition := by
  have hcd : I.calldata.extract 0 4 = endSelBytes 24 := (byteArray_eq_of_beq hsel).symm
  rw [dispatchMsg_eq_dispatchList contract I.calldata (by rfl) (by rfl)]
  change dispatchList transitions I.calldata = some snipTransition
  unfold transitions
  simp [dispatchList, selectorOf, hcd]
  native_decide

theorem endDispatchSkip {I : ExecutionEnv} (hsel : selIs I (endSelBytes 25)) :
    dispatchMsg contract I.calldata = some skipTransition := by
  have hcd : I.calldata.extract 0 4 = endSelBytes 25 := (byteArray_eq_of_beq hsel).symm
  rw [dispatchMsg_eq_dispatchList contract I.calldata (by rfl) (by rfl)]
  change dispatchList transitions I.calldata = some skipTransition
  unfold transitions
  simp [dispatchList, selectorOf, hcd]
  native_decide

theorem endDispatchSkim {I : ExecutionEnv} (hsel : selIs I (endSelBytes 26)) :
    dispatchMsg contract I.calldata = some skimTransition := by
  have hcd : I.calldata.extract 0 4 = endSelBytes 26 := (byteArray_eq_of_beq hsel).symm
  rw [dispatchMsg_eq_dispatchList contract I.calldata (by rfl) (by rfl)]
  change dispatchList transitions I.calldata = some skimTransition
  unfold transitions
  simp [dispatchList, selectorOf, hcd]
  native_decide

theorem endDispatchFree {I : ExecutionEnv} (hsel : selIs I (endSelBytes 27)) :
    dispatchMsg contract I.calldata = some freeTransition := by
  have hcd : I.calldata.extract 0 4 = endSelBytes 27 := (byteArray_eq_of_beq hsel).symm
  rw [dispatchMsg_eq_dispatchList contract I.calldata (by rfl) (by rfl)]
  change dispatchList transitions I.calldata = some freeTransition
  unfold transitions
  simp [dispatchList, selectorOf, hcd]
  native_decide

theorem endDispatchThaw {I : ExecutionEnv} (hsel : selIs I (endSelBytes 28)) :
    dispatchMsg contract I.calldata = some thawTransition := by
  have hcd : I.calldata.extract 0 4 = endSelBytes 28 := (byteArray_eq_of_beq hsel).symm
  rw [dispatchMsg_eq_dispatchList contract I.calldata (by rfl) (by rfl)]
  change dispatchList transitions I.calldata = some thawTransition
  unfold transitions
  simp [dispatchList, selectorOf, hcd]
  native_decide

theorem endDispatchFlow {I : ExecutionEnv} (hsel : selIs I (endSelBytes 29)) :
    dispatchMsg contract I.calldata = some flowTransition := by
  have hcd : I.calldata.extract 0 4 = endSelBytes 29 := (byteArray_eq_of_beq hsel).symm
  rw [dispatchMsg_eq_dispatchList contract I.calldata (by rfl) (by rfl)]
  change dispatchList transitions I.calldata = some flowTransition
  unfold transitions
  simp [dispatchList, selectorOf, hcd]
  native_decide

theorem endDispatchPack {I : ExecutionEnv} (hsel : selIs I (endSelBytes 30)) :
    dispatchMsg contract I.calldata = some packTransition := by
  have hcd : I.calldata.extract 0 4 = endSelBytes 30 := (byteArray_eq_of_beq hsel).symm
  rw [dispatchMsg_eq_dispatchList contract I.calldata (by rfl) (by rfl)]
  change dispatchList transitions I.calldata = some packTransition
  unfold transitions
  simp [dispatchList, selectorOf, hcd]
  native_decide

theorem endDispatchCash {I : ExecutionEnv} (hsel : selIs I (endSelBytes 31)) :
    dispatchMsg contract I.calldata = some cashTransition := by
  have hcd : I.calldata.extract 0 4 = endSelBytes 31 := (byteArray_eq_of_beq hsel).symm
  rw [dispatchMsg_eq_dispatchList contract I.calldata (by rfl) (by rfl)]
  change dispatchList transitions I.calldata = some cashTransition
  unfold transitions
  simp [dispatchList, selectorOf, hcd]
  native_decide

theorem endDispatch_none_short {cd : ByteArray} (h : cd.size < 4) :
    dispatchMsg contract cd = none := by
  rw [dispatchMsg_eq_dispatchList contract cd (by rfl)]
  change dispatchList transitions cd = none
  exact dispatchList_none_short _ (by
    intro t ht
    simp [transitions] at ht
    rcases ht with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals
      simp [selectorOf]
      native_decide) h

theorem endDispatch_none_nomatch {cd : ByteArray}
    (hnm : ∀ i, i < 32 → (endSelBytes i == cd.extract 0 4) = false) :
    dispatchMsg contract cd = none := by
  apply dispatchMsg_none_of_all_ne (hfallback := by rfl)
  intro t ht
  simp [contract, transitions] at ht
  rcases ht with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · rw [selectorOf, wardsSelectorBytes]
    simpa [endSelBytes] using hnm 0 (by omega)
  · rw [selectorOf, vatSelectorBytes]
    simpa [endSelBytes] using hnm 1 (by omega)
  · rw [selectorOf, catSelectorBytes]
    simpa [endSelBytes] using hnm 2 (by omega)
  · rw [selectorOf, dogSelectorBytes]
    simpa [endSelBytes] using hnm 3 (by omega)
  · rw [selectorOf, vowSelectorBytes]
    simpa [endSelBytes] using hnm 4 (by omega)
  · rw [selectorOf, potSelectorBytes]
    simpa [endSelBytes] using hnm 5 (by omega)
  · rw [selectorOf, spotSelectorBytes]
    simpa [endSelBytes] using hnm 6 (by omega)
  · rw [selectorOf, cureSelectorBytes]
    simpa [endSelBytes] using hnm 7 (by omega)
  · rw [selectorOf, liveSelectorBytes]
    simpa [endSelBytes] using hnm 8 (by omega)
  · rw [selectorOf, whenSelectorBytes]
    simpa [endSelBytes] using hnm 9 (by omega)
  · rw [selectorOf, waitSelectorBytes]
    simpa [endSelBytes] using hnm 10 (by omega)
  · rw [selectorOf, debtSelectorBytes]
    simpa [endSelBytes] using hnm 11 (by omega)
  · rw [selectorOf, tagSelectorBytes]
    simpa [endSelBytes] using hnm 12 (by omega)
  · rw [selectorOf, gapSelectorBytes]
    simpa [endSelBytes] using hnm 13 (by omega)
  · rw [selectorOf, ArtSelectorBytes]
    simpa [endSelBytes] using hnm 14 (by omega)
  · rw [selectorOf, fixSelectorBytes]
    simpa [endSelBytes] using hnm 15 (by omega)
  · rw [selectorOf, bagSelectorBytes]
    simpa [endSelBytes] using hnm 16 (by omega)
  · rw [selectorOf, outSelectorBytes]
    simpa [endSelBytes] using hnm 17 (by omega)
  · rw [selectorOf, relySelectorBytes]
    simpa [endSelBytes] using hnm 18 (by omega)
  · rw [selectorOf, denySelectorBytes]
    simpa [endSelBytes] using hnm 19 (by omega)
  · rw [selectorOf, fileAddressSelectorBytes]
    simpa [endSelBytes] using hnm 20 (by omega)
  · rw [selectorOf, fileUintSelectorBytes]
    simpa [endSelBytes] using hnm 21 (by omega)
  · rw [selectorOf, cageSelectorBytes]
    simpa [endSelBytes] using hnm 22 (by omega)
  · rw [selectorOf, cageIlkSelectorBytes]
    simpa [endSelBytes] using hnm 23 (by omega)
  · rw [selectorOf, snipSelectorBytes]
    simpa [endSelBytes] using hnm 24 (by omega)
  · rw [selectorOf, skipSelectorBytes]
    simpa [endSelBytes] using hnm 25 (by omega)
  · rw [selectorOf, skimSelectorBytes]
    simpa [endSelBytes] using hnm 26 (by omega)
  · rw [selectorOf, freeSelectorBytes]
    simpa [endSelBytes] using hnm 27 (by omega)
  · rw [selectorOf, thawSelectorBytes]
    simpa [endSelBytes] using hnm 28 (by omega)
  · rw [selectorOf, flowSelectorBytes]
    simpa [endSelBytes] using hnm 29 (by omega)
  · rw [selectorOf, packSelectorBytes]
    simpa [endSelBytes] using hnm 30 (by omega)
  · rw [selectorOf, cashSelectorBytes]
    simpa [endSelBytes] using hnm 31 (by omega)

theorem endJumpToNoMatchRevert {cA gh bl σ σ₀ A I} {g : Sat256} {pc : UInt256}
    {k C : ℕ}
    (h : RD endBytecode I g (initState cA gh bl σ σ₀ g A I) pc
      [endSelWord I] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C)
    (hpush : decode endBytecode pc = some (.Push .PUSH2, some (endDispatchRevertPc, 2)))
    (hjump : decode endBytecode (pc + UInt256.ofNat 3) = some (.JUMP, .none)) :
    RDrev endBytecode g (initState cA gh bl σ σ₀ g A I) := by
  have h496 := h.push2 endDispatchRevertPc hpush
    (by simp only [List.length_singleton]; omega)
    |>.jump hjump (by jump_dest) (by simp only [List.length_singleton]; omega)
    |>.jumpdest (by native_decide) (by simp only [List.length_singleton]; omega)
  exact RD.uniswapPush1Dup1Revert0 h496 (by native_decide) (by native_decide)
    (by native_decide) (by simp only [List.length_singleton]; omega)

theorem endBodyReverts_nonPayable (t : TransitionDecl) (ht : t ∈ contract.transitions)
    (evm : EVM.State) (locals : Store) (h : evm.executionEnv.weiValue ≠ ⟨0⟩) :
    ExecTransitionBody config contract evm locals t.body .reverted := by
  simp [contract, transitions] at ht
  rcases ht with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    exact bodyReverts_nonPayable h

theorem endX_callvalue_ne {cA gh bl σ σ₀ A I} {g : Sat256}
    (hcode : I.code = endBytecode) (hwv : I.weiValue ≠ ⟨0⟩) :
    RDrev endBytecode g (initState cA gh bl σ σ₀ g A I) := by
  have h0 := solcGuardPrologueRD (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀)
    (A := A) (g := g) hcode (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide)
  have h12 := h0.push2 ⟨16⟩ (by native_decide) (by simp only [List.length]; omega)
    |>.jumpiNT (by native_decide) (isZero_eq_zero_of_ne hwv)
      (by simp only [List.length]; omega)
  exact RD.uniswapPush1Dup1Revert0 h12 (by native_decide) (by native_decide)
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
  exact RD.uniswapPush1Dup1Revert0 h496 (by native_decide) (by native_decide)
    (by native_decide) (by simp only [List.length]; omega)

set_option maxHeartbeats 2000000 in
theorem endX_noMatch {cA gh bl σ σ₀ A I} {g : Sat256}
    (hcode : I.code = endBytecode) (hwv : I.weiValue = ⟨0⟩)
    (hsz : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hnm : ∀ i, i < 32 → (endSelBytes i == I.calldata.extract 0 4) = false) :
    RDrev endBytecode g (initState cA gh bl σ σ₀ g A I) := by
  have hselectorNoMatch (i : ℕ) (hi : i < 32) (c0 c1 c2 c3 : UInt8) (sel : UInt256)
      (hsel : (fromBytesBigEndian [c0, c1, c2, c3] : ℕ) = sel.toNat)
      (hbytes : endSelBytes i = (⟨#[c0, c1, c2, c3]⟩ : ByteArray)) :
      UInt256.eq sel (endSelWord I) = ⟨0⟩ := by
    dsimp [endSelWord]
    rw [evmSelectorDecode hsz c0 c1 c2 c3 sel hsel]
    have hno := hnm i hi
    rw [hbytes] at hno
    simp [hno]
  have hsplit32 : selectorSplitWellFormed endBytecode (⟨32⟩ : UInt256) := by
    dsimp [selectorSplitWellFormed]
    repeat' first | apply And.intro | native_decide
  have hsplit43 : selectorSplitWellFormed endBytecode (⟨43⟩ : UInt256) := by
    dsimp [selectorSplitWellFormed]
    repeat' first | apply And.intro | native_decide
  have hsplit54 : selectorSplitWellFormed endBytecode (⟨54⟩ : UInt256) := by
    dsimp [selectorSplitWellFormed]
    repeat' first | apply And.intro | native_decide
  have hsplit163 : selectorSplitWellFormed endBytecode (⟨163⟩ : UInt256) := by
    dsimp [selectorSplitWellFormed]
    repeat' first | apply And.intro | native_decide
  have hsplit272 : selectorSplitWellFormed endBytecode (⟨272⟩ : UInt256) := by
    dsimp [selectorSplitWellFormed]
    repeat' first | apply And.intro | native_decide
  have hsplit283 : selectorSplitWellFormed endBytecode (⟨283⟩ : UInt256) := by
    dsimp [selectorSplitWellFormed]
    repeat' first | apply And.intro | native_decide
  have hsplit392 : selectorSplitWellFormed endBytecode (⟨392⟩ : UInt256) := by
    dsimp [selectorSplitWellFormed]
    repeat' first | apply And.intro | native_decide
  obtain ⟨k32, C32, h32⟩ :=
    solcLegacyDispatchReachSelector (cA := cA) (gh := gh) (bl := bl) (σ := σ)
      (σ₀ := σ₀) (A := A) (g := g) (code := endBytecode)
      (bodyPc := (⟨18⟩ : UInt256)) (loadPc := (⟨26⟩ : UInt256))
      (firstPc := (⟨32⟩ : UInt256)) (guardTgt := (⟨16⟩ : UInt256))
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
  let finish496 {k C : ℕ}
      (h : RD endBytecode I g (initState cA gh bl σ σ₀ g A I) (⟨496⟩ : UInt256)
        [endSelWord I] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
      RDrev endBytecode g (initState cA gh bl σ σ₀ g A I) := by
    have h497 := h.jumpdest (by native_decide) (by simp only [List.length_singleton]; omega)
    exact RD.uniswapPush1Dup1Revert0 h497 (by native_decide) (by native_decide)
      (by native_decide) (by simp only [List.length_singleton]; omega)
  let finish65 {k C : ℕ}
      (h : RD endBytecode I g (initState cA gh bl σ σ₀ g A I) (⟨65⟩ : UInt256)
        [endSelWord I] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
      RDrev endBytecode g (initState cA gh bl σ σ₀ g A I) := by
    have h109 := h
      |>.selectorArmNotTakenAuto (by dsimp [armWellFormed]; repeat' first | apply And.intro | native_decide)
          (hselectorNoMatch 2 (by omega) 0xe4 0x88 0x18 0x13 _ (by native_decide) rfl) (by simp)
      |>.selectorArmNotTakenAuto (by dsimp [armWellFormed]; repeat' first | apply And.intro | native_decide)
          (hselectorNoMatch 13 (by omega) 0xe6 0xee 0x62 0xaa _ (by native_decide) rfl) (by simp)
      |>.selectorArmNotTakenAuto (by dsimp [armWellFormed]; repeat' first | apply And.intro | native_decide)
          (hselectorNoMatch 12 (by omega) 0xee 0x64 0x47 0xb5 _ (by native_decide) rfl) (by simp)
      |>.selectorArmNotTakenAuto (by dsimp [armWellFormed]; repeat' first | apply And.intro | native_decide)
          (hselectorNoMatch 31 (by omega) 0xfe 0x85 0x07 0xc6 _ (by native_decide) rfl) (by simp)
    exact endJumpToNoMatchRevert h109 (by native_decide) (by native_decide)
  let finish114 {k C : ℕ}
      (h : RD endBytecode I g (initState cA gh bl σ σ₀ g A I) (⟨114⟩ : UInt256)
        [endSelWord I] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
      RDrev endBytecode g (initState cA gh bl σ σ₀ g A I) := by
    have h158 := h
      |>.selectorArmNotTakenAuto (by dsimp [armWellFormed]; repeat' first | apply And.intro | native_decide)
          (hselectorNoMatch 20 (by omega) 0xd4 0xe8 0xbe 0x83 _ (by native_decide) rfl) (by simp)
      |>.selectorArmNotTakenAuto (by dsimp [armWellFormed]; repeat' first | apply And.intro | native_decide)
          (hselectorNoMatch 14 (by omega) 0xe1 0x34 0x0a 0x3d _ (by native_decide) rfl) (by simp)
      |>.selectorArmNotTakenAuto (by dsimp [armWellFormed]; repeat' first | apply And.intro | native_decide)
          (hselectorNoMatch 23 (by omega) 0xe2 0x70 0x2f 0xdc _ (by native_decide) rfl) (by simp)
      |>.selectorArmNotTakenAuto (by dsimp [armWellFormed]; repeat' first | apply And.intro | native_decide)
          (hselectorNoMatch 9 (by omega) 0xe2 0xb0 0xca 0xef _ (by native_decide) rfl) (by simp)
    exact endJumpToNoMatchRevert h158 (by native_decide) (by native_decide)
  let finish174 {k C : ℕ}
      (h : RD endBytecode I g (initState cA gh bl σ σ₀ g A I) (⟨174⟩ : UInt256)
        [endSelWord I] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
      RDrev endBytecode g (initState cA gh bl σ σ₀ g A I) := by
    have h218 := h
      |>.selectorArmNotTakenAuto (by dsimp [armWellFormed]; repeat' first | apply And.intro | native_decide)
          (hselectorNoMatch 0 (by omega) 0xbf 0x35 0x3d 0xbb _ (by native_decide) rfl) (by simp)
      |>.selectorArmNotTakenAuto (by dsimp [armWellFormed]; repeat' first | apply And.intro | native_decide)
          (hselectorNoMatch 3 (by omega) 0xc3 0xb3 0xad 0x7f _ (by native_decide) rfl) (by simp)
      |>.selectorArmNotTakenAuto (by dsimp [armWellFormed]; repeat' first | apply And.intro | native_decide)
          (hselectorNoMatch 27 (by omega) 0xc8 0x30 0x62 0xc6 _ (by native_decide) rfl) (by simp)
      |>.selectorArmNotTakenAuto (by dsimp [armWellFormed]; repeat' first | apply And.intro | native_decide)
          (hselectorNoMatch 17 (by omega) 0xc9 0x39 0xeb 0xfc _ (by native_decide) rfl) (by simp)
    exact endJumpToNoMatchRevert h218 (by native_decide) (by native_decide)
  let finish223 {k C : ℕ}
      (h : RD endBytecode I g (initState cA gh bl σ σ₀ g A I) (⟨223⟩ : UInt256)
        [endSelWord I] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
      RDrev endBytecode g (initState cA gh bl σ σ₀ g A I) := by
    have h267 := h
      |>.selectorArmNotTakenAuto (by dsimp [armWellFormed]; repeat' first | apply And.intro | native_decide)
          (hselectorNoMatch 26 (by omega) 0x89 0xea 0x45 0xd3 _ (by native_decide) rfl) (by simp)
      |>.selectorArmNotTakenAuto (by dsimp [armWellFormed]; repeat' first | apply And.intro | native_decide)
          (hselectorNoMatch 16 (by omega) 0x92 0x55 0xf8 0x09 _ (by native_decide) rfl) (by simp)
      |>.selectorArmNotTakenAuto (by dsimp [armWellFormed]; repeat' first | apply And.intro | native_decide)
          (hselectorNoMatch 8 (by omega) 0x95 0x7a 0xa5 0x8c _ (by native_decide) rfl) (by simp)
      |>.selectorArmNotTakenAuto (by dsimp [armWellFormed]; repeat' first | apply And.intro | native_decide)
          (hselectorNoMatch 19 (by omega) 0x9c 0x52 0xa7 0xf1 _ (by native_decide) rfl) (by simp)
    exact endJumpToNoMatchRevert h267 (by native_decide) (by native_decide)
  let finish294 {k C : ℕ}
      (h : RD endBytecode I g (initState cA gh bl σ σ₀ g A I) (⟨294⟩ : UInt256)
        [endSelWord I] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
      RDrev endBytecode g (initState cA gh bl σ σ₀ g A I) := by
    have h338 := h
      |>.selectorArmNotTakenAuto (by dsimp [armWellFormed]; repeat' first | apply And.intro | native_decide)
          (hselectorNoMatch 22 (by omega) 0x69 0x24 0x50 0x09 _ (by native_decide) rfl) (by simp)
      |>.selectorArmNotTakenAuto (by dsimp [armWellFormed]; repeat' first | apply And.intro | native_decide)
          (hselectorNoMatch 30 (by omega) 0x6e 0xa4 0x25 0x55 _ (by native_decide) rfl) (by simp)
      |>.selectorArmNotTakenAuto (by dsimp [armWellFormed]; repeat' first | apply And.intro | native_decide)
          (hselectorNoMatch 6 (by omega) 0x6f 0x26 0x5b 0x93 _ (by native_decide) rfl) (by simp)
      |>.selectorArmNotTakenAuto (by dsimp [armWellFormed]; repeat' first | apply And.intro | native_decide)
          (hselectorNoMatch 7 (by omega) 0x84 0x07 0x82 0xed _ (by native_decide) rfl) (by simp)
    exact endJumpToNoMatchRevert h338 (by native_decide) (by native_decide)
  let finish343 {k C : ℕ}
      (h : RD endBytecode I g (initState cA gh bl σ σ₀ g A I) (⟨343⟩ : UInt256)
        [endSelWord I] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
      RDrev endBytecode g (initState cA gh bl σ σ₀ g A I) := by
    have h387 := h
      |>.selectorArmNotTakenAuto (by dsimp [armWellFormed]; repeat' first | apply And.intro | native_decide)
          (hselectorNoMatch 4 (by omega) 0x62 0x6c 0xb3 0xc5 _ (by native_decide) rfl) (by simp)
      |>.selectorArmNotTakenAuto (by dsimp [armWellFormed]; repeat' first | apply And.intro | native_decide)
          (hselectorNoMatch 15 (by omega) 0x63 0xfa 0xd8 0x5e _ (by native_decide) rfl) (by simp)
      |>.selectorArmNotTakenAuto (by dsimp [armWellFormed]; repeat' first | apply And.intro | native_decide)
          (hselectorNoMatch 10 (by omega) 0x64 0xbd 0x70 0x13 _ (by native_decide) rfl) (by simp)
      |>.selectorArmNotTakenAuto (by dsimp [armWellFormed]; repeat' first | apply And.intro | native_decide)
          (hselectorNoMatch 18 (by omega) 0x65 0xfa 0xe3 0x5e _ (by native_decide) rfl) (by simp)
    exact endJumpToNoMatchRevert h387 (by native_decide) (by native_decide)
  let finish403 {k C : ℕ}
      (h : RD endBytecode I g (initState cA gh bl σ σ₀ g A I) (⟨403⟩ : UInt256)
        [endSelWord I] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
      RDrev endBytecode g (initState cA gh bl σ σ₀ g A I) := by
    have h447 := h
      |>.selectorArmNotTakenAuto (by dsimp [armWellFormed]; repeat' first | apply And.intro | native_decide)
          (hselectorNoMatch 29 (by omega) 0x4a 0x10 0xea 0xa6 _ (by native_decide) rfl) (by simp)
      |>.selectorArmNotTakenAuto (by dsimp [armWellFormed]; repeat' first | apply And.intro | native_decide)
          (hselectorNoMatch 5 (by omega) 0x4b 0xa2 0x36 0x3a _ (by native_decide) rfl) (by simp)
      |>.selectorArmNotTakenAuto (by dsimp [armWellFormed]; repeat' first | apply And.intro | native_decide)
          (hselectorNoMatch 25 (by omega) 0x50 0x3e 0xcf 0x06 _ (by native_decide) rfl) (by simp)
      |>.selectorArmNotTakenAuto (by dsimp [armWellFormed]; repeat' first | apply And.intro | native_decide)
          (hselectorNoMatch 28 (by omega) 0x59 0x20 0x37 0x5c _ (by native_decide) rfl) (by simp)
    exact endJumpToNoMatchRevert h447 (by native_decide) (by native_decide)
  let finish452 {k C : ℕ}
      (h : RD endBytecode I g (initState cA gh bl σ σ₀ g A I) (⟨452⟩ : UInt256)
        [endSelWord I] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
      RDrev endBytecode g (initState cA gh bl σ σ₀ g A I) := by
    have h496 := h
      |>.selectorArmNotTakenAuto (by dsimp [armWellFormed]; repeat' first | apply And.intro | native_decide)
          (hselectorNoMatch 11 (by omega) 0x0d 0xca 0x59 0xc1 _ (by native_decide) rfl) (by simp)
      |>.selectorArmNotTakenAuto (by dsimp [armWellFormed]; repeat' first | apply And.intro | native_decide)
          (hselectorNoMatch 21 (by omega) 0x29 0xae 0x81 0x14 _ (by native_decide) rfl) (by simp)
      |>.selectorArmNotTakenAuto (by dsimp [armWellFormed]; repeat' first | apply And.intro | native_decide)
          (hselectorNoMatch 1 (by omega) 0x36 0x56 0x9e 0x77 _ (by native_decide) rfl) (by simp)
      |>.selectorArmNotTakenAuto (by dsimp [armWellFormed]; repeat' first | apply And.intro | native_decide)
          (hselectorNoMatch 24 (by omega) 0x38 0xc6 0xde 0x40 _ (by native_decide) rfl) (by simp)
    exact finish496 h496
  by_cases hroot :
      UInt256.gt (armSelNat endBytecode (⟨32⟩ : UInt256)) (endSelWord I) = ⟨0⟩
  · have h43 := RD.selectorSplitNotTakenAuto h32 hsplit32 hroot (by simp)
    by_cases h43gt :
        UInt256.gt (armSelNat endBytecode (⟨43⟩ : UInt256)) (endSelWord I) = ⟨0⟩
    · have h54 := RD.selectorSplitNotTakenAuto h43 hsplit43 h43gt (by simp)
      by_cases h54gt :
          UInt256.gt (armSelNat endBytecode (⟨54⟩ : UInt256)) (endSelWord I) = ⟨0⟩
      · have h65 : RD endBytecode I g (initState cA gh bl σ σ₀ g A I) (⟨65⟩ : UInt256)
            [endSelWord I] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty
            (cA, σ) (k32 + 5 + 5 + 5) (C32 + 22 + 22 + 22) := by
          simpa [selArmNextPc, armTgtWidth, selArmJumpiPc, selArmPushTgtPc,
            selArmEqPc, selArmPush4Pc] using
            RD.selectorSplitNotTakenAuto h54 hsplit54 h54gt (by simp)
        exact finish65 h65
      · have h113 := RD.selectorSplitTakenAuto h54 hsplit54 h54gt (by jump_dest) (by simp)
        have h114 := h113.jumpdest (by native_decide) (by simp only [List.length_singleton]; omega)
        exact finish114 h114
    · have h162 := RD.selectorSplitTakenAuto h43 hsplit43 h43gt (by jump_dest) (by simp)
      have h163 := h162.jumpdest (by native_decide) (by simp only [List.length_singleton]; omega)
      by_cases h163gt :
          UInt256.gt (armSelNat endBytecode (⟨163⟩ : UInt256)) (endSelWord I) = ⟨0⟩
      · have h174 : RD endBytecode I g (initState cA gh bl σ σ₀ g A I) (⟨174⟩ : UInt256)
            [endSelWord I] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty
            (cA, σ) _ _ := by
          simpa [selArmNextPc, armTgtWidth, selArmJumpiPc, selArmPushTgtPc,
            selArmEqPc, selArmPush4Pc] using
            RD.selectorSplitNotTakenAuto h163 hsplit163 h163gt (by simp)
        exact finish174 h174
      · have h222 := RD.selectorSplitTakenAuto h163 hsplit163 h163gt (by jump_dest) (by simp)
        have h223 := h222.jumpdest (by native_decide) (by simp only [List.length_singleton]; omega)
        exact finish223 h223
  · have h271 := RD.selectorSplitTakenAuto h32 hsplit32 hroot (by jump_dest) (by simp)
    have h272 := h271.jumpdest (by native_decide) (by simp only [List.length_singleton]; omega)
    by_cases h272gt :
        UInt256.gt (armSelNat endBytecode (⟨272⟩ : UInt256)) (endSelWord I) = ⟨0⟩
    · have h283 : RD endBytecode I g (initState cA gh bl σ σ₀ g A I) (⟨283⟩ : UInt256)
          [endSelWord I] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) _ _ := by
        simpa [selArmNextPc, armTgtWidth, selArmJumpiPc, selArmPushTgtPc,
          selArmEqPc, selArmPush4Pc] using
          RD.selectorSplitNotTakenAuto h272 hsplit272 h272gt (by simp)
      by_cases h283gt :
          UInt256.gt (armSelNat endBytecode (⟨283⟩ : UInt256)) (endSelWord I) = ⟨0⟩
      · have h294 : RD endBytecode I g (initState cA gh bl σ σ₀ g A I) (⟨294⟩ : UInt256)
            [endSelWord I] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty
            (cA, σ) _ _ := by
          simpa [selArmNextPc, armTgtWidth, selArmJumpiPc, selArmPushTgtPc,
            selArmEqPc, selArmPush4Pc] using
            RD.selectorSplitNotTakenAuto h283 hsplit283 h283gt (by simp)
        exact finish294 h294
      · have h342 := RD.selectorSplitTakenAuto h283 hsplit283 h283gt (by jump_dest) (by simp)
        have h343 := h342.jumpdest (by native_decide) (by simp only [List.length_singleton]; omega)
        exact finish343 h343
    · have h391 := RD.selectorSplitTakenAuto h272 hsplit272 h272gt (by jump_dest) (by simp)
      have h392 := h391.jumpdest (by native_decide) (by simp only [List.length_singleton]; omega)
      by_cases h392gt :
          UInt256.gt (armSelNat endBytecode (⟨392⟩ : UInt256)) (endSelWord I) = ⟨0⟩
      · have h403 : RD endBytecode I g (initState cA gh bl σ σ₀ g A I) (⟨403⟩ : UInt256)
            [endSelWord I] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty
            (cA, σ) _ _ := by
          simpa [selArmNextPc, armTgtWidth, selArmJumpiPc, selArmPushTgtPc,
            selArmEqPc, selArmPush4Pc] using
            RD.selectorSplitNotTakenAuto h392 hsplit392 h392gt (by simp)
        exact finish403 h403
      · have h451 := RD.selectorSplitTakenAuto h392 hsplit392 h392gt (by jump_dest) (by simp)
        have h452 := h451.jumpdest (by native_decide) (by simp only [List.length_singleton]; omega)
        exact finish452 h452

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
              (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)
              callargs (by simp only [initState]; exact hwv))
            (by rw [hrev]; exact execResultsEquiv.revert rfl rfl)

theorem endNoDispatch {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256}
    (hcode : I.code = endBytecode) (hsize : I.calldata.size < UInt256.size)
    (_hperm : I.perm = true) (hwv : I.weiValue = ⟨0⟩)
    (hnm : ∀ i, i < 32 → (endSelBytes i == I.calldata.extract 0 4) = false)
    (_hAccounts : accountMapEquiv σ_evm σ_solm) :
    runtimeEquivalenceFor config contract cA gh bl σ_evm σ_solm σ₀ g A I := by
  by_cases hsz : 4 ≤ I.calldata.size
  · exact (endX_noMatch (g := Sat256.ofUInt256 g) hcode hwv hsz hsize hnm)
      |>.reEquivNoDispatch hcode (endDispatch_none_nomatch hnm)
  · have hshort : I.calldata.size < 4 := by omega
    exact (endX_short (g := Sat256.ofUInt256 g) hcode hwv hshort)
      |>.reEquivNoDispatch hcode (endDispatch_none_short hshort)

theorem endNoSelectorMatches {I : ExecutionEnv}
    (hwards : ¬ selIs I (endSelBytes 0))
    (hvat : ¬ selIs I (endSelBytes 1))
    (hcat : ¬ selIs I (endSelBytes 2))
    (hdog : ¬ selIs I (endSelBytes 3))
    (hvow : ¬ selIs I (endSelBytes 4))
    (hpot : ¬ selIs I (endSelBytes 5))
    (hspot : ¬ selIs I (endSelBytes 6))
    (hcure : ¬ selIs I (endSelBytes 7))
    (hlive : ¬ selIs I (endSelBytes 8))
    (hwhen : ¬ selIs I (endSelBytes 9))
    (hwait : ¬ selIs I (endSelBytes 10))
    (hdebt : ¬ selIs I (endSelBytes 11))
    (htag : ¬ selIs I (endSelBytes 12))
    (hgap : ¬ selIs I (endSelBytes 13))
    (hArt : ¬ selIs I (endSelBytes 14))
    (hfix : ¬ selIs I (endSelBytes 15))
    (hbag : ¬ selIs I (endSelBytes 16))
    (hout : ¬ selIs I (endSelBytes 17))
    (hrely : ¬ selIs I (endSelBytes 18))
    (hdeny : ¬ selIs I (endSelBytes 19))
    (hfileAddress : ¬ selIs I (endSelBytes 20))
    (hfileUint : ¬ selIs I (endSelBytes 21))
    (hcage : ¬ selIs I (endSelBytes 22))
    (hcageIlk : ¬ selIs I (endSelBytes 23))
    (hsnip : ¬ selIs I (endSelBytes 24))
    (hskip : ¬ selIs I (endSelBytes 25))
    (hskim : ¬ selIs I (endSelBytes 26))
    (hfree : ¬ selIs I (endSelBytes 27))
    (hthaw : ¬ selIs I (endSelBytes 28))
    (hflow : ¬ selIs I (endSelBytes 29))
    (hpack : ¬ selIs I (endSelBytes 30))
    (hcash : ¬ selIs I (endSelBytes 31)) :
    ∀ i, i < 32 → (endSelBytes i == I.calldata.extract 0 4) = false := by
  intro i hi
  interval_cases i
  · simpa [selIs, endSelBytes] using hwards
  · simpa [selIs, endSelBytes] using hvat
  · simpa [selIs, endSelBytes] using hcat
  · simpa [selIs, endSelBytes] using hdog
  · simpa [selIs, endSelBytes] using hvow
  · simpa [selIs, endSelBytes] using hpot
  · simpa [selIs, endSelBytes] using hspot
  · simpa [selIs, endSelBytes] using hcure
  · simpa [selIs, endSelBytes] using hlive
  · simpa [selIs, endSelBytes] using hwhen
  · simpa [selIs, endSelBytes] using hwait
  · simpa [selIs, endSelBytes] using hdebt
  · simpa [selIs, endSelBytes] using htag
  · simpa [selIs, endSelBytes] using hgap
  · simpa [selIs, endSelBytes] using hArt
  · simpa [selIs, endSelBytes] using hfix
  · simpa [selIs, endSelBytes] using hbag
  · simpa [selIs, endSelBytes] using hout
  · simpa [selIs, endSelBytes] using hrely
  · simpa [selIs, endSelBytes] using hdeny
  · simpa [selIs, endSelBytes] using hfileAddress
  · simpa [selIs, endSelBytes] using hfileUint
  · simpa [selIs, endSelBytes] using hcage
  · simpa [selIs, endSelBytes] using hcageIlk
  · simpa [selIs, endSelBytes] using hsnip
  · simpa [selIs, endSelBytes] using hskip
  · simpa [selIs, endSelBytes] using hskim
  · simpa [selIs, endSelBytes] using hfree
  · simpa [selIs, endSelBytes] using hthaw
  · simpa [selIs, endSelBytes] using hflow
  · simpa [selIs, endSelBytes] using hpack
  · simpa [selIs, endSelBytes] using hcash

end Benchmarks.Dss.End
