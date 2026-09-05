import Benchmarks.Dss.Clipper.KickPostFeed

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Benchmarks.Dss.Clipper.Immutables

namespace Benchmarks.Dss.Clipper

set_option maxHeartbeats 2000000
set_option maxRecDepth 10000
set_option linter.unusedTactic false

/-! At depth 1024 the first `getFeedPrice` static call is not made.  Both the
compiler trace and the source interpreter therefore take their call-failure
branches without invoking the external transition relation. -/

theorem RD.clipperKickGetFeedPriceSpotterIlksDepthLimit {code : ByteArray}
    (v : ClipperImmutables)
    (hpatch : patchRuntime clipperBytecode (patches v) = some code)
    {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap}
    {id sel : UInt256} {R : List UInt256}
    {mem rdata : ByteArray} {k C : ℕ}
    (hrd : RD code ee g s0 ⟨8728⟩
      (⟨6061⟩ :: ⟨6069⟩ :: ⟨0⟩ :: ⟨1⟩ :: id ::
        clipperKickKprMaskedWord ee :: clipperKickUsrMaskedWord ee ::
        clipperKickLotWord ee :: clipperKickTabWord ee :: ⟨476⟩ :: sel :: R)
      mem (UInt256.ofNat 3) rdata (cA, σ) k C)
    (hcode : extCodeSizeWord σ (clipperSpotterTarget σ ee) ≠ ⟨0⟩)
    (hdepth : ee.depth = 1024)
    (hmem : mem.size = 96)
    (hread64 : mem.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩)
    (hov : R.length + 100 ≤ 1024) :
    ∃ k' C', RD code ee g s0 ⟨8840⟩
      (⟨0⟩ :: ⟨164⟩ :: clipperSpotterIlksSelectorWord ::
        clipperSpotterTarget σ ee :: ⟨0⟩ :: ⟨0⟩ :: ⟨6061⟩ :: ⟨6069⟩ ::
        ⟨0⟩ :: ⟨1⟩ :: id :: clipperKickKprMaskedWord ee ::
        clipperKickUsrMaskedWord ee :: clipperKickLotWord ee ::
        clipperKickTabWord ee :: ⟨476⟩ :: sel :: R)
      (clipperSpotterIlksPostCallMem v mem ByteArray.empty)
      (UInt256.ofNat 6) ByteArray.empty (cA, σ) k' C' := by
  obtain ⟨_, _, rd8824⟩ :=
    RD.clipperKickGetFeedPriceToSpotterIlksExtcodesizeGuard
      v hpatch hrd hmem hread64 (by simp only [List.length_cons]; omega)
  obtain ⟨gasWord, _, _, rd8839⟩ :=
    RD.solcExtcodesizeGuardOkGas (pc := ⟨8824⟩) (okPc := ⟨8836⟩)
      rd8824 hcode
      (by clipper_runtime_decode) (by clipper_runtime_decode)
      (by clipper_runtime_decode) (by clipper_runtime_decode)
      (by clipper_runtime_decode) (by clipper_runtime_decode)
      (clipperGetFeedPriceJumpDest8836 v hpatch)
      (by clipper_runtime_decode) (by clipper_runtime_decode)
      (by clipper_runtime_decode)
      (by simp only [List.length_cons]; omega)
  obtain ⟨k8840, C8840, rd8840⟩ :=
    RD.callDepthLimit rd8839 (by clipper_runtime_decode) hdepth
      (by simp only [List.length_cons]; omega)
  refine ⟨k8840, C8840, ?_⟩
  have hmin :
      (min (⟨64⟩ : UInt256) (UInt256.ofNat ByteArray.empty.size)).toNat = 0 := by
    decide
  have haw :
      UInt256.ofNat
        (MachineState.M (MachineState.M (UInt256.ofNat 6).toNat 128 36)
          128 64) = UInt256.ofNat 6 := by
    native_decide
  simpa [clipperSpotterIlksPostCallMem, hmin, byteArray_write_len_zero, haw]
    using rd8840

theorem clipperKickDepthLimitReverts
    (v : ClipperImmutables) {code : ByteArray}
    (hpatch : patchRuntime clipperBytecode (patches v) = some code)
    {cA0 : Batteries.RBSet AccountAddress compare} {gh : BlockHeader}
    {bl : ProcessedBlocks} {σStart σ₀ : AccountMap} {A : Substate}
    {g : UInt256} {I : ExecutionEnv} {evmLock sourceInit : EVM.State}
    {id sel : UInt256} {R : List UInt256}
    {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap}
    {mem rdata : ByteArray} {k C : ℕ}
    (hdepth : I.depth = 1024)
    (hspotter : extCodeSizeWord σ (clipperSpotterTarget σ I) ≠ ⟨0⟩)
    (halign : ClipperKickCallAligned
      (initState cA0 gh bl σStart σ₀ (Sat256.ofUInt256 g) A I)
      cA σ I sourceInit)
    (hrd : RD code I (Sat256.ofUInt256 g)
      (initState cA0 gh bl σStart σ₀ (Sat256.ofUInt256 g) A I) ⟨8728⟩
      (⟨6061⟩ :: ⟨6069⟩ :: ⟨0⟩ :: ⟨1⟩ :: id ::
        clipperKickKprMaskedWord I :: clipperKickUsrMaskedWord I ::
        clipperKickLotWord I :: clipperKickTabWord I :: ⟨476⟩ :: sel :: R)
      mem (UInt256.ofNat 3) rdata (cA, σ) k C)
    (hmem : mem.size = 96)
    (hread64 : mem.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩)
    (hov : R.length + 101 ≤ 1024) :
    ClipperKickTailOutcome v code g
      (initState cA0 gh bl σStart σ₀ (Sat256.ofUInt256 g) A I) I
      evmLock sourceInit id := by
  obtain ⟨k8840, C8840, rd8840⟩ :=
    RD.clipperKickGetFeedPriceSpotterIlksDepthLimit
      v hpatch hrd hspotter hdepth hmem hread64 (by omega)
  have hevm := RD.clipperGetFeedPriceSpotterIlksCallFailure
    v hpatch rd8840 (by decide) (by simp only [List.length_cons]; omega)
  have haddr := clipperKickSpotterAddress_eq_of_aligned halign
  have hcode := clipperKickHasCode_of_aligned halign haddr hspotter
  have hdepthSource : sourceInit.executionEnv.depth = 1024 := by
    rw [halign.executionEnv]
    exact hdepth
  let sourceAfter : EVM.State :=
    { sourceInit with
      substate := (sourceInit.addAccessedAccount
        (EVM.address (clipperGetFeedPriceSpotterAddress sourceInit))).substate }
  have hcalldata := clipperKickSpotterIlksEncode_eq v hmem
  have hcall : typedCallViaEVM (config v) sourceInit
      (EVM.address (clipperGetFeedPriceSpotterAddress sourceInit))
      "spotterIlks" 0 [v.ilk] (false, sourceAfter, ByteArray.empty) true := by
    simpa [sourceAfter] using
      (callNotMade_depthLimit (cfg := config v) (evm := sourceInit)
        (tgt := EVM.address (clipperGetFeedPriceSpotterAddress sourceInit))
        (name := "spotterIlks") (args := [v.ilk]) (callPerm := true)
        hcalldata hdepthSource)
  have hgetFeed := clipperGetFeedPriceCallRevertsSpotterIlksCallFailure
    v (clipperKickLocalsActivePos evmLock I) "feedPrice" hcode hcall
  exact .reverted
    (clipperKickAfterInitializationGetFeedReverts
      v evmLock sourceInit I hgetFeed)
    hevm

end Benchmarks.Dss.Clipper
