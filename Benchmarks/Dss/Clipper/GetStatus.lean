import Reasoning.ExternalCall
import Benchmarks.Dss.Clipper.GetStatusEVMReverts
import Benchmarks.Dss.Clipper.GetStatusReverts

variable {fork : Ethereum.Fork}

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Benchmarks.Dss.Clipper.Immutables

namespace Benchmarks.Dss.Clipper

attribute [local irreducible] Ethereum.KEC

set_option linter.unusedTactic false

theorem clipperGetStatusSalesBaseSlot_eq (I : ExecutionEnv) :
    clipperGetStatusSalesBaseSlot I = solcMappingSlot ⟨12⟩ (clipperGetStatusArgWord I) := by
  unfold clipperGetStatusSalesBaseSlot salesBase mapSlot solcMappingSlot clipperGetStatusArgKey
  rw [keyValueToWord_uint256]

theorem clipperGetStatusReturnEquiv
    (needsWord : UInt256) (needs : Bool) (price lot tab : UInt256)
    (hneeds : UInt256.isZero (UInt256.isZero needsWord) = needs.toUInt256) :
    returnEquiv (clipperGetStatusReturnBytes needsWord price lot tab)
      (some [.bool needs, .int (Int.ofNat price.toNat), .int (Int.ofNat lot.toNat),
        .int (Int.ofNat tab.toNat)])
      getStatusTransition.returnType := by
  rw [show getStatusTransition.returnType = [.elem .bool, uint256, uint256, uint256] from rfl]
  exact returnEquiv.returned rfl
    (clipperGetStatusReturnEncoding needsWord needs price lot tab hneeds)


theorem clipperDecode_getStatus_ok {I : ExecutionEnv}
    (hsz36 : 36 ≤ I.calldata.size) :
    config.externalABI.decodeCalldata? (getStatusTransition.params.map Param.name)
      (transitionSignature getStatusTransition).paramTypes I.calldata =
        some (clipperGetStatusStore I) := by
  show config.externalABI.decodeCalldata? ["id"] [uint256] I.calldata = _
  simpa [config, clipperGetStatusStore, clipperGetStatusArgValue,
    clipperGetStatusArgWord] using
    decodeCalldata_legacyUInt256_ok (cd := I.calldata) (x := "id") hsz36

theorem clipperDecode_getStatus_none_short {I : ExecutionEnv}
    (hsz4 : 4 ≤ I.calldata.size) (hshort : I.calldata.size < 36) :
    config.externalABI.decodeCalldata? (getStatusTransition.params.map Param.name)
      (transitionSignature getStatusTransition).paramTypes I.calldata = none := by
  show config.externalABI.decodeCalldata? ["id"] [uint256] I.calldata = none
  simpa [config] using
    decodeCalldata_legacyUInt256_none_short (cd := I.calldata) (x := "id")
      hsz4 hshort

theorem clipperGetStatusSelectorWord {I : ExecutionEnv} (hsz : 4 ≤ I.calldata.size)
    (hsel : selIs I (clipperSelBytes 11)) :
    clipperSelWord I = clipperSelNat 11 := by
  simpa [clipperSelWord, solcSelectorWord, clipperSelNat] using
    solcSelectorWord_eq_of_beq I hsz 0x5c 0x62 0x2a 0x0e (clipperSelNat 11)
      (by native_decide) (by simpa [clipperSelBytes, selIs] using hsel)

theorem clipperDispatch_getStatus {I : ExecutionEnv}
    (hsel : selIs I (clipperSelBytes 11)) :
    dispatchMsg contract I.calldata = some getStatusTransition := by
  refine dispatchMsg_eq_some_of_split (contract := contract)
    (pre :=
      [activeTransition, bufTransition, calcTransition, chipTransition, chostTransition,
        countTransition, cuspTransition, denyTransition, dogTransition, fileUintTransition,
        fileAddressTransition])
    (post :=
      [ilkTransition, kickTransition, kicksTransition, listTransition, redoTransition,
        relyTransition, salesTransition, spotterTransition, stoppedTransition, tailTransition,
        takeTransition, tipTransition, upchostTransition, vatTransition, vowTransition,
        wardsTransition, yankTransition])
    (ti := getStatusTransition) (cd := I.calldata) (by rfl) ?_ ?_ ?_ (by rfl)
  · rfl
  · intro t ht
    simp only [List.mem_cons, List.mem_nil_iff] at ht
    rcases ht with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      | hfalse
    · rw [selectorOf, activeSelectorBytes, ← byteArray_eq_of_beq hsel]
      native_decide
    · rw [selectorOf, bufSelectorBytes, ← byteArray_eq_of_beq hsel]
      native_decide
    · rw [selectorOf, calcSelectorBytes, ← byteArray_eq_of_beq hsel]
      native_decide
    · rw [selectorOf, chipSelectorBytes, ← byteArray_eq_of_beq hsel]
      native_decide
    · rw [selectorOf, chostSelectorBytes, ← byteArray_eq_of_beq hsel]
      native_decide
    · rw [selectorOf, countSelectorBytes, ← byteArray_eq_of_beq hsel]
      native_decide
    · rw [selectorOf, cuspSelectorBytes, ← byteArray_eq_of_beq hsel]
      native_decide
    · rw [selectorOf, denySelectorBytes, ← byteArray_eq_of_beq hsel]
      native_decide
    · rw [selectorOf, dogSelectorBytes, ← byteArray_eq_of_beq hsel]
      native_decide
    · rw [selectorOf, fileUintSelectorBytes, ← byteArray_eq_of_beq hsel]
      native_decide
    · rw [selectorOf, fileAddressSelectorBytes, ← byteArray_eq_of_beq hsel]
      native_decide
    · cases hfalse
  · rw [selectorOf, getStatusSelectorBytes]
    simpa [clipperSelBytes] using hsel

set_option maxHeartbeats 1000000 in
theorem clipperReachGetStatusBody {σ σ₀ A I} {g : Sat256}
    (v : ClipperImmutables) {code : ByteArray}
    (hpatch : patchRuntime clipperBytecode (patches v) = some code)
    (hcode : I.code = code) (hwv : I.weiValue = ⟨0⟩)
    (hsz : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hsel : selIs I (clipperSelBytes 11)) :
    ∃ k C, RD fork code I g (initState σ σ₀ g A I) (⟨760⟩ : UInt256)
      [clipperSelWord I] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty σ k C := by
  obtain ⟨_, _, h32⟩ := clipperReachRoot (fork := fork)
    (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := g) v hpatch hcode hwv hsz hsize
  have hword := clipperGetStatusSelectorWord hsz hsel
  have h260 := RD.selectorSplitTakenPush2 (fork := fork) (pc := (⟨32⟩ : UInt256)) (pivot := clipperSelNat 20)
    (tgt := (⟨260⟩ : UInt256)) h32
    (by change decode code (⟨32⟩ : UInt256) = some (.DUP1, .none); clipper_decode)
    (by
      change decode code (selArmPush4Pc (⟨32⟩ : UInt256)) =
        some (.Push .PUSH4, some (clipperSelNat 20, 4))
      clipper_decode)
    (by change decode code (selArmEqPc (⟨32⟩ : UInt256)) = some (.GT, .none); clipper_decode)
    (by decide)
    (by
      change decode code (selArmPushTgtPc (⟨32⟩ : UInt256)) =
        some (.Push .PUSH2, some (⟨260⟩, 2))
      clipper_decode)
    (by
      change decode code (selArmJumpiPc (⟨32⟩ : UInt256) 2) = some (.JUMPI, .none)
      clipper_decode)
    (by rw [hword]; native_decide)
    (clipperJumpDestBeforeFirstPatch v hpatch (⟨260⟩ : UInt256) (by native_decide))
    (by simp)
  have h272 := RD.selectorSplitNotTakenPush2 (fork := fork) (pc := (⟨261⟩ : UInt256))
    (next := (⟨272⟩ : UInt256)) (pivot := clipperSelNat 9)
    (tgt := (⟨369⟩ : UInt256))
    (h260.jumpdest
      (by change decode code (⟨260⟩ : UInt256) = some (.JUMPDEST, .none); clipper_decode)
      (by simp))
    (by change decode code (⟨261⟩ : UInt256) = some (.DUP1, .none); clipper_decode)
    (by
      change decode code (selArmPush4Pc (⟨261⟩ : UInt256)) =
        some (.Push .PUSH4, some (clipperSelNat 9, 4))
      clipper_decode)
    (by change decode code (selArmEqPc (⟨261⟩ : UInt256)) = some (.GT, .none); clipper_decode)
    (by decide)
    (by
      change decode code (selArmPushTgtPc (⟨261⟩ : UInt256)) =
        some (.Push .PUSH2, some (⟨369⟩, 2))
      clipper_decode)
    (by
      change decode code (selArmJumpiPc (⟨261⟩ : UInt256) 2) = some (.JUMPI, .none)
      clipper_decode)
    (by rw [hword]; native_decide)
    (by native_decide)
    (by simp)
  have h283 := RD.selectorSplitNotTakenPush2 (pc := (⟨272⟩ : UInt256))
    (next := (⟨283⟩ : UInt256)) (pivot := clipperSelNat 6)
    (tgt := (⟨331⟩ : UInt256)) h272
    (by change decode code (⟨272⟩ : UInt256) = some (.DUP1, .none); clipper_decode)
    (by
      change decode code (selArmPush4Pc (⟨272⟩ : UInt256)) =
        some (.Push .PUSH4, some (clipperSelNat 6, 4))
      clipper_decode)
    (by change decode code (selArmEqPc (⟨272⟩ : UInt256)) = some (.GT, .none); clipper_decode)
    (by decide)
    (by
      change decode code (selArmPushTgtPc (⟨272⟩ : UInt256)) =
        some (.Push .PUSH2, some (⟨331⟩, 2))
      clipper_decode)
    (by
      change decode code (selArmJumpiPc (⟨272⟩ : UInt256) 2) = some (.JUMPI, .none)
      clipper_decode)
    (by rw [hword]; native_decide)
    (by native_decide)
    (by simp)
  have h294 := RD.selectorArmNotTakenPush2 (pc := (⟨283⟩ : UInt256))
    (next := (⟨294⟩ : UInt256)) (sel := clipperSelNat 6)
    (tgt := (⟨752⟩ : UInt256)) h283
    (by change decode code (⟨283⟩ : UInt256) = some (.DUP1, .none); clipper_decode)
    (by
      change decode code (selArmPush4Pc (⟨283⟩ : UInt256)) =
        some (.Push .PUSH4, some (clipperSelNat 6, 4))
      clipper_decode)
    (by change decode code (selArmEqPc (⟨283⟩ : UInt256)) = some (.EQ, .none); clipper_decode)
    (by decide)
    (by
      change decode code (selArmPushTgtPc (⟨283⟩ : UInt256)) =
        some (.Push .PUSH2, some (⟨752⟩, 2))
      clipper_decode)
    (by
      change decode code (selArmJumpiPc (⟨283⟩ : UInt256) 2) = some (.JUMPI, .none)
      clipper_decode)
    (by rw [hword]; native_decide)
    (by native_decide)
    (by simp)
  have h760 := RD.selectorArmTakenPush2 (pc := (⟨294⟩ : UInt256)) (sel := clipperSelNat 11)
    (tgt := (⟨760⟩ : UInt256)) h294
    (by change decode code (⟨294⟩ : UInt256) = some (.DUP1, .none); clipper_decode)
    (by
      change decode code (selArmPush4Pc (⟨294⟩ : UInt256)) =
        some (.Push .PUSH4, some (clipperSelNat 11, 4))
      clipper_decode)
    (by change decode code (selArmEqPc (⟨294⟩ : UInt256)) = some (.EQ, .none); clipper_decode)
    (by decide)
    (by
      change decode code (selArmPushTgtPc (⟨294⟩ : UInt256)) =
        some (.Push .PUSH2, some (⟨760⟩, 2))
      clipper_decode)
    (by
      change decode code (selArmJumpiPc (⟨294⟩ : UInt256) 2) = some (.JUMPI, .none)
      clipper_decode)
    (by rw [hword]; native_decide)
    (clipperJumpDestBeforeFirstPatch v hpatch (⟨760⟩ : UInt256) (by native_decide))
    (by simp)
  exact ⟨_, _, h760⟩

theorem clipperGetStatusEntryWf (v : ClipperImmutables) {code : ByteArray}
    (hpatch : patchRuntime clipperBytecode (patches v) = some code) :
    solcOneUintExternalEntryWf code (⟨760⟩ : UInt256) (⟨789⟩ : UInt256)
      (⟨3185⟩ : UInt256) := by
  unfold solcOneUintExternalEntryWf solcOneUintExternalDecodedPc
  repeat' first | apply And.intro
  all_goals
    rw [clipperDecodeBeforeFirstPatch v hpatch _ (by native_decide)]
    native_decide

theorem clipperJumpDest3185 (v : ClipperImmutables) {code : ByteArray}
    (hpatch : patchRuntime clipperBytecode (patches v) = some code) :
    (D_J code 0).contains (⟨3185⟩ : UInt256) = true := by
  apply patchRuntime_D_J_contains_of_patchScanReaches (fuel := 4000) hpatch
  unfold patches patchesFrom offsets immValues
  simp only [List.foldrM_cons, List.foldrM_nil, List.lookup_cons]
  cases hIlk : Reasoning.Theory.wordBytes? v.ilk with
  | none =>
      simp [hIlk]
      native_decide
  | some bs =>
      simp [hIlk]
      native_decide

theorem clipperGetStatusX_decoded {σ σ₀ A I} {g : Sat256} {sel : UInt256}
    (v : ClipperImmutables) {code : ByteArray}
    (hpatch : patchRuntime clipperBytecode (patches v) = some code)
    (hsz36 : 36 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hreach : ∃ k C, RD fork code I g
      (initState σ σ₀ g A I) (⟨760⟩ : UInt256) [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty σ k C) :
    ∃ k C, RD fork code I g (initState σ σ₀ g A I) (⟨3185⟩ : UInt256)
      (clipperGetStatusArgWord I :: ⟨789⟩ :: [sel])
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty σ k C := by
  obtain ⟨_, _, hdecoded⟩ := solcOneUintExternalLenOk
    (entry := (⟨760⟩ : UInt256)) (ret := (⟨789⟩ : UInt256))
    (routine := (⟨3185⟩ : UInt256)) hreach (clipperGetStatusEntryWf v hpatch)
    (by
      simpa [solcOneUintExternalDecodedPc] using
        clipperJumpDestBeforeFirstPatch v hpatch (⟨782⟩ : UInt256) (by native_decide))
    hsz36 hsize
  exact solcOneUintExternalLoadAndJump
    (entry := (⟨760⟩ : UInt256)) (ret := (⟨789⟩ : UInt256))
    (routine := (⟨3185⟩ : UInt256)) hdecoded (clipperGetStatusEntryWf v hpatch)
    (clipperJumpDest3185 v hpatch) (by simp)

theorem clipperGetStatusX_shortarg {σ σ₀ A I} {g : Sat256} {sel : UInt256}
    (v : ClipperImmutables) {code : ByteArray}
    (hpatch : patchRuntime clipperBytecode (patches v) = some code)
    (hsz4 : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hshort : I.calldata.size < 36)
    (hreach : ∃ k C, RD fork code I g
      (initState σ σ₀ g A I) (⟨760⟩ : UInt256) [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty σ k C) :
    RDrev fork code g (initState σ σ₀ g A I) := by
  exact solcOneUintExternalShort (entry := (⟨760⟩ : UInt256))
    (ret := (⟨789⟩ : UInt256)) (routine := (⟨3185⟩ : UInt256)) hreach
    (clipperGetStatusEntryWf v hpatch) hsz4 hsize hshort

theorem clipperGetStatusBodyCoreDecodeFailed_short
    {σ σ₀ A I} {g : UInt256} {sel : UInt256}
    (v : ClipperImmutables) {code : ByteArray}
    (hpatch : patchRuntime clipperBytecode (patches v) = some code)
    (hcode : I.code = code) (hsize : I.calldata.size < UInt256.size)
    (hsz4 : 4 ≤ I.calldata.size) (hshort : I.calldata.size < 36)
    (hdispatch : dispatchMsg contract I.calldata = some getStatusTransition)
    (hreach : ∃ k C, RD fork code I (Sat256.ofUInt256 g)
      (initState σ σ₀ (Sat256.ofUInt256 g) A I) (⟨760⟩ : UInt256)
      [sel] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty σ k C) :
    runtimeRefinementFor fork config contract σ σ₀ g A I (immStore v) := by
  have hdec := clipperDecode_getStatus_none_short (I := I) hsz4 hshort
  exact (clipperGetStatusX_shortarg (v := v) (g := Sat256.ofUInt256 g) hpatch hsz4
    hsize hshort hreach)
    |>.reEquivDecodingFailed hcode hdispatch hdec

theorem clipperGetStatusPostCallReturnRuntime
    {v : ClipperImmutables} {code retBytes : ByteArray}
    {σ σ₀ A I g}
    {cs retVal} {evmPrice : EVM.State}
    (hcode : I.code = code)
    (hdispatch : dispatchMsg contract I.calldata = some getStatusTransition)
    (hdec :
      config.externalABI.decodeCalldata?
        (getStatusTransition.params.map Param.name)
        (transitionSignature getStatusTransition).paramTypes I.calldata =
          some (clipperGetStatusStore I))
    (hret :
      RDret fork code (Sat256.ofUInt256 g)
        (initState σ σ₀ (Sat256.ofUInt256 g) A I)
        σ' retBytes)
    (hbody :
      ExecTransitionBody fork config contract
        (initState σ σ₀ (Sat256.ofUInt256 g) A I)
        (clipperGetStatusStore I) getStatusTransition.body
        (.returned cs evmPrice retVal) (immStore v))
    (hAccountsPost : σ' = evmPrice.accountMap)
    (henc : returnEquiv retBytes retVal getStatusTransition.returnType) :
    runtimeRefinementFor fork config contract σ σ₀ g A I (immStore v) :=
  hret.reEquivExecutionGen hcode hdispatch hdec hbody
    hAccountsPost henc

set_option maxHeartbeats 200000000 in
theorem clipperGetStatusBody (v : ClipperImmutables) {code : ByteArray}
    (hpatch : patchRuntime clipperBytecode (patches v) = some code)
    {σ σ₀ A I} {g : UInt256}
    (hcode : I.code = code) (hsize : I.calldata.size < UInt256.size)
    (hwv : I.weiValue = ⟨0⟩)
    (hsel : selIs I (clipperSelBytes 11)) :
    runtimeRefinementFor fork config contract σ σ₀ g A I (immStore v) := by
  have hsz4 : 4 ≤ I.calldata.size :=
    calldata_size_ge_of_selIs I (clipperSelBytes 11) (by native_decide) hsel
  have hdispatch : dispatchMsg contract I.calldata = some getStatusTransition :=
    clipperDispatch_getStatus hsel
  have hreach := clipperReachGetStatusBody (fork := fork) (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := Sat256.ofUInt256 g)
    (v := v) hpatch hcode hwv hsz4 hsize hsel
  by_cases hsz36 : 36 ≤ I.calldata.size
  · have hdec := clipperDecode_getStatus_ok (I := I) hsz36
    obtain ⟨_, _, rd3185⟩ := clipperGetStatusX_decoded
      (v := v) (g := Sat256.ofUInt256 g) hpatch hsz36 hsize hreach
    obtain ⟨_, _, rd8460⟩ :=
      Benchmarks.Dss.Clipper.Reasoning.Reach.RD.clipperGetStatusToStatus
      (v := v) (hpatch := hpatch) rd3185 solcFreePtrMem_size
      (by simp only [List.length_singleton]; omega)
    let id : UInt256 := clipperGetStatusArgWord I
    let packed : UInt256 := solcSlotWord σ I ((solcMappingSlot ⟨12⟩ id) + ⟨3⟩)
    let tic : UInt256 := clipperSalesPackedTicWord packed
    let top : UInt256 := solcSlotWord σ I ((solcMappingSlot ⟨12⟩ id) + ⟨4⟩)
    let calcAddr : UInt256 := UInt256.land (solcSlotWord σ I ⟨4⟩) solcAddrMask
    have hhashMem :
        (twoWordHashMem id (⟨12⟩ : UInt256) solcFreePtrMem).size = 96 := by
      exact twoWordHashMem_size_96 id ⟨12⟩ solcFreePtrMem_size
    have hhashRead64 :
        (twoWordHashMem id (⟨12⟩ : UInt256) solcFreePtrMem).readWithPadding 64 32 =
          UInt256.toByteArray ⟨128⟩ := by
      exact twoWordHashMem_read64 id ⟨12⟩ solcFreePtrMem_size solcFreePtrMem_read64
    have hhashMload64 :
        (if (⟨64⟩ : UInt256).toNat ≥
              (twoWordHashMem id (⟨12⟩ : UInt256) solcFreePtrMem).size then ⟨0⟩
         else UInt256.ofNat
            (fromByteArrayBigEndian
              ((twoWordHashMem id (⟨12⟩ : UInt256) solcFreePtrMem).readWithPadding
                (⟨64⟩ : UInt256).toNat 32))) =
          ⟨128⟩ := by
      exact mloadFreePtrValue (by rw [hhashMem]; native_decide)
        hhashRead64
    let evmStele : EVM.State :=
      initState σ σ₀ (Sat256.ofUInt256 g) A I
    have hbaseSlot :
        clipperGetStatusSalesBaseSlot I = solcMappingSlot ⟨12⟩ id := by
      simpa [id] using clipperGetStatusSalesBaseSlot_eq I
    have hpackedStele :
        packed = solcSlotWord σ I (clipperGetStatusSalesPackedSlot I) := by
      simp [packed, clipperGetStatusSalesPackedSlot, hbaseSlot]
    have htopStele :
        top = solcSlotWord σ I (clipperGetStatusSalesTopSlot I) := by
      simp [top, clipperGetStatusSalesTopSlot, hbaseSlot]
    have hmask96 : clipperSalesUint96Mask.toNat = 2 ^ 96 - 1 := by
      native_decide
    have hticLt : tic.toNat < EVM.twoPow 96 := by
      simpa [tic, clipperSalesPackedTicWord, clipperSalesUint96Mask] using
        u256LandMaskToNatLtOfToNat
          (UInt256.div packed (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨160⟩))
          clipperSalesUint96Mask hmask96
    have hticClean : UInt256.land tic clipperSalesUint96Mask = tic := by
      exact u256LandMaskCleanOfToNat tic clipperSalesUint96Mask hmask96 hticLt
    have hticCleanStele :
        UInt256.land
            (clipperSalesPackedTicWord
              (solcSlotWord σ I ((solcMappingSlot ⟨12⟩ id) + ⟨3⟩)))
            clipperSalesUint96Mask =
          clipperSalesPackedTicWord
            (solcSlotWord σ I ((solcMappingSlot ⟨12⟩ id) + ⟨3⟩)) := by
      simpa [tic, packed] using hticClean
    have _hstatusPricePostCall :
        ∀
        (hle :
          (UInt256.land tic clipperSalesUint96Mask).toNat ≤
            (UInt256.ofNat I.header.timestamp).toNat)
        (hcalcCode :
          Reasoning.Theory.extCodeSizeWord σ calcAddr ≠ ⟨0⟩)
        (hdepth : I.depth.val < 1024),
          runtimeRefinementFor fork config contract σ σ₀ g A I (immStore v) := by
      intro hle hcalcCode hdepth
      obtain ⟨_, _, rd8502⟩ :=
        Benchmarks.Dss.Clipper.Reasoning.Reach.RD.clipperStatusAgeForPrice
          (v := v) (hpatch := hpatch) rd8460 (by simpa [tic, packed, id] using hle)
          (by simp only [List.length_cons, List.length_nil]; omega)
      obtain ⟨_, _, rd8549⟩ :=
        Benchmarks.Dss.Clipper.Reasoning.Reach.RD.clipperStatusPriceExtcodesizeGuard
          (v := v) (hpatch := hpatch) rd8502
          (by simpa [id] using hhashMload64)
          (by simpa [id] using hhashMem)
          (by simpa [id] using hhashRead64)
          (by simp only [List.length_cons, List.length_nil]; omega)
      obtain ⟨σ', z, o, A', k8565, C8565, rd8565, hcallPrice, hout⟩ :=
        Benchmarks.Dss.Clipper.Reasoning.Reach.RD.clipperStatusPricePostStaticcall
        (v := v) (hpatch := hpatch) rd8549
        (by simpa [calcAddr] using hcalcCode) hdepth (by simpa [id] using hhashMem)
        (by simp only [List.length_cons, List.length_nil]; omega)
      have hcalcAddrStele :
          clipperStatusCalcAddress evmStele = AccountAddress.ofUInt256 calcAddr := by
        simp [evmStele, clipperStatusCalcAddress, clipperStatusCalcWord, calcAddr,
          initState, Stele.EVM.storageLoad, State.lookupAccount, Account.lookupStorage,
          solcSlotWord]
      have htopWordStele : clipperGetStatusTopWord evmStele I = top := by
        simpa [-Std.ExtTreeMap.get?_eq_getElem?, evmStele, initState, clipperGetStatusTopWord, Stele.EVM.storageLoad,
          State.lookupAccount, Account.lookupStorage, solcSlotWord,
          clipperGetStatusSalesTopSlot, hbaseSlot] using htopStele.symm
      have htopRaw : top = solcSlotWord σ I ((solcMappingSlot ⟨12⟩ id) + ⟨4⟩) := by
        simpa [clipperGetStatusSalesTopSlot, hbaseSlot] using htopStele
      have hticWordStele : clipperGetStatusTicWord evmStele I = tic := by
        have hpackedWord := congrArg clipperSalesPackedTicWord hpackedStele.symm
        simpa [-Std.ExtTreeMap.get?_eq_getElem?, evmStele, initState, clipperGetStatusTicWord, Stele.EVM.storageLoad,
          State.lookupAccount, Account.lookupStorage, solcSlotWord,
          clipperGetStatusSalesPackedSlot, hbaseSlot, tic] using hpackedWord
      have hticPacked : tic = clipperSalesPackedTicWord
          (solcSlotWord σ I ((solcMappingSlot ⟨12⟩ id) + ⟨3⟩)) := by
        simpa [tic, packed] using
          congrArg clipperSalesPackedTicWord hpackedStele
      have hpriceAge :
          UInt256.sub (UInt256.ofNat I.header.timestamp)
              (UInt256.land
                (clipperSalesPackedTicWord
                  (solcSlotWord σ I ((solcMappingSlot ⟨12⟩ id) + ⟨3⟩)))
                clipperSalesUint96Mask) =
            UInt256.sub (UInt256.ofNat I.header.timestamp) tic := by
        rw [hticCleanStele, ← hticPacked]
      have htimestampStele :
          clipperTimestampWord evmStele = UInt256.ofNat I.header.timestamp := by
        simp [evmStele, initState, clipperTimestampWord]
      cases z
      · have hrev :=
          Benchmarks.Dss.Clipper.Reasoning.Reach.RD.clipperStatusPriceCallFailure
            (v := v) (hpatch := hpatch) rd8565 hout
            (by simp only [List.length_cons, List.length_nil]; omega)
        have hcalcCodeSteleNE :
            Reasoning.Theory.extCodeSizeWord σ calcAddr ≠ ⟨0⟩ := by
          exact hcalcCode
        have hcalcCodeStele :
            0 < (UInt256.ofNat
              ((evmStele.lookupAccount (clipperStatusCalcAddress evmStele)).option 0
                (fun acc => acc.code.size))).toNat := by
          simpa [-Std.ExtTreeMap.get?_eq_getElem?, evmStele, State.lookupAccount, initState] using
            extCodeSizeWord_ne_zero_lookup_code_pos
              (σ := σ) (target := calcAddr)
              (addr := clipperStatusCalcAddress evmStele)
              hcalcAddrStele hcalcCodeSteleNE
        let σ'_stele := σ'
        let A'_stele := A'
        let evmPriceStele : EVM.State :=
          { evmStele with
            accountMap := σ'_stele
            substate := A'_stele }
        have hcallPriceStele :
            typedCallViaEVM fork config evmStele
              (EVM.address (clipperStatusCalcAddress evmStele)) "price" 0
              [.int (Int.ofNat (clipperGetStatusTopWord evmStele I).toNat),
                .int (Int.ofNat
                  (UInt256.sub (clipperTimestampWord evmStele)
                    (clipperGetStatusTicWord evmStele I)).toNat)]
              (false, evmPriceStele, o) false := by
          have hcallPrice' := hcallPrice
          rw [hpriceAge, ← hcalcAddrStele, ← htopRaw, ← htopWordStele,
            ← htimestampStele, ← hticWordStele] at hcallPrice'
          exact hcallPrice'
        have hlePriceStele :
            (clipperGetStatusTicWord evmStele I).toNat ≤
              (clipperTimestampWord evmStele).toNat := by
          rw [hticWordStele, htimestampStele, ← hticClean]
          exact hle
        have hbody :=
          clipperGetStatusBodyRevertsPriceCallFailure v (evm := evmStele)
            (evmPrice := evmPriceStele) I (out := o)
            (by simpa [-Std.ExtTreeMap.get?_eq_getElem?, evmStele, initState] using hwv)
            hlePriceStele hcalcCodeStele hcallPriceStele
        exact hrev.reEquivExecutionRevert hcode hdispatch hdec hbody
      · obtain ⟨_, _, rd8583⟩ :=
          Benchmarks.Dss.Clipper.Reasoning.Reach.RD.clipperStatusPriceCallSuccessToDecode
            (v := v) (hpatch := hpatch) rd8565
            (by simp only [List.length_cons, List.length_nil]; omega)
        by_cases hshortOut : o.size < 32
        · have hrev :=
            Benchmarks.Dss.Clipper.Reasoning.Reach.RD.clipperStatusPriceReturnDecodeShortReverts
              (v := v) (hpatch := hpatch) rd8583
              (by simpa [id] using hhashMem)
              (by simpa [id] using hhashRead64)
              hshortOut hout
              (by simp only [List.length_cons, List.length_nil]; omega)
          have hpriceDecode :
              config.externalABI.decode? "price" o = none :=
            clipperStatusPriceDecode_none_short hshortOut
          have hcalcCodeSteleNE :
              Reasoning.Theory.extCodeSizeWord σ calcAddr ≠ ⟨0⟩ := by
            exact hcalcCode
          have hcalcCodeStele :
              0 < (UInt256.ofNat
                ((evmStele.lookupAccount (clipperStatusCalcAddress evmStele)).option 0
                  (fun acc => acc.code.size))).toNat := by
            simpa [-Std.ExtTreeMap.get?_eq_getElem?, evmStele, State.lookupAccount, initState] using
              extCodeSizeWord_ne_zero_lookup_code_pos
                (σ := σ) (target := calcAddr)
                (addr := clipperStatusCalcAddress evmStele)
                hcalcAddrStele hcalcCodeSteleNE
          let σ'_stele := σ'
          let A'_stele := A'
          let evmPriceStele : EVM.State :=
            { evmStele with
              accountMap := σ'_stele
              substate := A'_stele }
          have hcallPriceStele :
              typedCallViaEVM fork config evmStele
                (EVM.address (clipperStatusCalcAddress evmStele)) "price" 0
                [.int (Int.ofNat (clipperGetStatusTopWord evmStele I).toNat),
                  .int (Int.ofNat
                    (UInt256.sub (clipperTimestampWord evmStele)
                      (clipperGetStatusTicWord evmStele I)).toNat)]
                (true, evmPriceStele, o) false := by
            have hcallPrice' := hcallPrice
            rw [hpriceAge, ← hcalcAddrStele, ← htopRaw, ← htopWordStele,
              ← htimestampStele, ← hticWordStele] at hcallPrice'
            exact hcallPrice'
          have hlePriceStele :
              (clipperGetStatusTicWord evmStele I).toNat ≤
                (clipperTimestampWord evmStele).toNat := by
            rw [hticWordStele, htimestampStele, ← hticClean]
            exact hle
          have hbody :=
            clipperGetStatusBodyRevertsPriceDecode v (evm := evmStele)
              (evmPrice := evmPriceStele) I (out := o)
              (by simpa [-Std.ExtTreeMap.get?_eq_getElem?, evmStele, initState] using hwv)
              hlePriceStele hcalcCodeStele hcallPriceStele hpriceDecode
          exact hrev.reEquivExecutionRevert hcode hdispatch hdec hbody
        · have hloOut : 32 ≤ o.size := by omega
          obtain ⟨_, _, _rd8606⟩ :=
            Benchmarks.Dss.Clipper.Reasoning.Reach.RD.clipperStatusPriceReturnDecodeOk
              (v := v) (hpatch := hpatch) rd8583
              (by simpa [id] using hhashMem)
              (by simpa [id] using hhashRead64)
              hloOut hout
              (by simp only [List.length_cons, List.length_nil]; omega)
          have _hdec :
              config.externalABI.decode? "price" o =
                some (clipperStatusPriceValues o) :=
            clipperStatusPriceDecode_ok hloOut
          let ageForPrice : UInt256 :=
            UInt256.sub (UInt256.ofNat I.header.timestamp) (UInt256.land tic clipperSalesUint96Mask)
          let priceCallMem : ByteArray := twoWordHashMem id (⟨12⟩ : UInt256) solcFreePtrMem
          let pricePostMem : ByteArray :=
            clipperStatusPricePostCallMem top ageForPrice priceCallMem o
          have hpricePostMemSize : pricePostMem.size = 196 := by
            simpa [pricePostMem, priceCallMem, ageForPrice, top, id] using
              clipperStatusPricePostCallMem_size top ageForPrice hhashMem hout
          have hpricePostRead64 :
              pricePostMem.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩ := by
            simpa [pricePostMem, priceCallMem, ageForPrice, top, id] using
              clipperStatusPricePostCallMem_read64 top ageForPrice hhashMem hhashRead64 hout
          have hreturnScratchSize :
              (twoWordHashMem id (⟨12⟩ : UInt256) pricePostMem).size = 196 := by
            rw [twoWordHashMem_size_of_ge_64 id ⟨12⟩]
            · exact hpricePostMemSize
            · rw [hpricePostMemSize]
              omega
          have hreturnScratchRead64 :
              (twoWordHashMem id (⟨12⟩ : UInt256) pricePostMem).readWithPadding 64 32 =
                UInt256.toByteArray ⟨128⟩ := by
            exact twoWordHashMem_read64_of_ge id ⟨12⟩
              (by rw [hpricePostMemSize]; omega) hpricePostRead64
          have hcalcCodeSteleNE :
              Reasoning.Theory.extCodeSizeWord σ calcAddr ≠ ⟨0⟩ := by
            exact hcalcCode
          have hcalcCodeStele :
              0 < (UInt256.ofNat
                ((evmStele.lookupAccount (clipperStatusCalcAddress evmStele)).option 0
                  (fun acc => acc.code.size))).toNat := by
            simpa [-Std.ExtTreeMap.get?_eq_getElem?, evmStele, State.lookupAccount, initState] using
              extCodeSizeWord_ne_zero_lookup_code_pos
                (σ := σ) (target := calcAddr)
                (addr := clipperStatusCalcAddress evmStele)
                hcalcAddrStele hcalcCodeSteleNE
          let σ'_stele := σ'
          let A'_stele := A'
          let evmPriceStele : EVM.State :=
            { evmStele with
              accountMap := σ'_stele
              substate := A'_stele }
          have hPostAccounts : σ' = evmPriceStele.accountMap := by
            rfl
          have hcallPriceStele :
              typedCallViaEVM fork config evmStele
                (EVM.address (clipperStatusCalcAddress evmStele)) "price" 0
                [.int (Int.ofNat (clipperGetStatusTopWord evmStele I).toNat),
                  .int (Int.ofNat
                    (UInt256.sub (clipperTimestampWord evmStele)
                      (clipperGetStatusTicWord evmStele I)).toNat)]
                (true, evmPriceStele, o) false := by
            have hcallPrice' := hcallPrice
            rw [hpriceAge, ← hcalcAddrStele, ← htopRaw, ← htopWordStele,
              ← htimestampStele, ← hticWordStele] at hcallPrice'
            exact hcallPrice'
          have _hstatusDoneTailTrue :
              ∀
              (hleDone :
                (UInt256.land tic clipperSalesUint96Mask).toNat ≤
                  (UInt256.ofNat I.header.timestamp).toNat)
              (htail :
                (solcSlotWord σ' I ⟨6⟩).toNat <
                  (UInt256.sub (UInt256.ofNat I.header.timestamp)
                    (UInt256.land tic clipperSalesUint96Mask)).toNat),
                runtimeRefinementFor fork config contract σ σ₀ g A I (immStore v) := by
            intro hleDone htail
            obtain ⟨_, _, _rd3258⟩ :=
              Benchmarks.Dss.Clipper.Reasoning.Reach.RD.clipperStatusAfterPriceDoneTailTrue
                (v := v) (hpatch := hpatch) _rd8606 hleDone htail
                (clipperJumpDest3258 v hpatch)
                (by simp only [List.length_cons, List.length_nil]; omega)
            obtain ⟨_, _, _rd789⟩ :=
              Benchmarks.Dss.Clipper.Reasoning.Reach.RD.clipperGetStatusAfterStatusToReturnEncoder
                (v := v) (hpatch := hpatch) _rd3258
                (by
                  rw [clipperStatusPricePostCallMem_size]
                  · omega
                  · simpa [id] using hhashMem
                  · exact hout)
                (clipperJumpDestBeforeFirstPatch v hpatch (⟨789⟩ : UInt256)
                  (by native_decide))
                (by simp only [List.length_singleton]; omega)
            have _hret :=
              Benchmarks.Dss.Clipper.Reasoning.Reach.RD.clipperGetStatusReturnEncodeConcrete
                (v := v) (hpatch := hpatch)
                (by simpa [pricePostMem, priceCallMem, ageForPrice, top, id] using _rd789)
                hreturnScratchSize hreturnScratchRead64
                (by simp only [List.length_singleton]; omega)
            let usrWord : UInt256 := UInt256.land packed solcAddrMask
            let needsWord : UInt256 := clipperGetStatusNeedsRedoWord usrWord ⟨1⟩
            let priceWord : UInt256 := clipperStatusPriceWord o
            let lotWord : UInt256 :=
              solcSlotWord σ' I ((solcMappingSlot ⟨12⟩ id) + ⟨2⟩)
            let tabWord : UInt256 :=
              solcSlotWord σ' I ((solcMappingSlot ⟨12⟩ id) + ⟨1⟩)
            have hret :
                RDret fork code (Sat256.ofUInt256 g)
                  (initState σ σ₀ (Sat256.ofUInt256 g) A I)
                  σ'
                  (clipperGetStatusReturnBytes needsWord priceWord lotWord tabWord) := by
              simpa [needsWord, usrWord, priceWord, lotWord, tabWord, packed, id] using _hret
            have hdecPrice :
                config.externalABI.decode? "price" o =
                  some [.int (Int.ofNat priceWord.toNat)] := by
              simpa [priceWord, clipperStatusPriceValues] using _hdec
            have hlePriceStele :
                (clipperGetStatusTicWord evmStele I).toNat ≤
                  (clipperTimestampWord evmStele).toNat := by
              simpa [-Std.ExtTreeMap.get?_eq_getElem?, evmStele, initState, clipperGetStatusTicWord, clipperTimestampWord,
                Stele.EVM.storageLoad, State.lookupAccount, Account.lookupStorage,
                solcSlotWord, clipperGetStatusSalesPackedSlot, hbaseSlot,
                tic, packed, hticClean, hticCleanStele] using hle
            have hleDoneStele :
                (clipperGetStatusTicWord evmStele I).toNat ≤
                  (clipperTimestampWord evmPriceStele).toNat := by
              simpa [-Std.ExtTreeMap.get?_eq_getElem?, evmStele, evmPriceStele, initState, clipperGetStatusTicWord,
                clipperTimestampWord, Stele.EVM.storageLoad, State.lookupAccount,
                Account.lookupStorage, solcSlotWord, clipperGetStatusSalesPackedSlot,
                hbaseSlot, tic, packed, hticClean, hticCleanStele] using hleDone
            have htailSlotStele :
                solcSlotWord σ' I ⟨6⟩ = solcSlotWord σ'_stele I ⟨6⟩ := by
              exact congrArg (fun m => solcSlotWord m I ⟨6⟩) hPostAccounts
            have htailStele :
                (clipperStatusTailWord evmPriceStele).toNat <
                  (UInt256.sub (clipperTimestampWord evmPriceStele)
                    (clipperGetStatusTicWord evmStele I)).toNat := by
              simpa [-Std.ExtTreeMap.get?_eq_getElem?, evmStele, evmPriceStele, initState, clipperStatusTailWord,
                clipperTimestampWord, clipperGetStatusTicWord, Stele.EVM.storageLoad,
                State.lookupAccount, Account.lookupStorage, solcSlotWord,
                clipperGetStatusSalesPackedSlot, hbaseSlot, htailSlotStele,
                tic, packed, hticClean, hticCleanStele] using htail
            have hbody :=
              clipperGetStatusBodyReturnsDoneTailTrue v (evm := evmStele)
                (evmPrice := evmPriceStele) I priceWord (out := o)
                (by simpa [-Std.ExtTreeMap.get?_eq_getElem?, evmStele, initState] using hwv)
                hlePriceStele hcalcCodeStele hcallPriceStele hdecPrice hleDoneStele htailStele
            have hlotWordStele :
                lotWord = clipperGetStatusLotWord evmPriceStele I := by
              have hslot :=
                congrArg (fun m => solcSlotWord m I ((solcMappingSlot ⟨12⟩ id) + ⟨2⟩)) hPostAccounts
              simpa [lotWord, evmPriceStele, clipperGetStatusLotWord, initState,
                Stele.EVM.storageLoad, State.lookupAccount, Account.lookupStorage,
                solcSlotWord, clipperGetStatusSalesLotSlot, hbaseSlot] using hslot
            have htabWordStele :
                tabWord = clipperGetStatusTabWord evmPriceStele I := by
              have hslot :=
                congrArg (fun m => solcSlotWord m I ((solcMappingSlot ⟨12⟩ id) + ⟨1⟩)) hPostAccounts
              simpa [tabWord, evmPriceStele, clipperGetStatusTabWord, initState,
                Stele.EVM.storageLoad, State.lookupAccount, Account.lookupStorage,
                solcSlotWord, clipperGetStatusSalesTabSlot, hbaseSlot] using hslot
            have hneedsNorm :
                UInt256.isZero (UInt256.isZero needsWord) =
                  (clipperGetStatusNeedsRedo evmStele I true).toUInt256 := by
              simpa [needsWord, usrWord, evmStele, initState, clipperGetStatusNeedsRedo,
                clipperGetStatusUsrWord, Stele.EVM.storageLoad, State.lookupAccount,
                Account.lookupStorage, solcSlotWord, clipperGetStatusSalesPackedSlot,
                hbaseSlot, packed] using
                  clipperGetStatusNeedsRedoWord_bool usrWord ⟨1⟩ true (by native_decide)
            have henc :
                returnEquiv (clipperGetStatusReturnBytes needsWord priceWord lotWord tabWord)
                  (some [.bool (clipperGetStatusNeedsRedo evmStele I true),
                    .int (Int.ofNat priceWord.toNat),
                    .int (Int.ofNat (clipperGetStatusLotWord evmPriceStele I).toNat),
                    .int (Int.ofNat (clipperGetStatusTabWord evmPriceStele I).toNat)])
                  getStatusTransition.returnType := by
              rw [← hlotWordStele, ← htabWordStele]
              exact clipperGetStatusReturnEquiv needsWord
                (clipperGetStatusNeedsRedo evmStele I true) priceWord lotWord tabWord hneedsNorm
            exact clipperGetStatusPostCallReturnRuntime hcode hdispatch hdec hret hbody
              (by simpa [evmPriceStele] using hPostAccounts)
              henc
          let priceWord : UInt256 := clipperStatusPriceWord o
          have hdecPrice :
              config.externalABI.decode? "price" o =
                some [.int (Int.ofNat priceWord.toNat)] := by
            simpa [priceWord, clipperStatusPriceValues] using _hdec
          have hlePriceStele :
              (clipperGetStatusTicWord evmStele I).toNat ≤
                (clipperTimestampWord evmStele).toNat := by
            simpa [-Std.ExtTreeMap.get?_eq_getElem?, evmStele, initState, clipperGetStatusTicWord, clipperTimestampWord,
              Stele.EVM.storageLoad, State.lookupAccount, Account.lookupStorage,
              solcSlotWord, clipperGetStatusSalesPackedSlot, hbaseSlot,
              tic, packed, hticClean, hticCleanStele] using hle
          by_cases hleDone :
              (UInt256.land tic clipperSalesUint96Mask).toNat ≤
                (UInt256.ofNat I.header.timestamp).toNat
          · have hleDoneStele :
                (clipperGetStatusTicWord evmStele I).toNat ≤
                  (clipperTimestampWord evmPriceStele).toNat := by
              simpa [-Std.ExtTreeMap.get?_eq_getElem?, evmStele, evmPriceStele, initState, clipperGetStatusTicWord,
                clipperTimestampWord, Stele.EVM.storageLoad, State.lookupAccount,
                Account.lookupStorage, solcSlotWord, clipperGetStatusSalesPackedSlot,
                hbaseSlot, tic, packed, hticClean, hticCleanStele] using
                hleDone
            by_cases htailLt :
                (solcSlotWord σ' I ⟨6⟩).toNat <
                  (UInt256.sub (UInt256.ofNat I.header.timestamp)
                    (UInt256.land tic clipperSalesUint96Mask)).toNat
            · exact _hstatusDoneTailTrue hleDone htailLt
            · have htailLe :
                  (UInt256.sub (UInt256.ofNat I.header.timestamp)
                      (UInt256.land tic clipperSalesUint96Mask)).toNat ≤
                    (solcSlotWord σ' I ⟨6⟩).toNat := by
                exact Nat.le_of_not_gt htailLt
              have htailSlotStele :
                  solcSlotWord σ' I ⟨6⟩ = solcSlotWord σ'_stele I ⟨6⟩ := by
                exact congrArg (fun m => solcSlotWord m I ⟨6⟩) hPostAccounts
              have htailStele :
                  (UInt256.sub (clipperTimestampWord evmPriceStele)
                      (clipperGetStatusTicWord evmStele I)).toNat ≤
                    (clipperStatusTailWord evmPriceStele).toNat := by
                simpa [-Std.ExtTreeMap.get?_eq_getElem?, evmStele, evmPriceStele, initState, clipperStatusTailWord,
                  clipperTimestampWord, clipperGetStatusTicWord, Stele.EVM.storageLoad,
                  State.lookupAccount, Account.lookupStorage, solcSlotWord,
                  clipperGetStatusSalesPackedSlot, hbaseSlot, htailSlotStele,
                  tic, packed, hticClean, hticCleanStele] using htailLe
              by_cases hmul :
                  priceWord.toNat * clipperRayWord.toNat < UInt256.size
              · by_cases htopZero : top = ⟨0⟩
                · have hinv :=
                    Benchmarks.Dss.Clipper.Reasoning.Reach.RD.clipperStatusAfterPriceRdivDivZeroInvalid
                      (v := v) (hpatch := hpatch) _rd8606 hleDone htailLe
                      (by simpa [priceWord] using hmul) htopZero
                      (by simp only [List.length_cons, List.length_nil]; omega)
                  have htopSteleZero : clipperGetStatusTopWord evmStele I = ⟨0⟩ := by
                    simpa [-Std.ExtTreeMap.get?_eq_getElem?, evmStele, initState, clipperGetStatusTopWord,
                      Stele.EVM.storageLoad, State.lookupAccount, Account.lookupStorage,
                      solcSlotWord, clipperGetStatusSalesTopSlot, hbaseSlot,
                      top] using htopZero
                  have hbody :=
                    clipperGetStatusBodyRevertsRdivDivZero v (evm := evmStele)
                      (evmPrice := evmPriceStele) I priceWord (out := o)
                      (by simpa [-Std.ExtTreeMap.get?_eq_getElem?, evmStele, initState] using hwv)
                      hlePriceStele hcalcCodeStele hcallPriceStele hdecPrice
                      hleDoneStele htailStele hmul htopSteleZero
                  exact RDinvalid.reEquivExecutionInvalid hcode hinv hdispatch hdec hbody
                · obtain ⟨_, _, _rd3258⟩ :=
                    Benchmarks.Dss.Clipper.Reasoning.Reach.RD.clipperStatusAfterPriceRdivBranch
                      (v := v) (hpatch := hpatch) _rd8606 hleDone htailLe
                      (by simpa [priceWord] using hmul) htopZero
                      (clipperJumpDest3258 v hpatch)
                      (by simp only [List.length_cons, List.length_nil]; omega)
                  obtain ⟨_, _, _rd789⟩ :=
                    Benchmarks.Dss.Clipper.Reasoning.Reach.RD.clipperGetStatusAfterStatusToReturnEncoder
                      (v := v) (hpatch := hpatch) _rd3258
                      (by
                        rw [clipperStatusPricePostCallMem_size]
                        · omega
                        · simpa [id] using hhashMem
                        · exact hout)
                      (clipperJumpDestBeforeFirstPatch v hpatch (⟨789⟩ : UInt256)
                        (by native_decide))
                      (by simp only [List.length_singleton]; omega)
                  have _hret :=
                    Benchmarks.Dss.Clipper.Reasoning.Reach.RD.clipperGetStatusReturnEncodeConcrete
                      (v := v) (hpatch := hpatch)
                      (by simpa [pricePostMem, priceCallMem, ageForPrice, top, id] using _rd789)
                      hreturnScratchSize hreturnScratchRead64
                      (by simp only [List.length_singleton]; omega)
                  let usrWord : UInt256 := UInt256.land packed solcAddrMask
                  let ratioWord : UInt256 := UInt256.div (UInt256.mul priceWord clipperRayWord) top
                  let cuspWord : UInt256 := solcSlotWord σ' I ⟨7⟩
                  let doneWord : UInt256 := UInt256.lt ratioWord cuspWord
                  let needsWord : UInt256 := clipperGetStatusNeedsRedoWord usrWord doneWord
                  let lotWord : UInt256 :=
                    solcSlotWord σ' I ((solcMappingSlot ⟨12⟩ id) + ⟨2⟩)
                  let tabWord : UInt256 :=
                    solcSlotWord σ' I ((solcMappingSlot ⟨12⟩ id) + ⟨1⟩)
                  have hret :
                      RDret fork code (Sat256.ofUInt256 g)
                        (initState σ σ₀ (Sat256.ofUInt256 g) A I)
                        σ'
                        (clipperGetStatusReturnBytes needsWord priceWord lotWord tabWord) := by
                    simpa [needsWord, usrWord, doneWord, ratioWord, cuspWord, priceWord,
                      lotWord, tabWord, packed, id] using _hret
                  have htopWordStele : clipperGetStatusTopWord evmStele I = top := by
                    simpa [-Std.ExtTreeMap.get?_eq_getElem?, evmStele, initState, clipperGetStatusTopWord,
                      Stele.EVM.storageLoad, State.lookupAccount, Account.lookupStorage,
                      solcSlotWord, clipperGetStatusSalesTopSlot, hbaseSlot] using htopStele.symm
                  have htopSteleNe : clipperGetStatusTopWord evmStele I ≠ ⟨0⟩ := by
                    intro hzero
                    exact htopZero (by simpa [htopWordStele] using hzero)
                  have hlotWordStele :
                      lotWord = clipperGetStatusLotWord evmPriceStele I := by
                    have hslot :=
                      congrArg (fun m => solcSlotWord m I ((solcMappingSlot ⟨12⟩ id) + ⟨2⟩)) hPostAccounts
                    simpa [lotWord, evmPriceStele, clipperGetStatusLotWord, initState,
                      Stele.EVM.storageLoad, State.lookupAccount, Account.lookupStorage,
                      solcSlotWord, clipperGetStatusSalesLotSlot, hbaseSlot] using hslot
                  have htabWordStele :
                      tabWord = clipperGetStatusTabWord evmPriceStele I := by
                    have hslot :=
                      congrArg (fun m => solcSlotWord m I ((solcMappingSlot ⟨12⟩ id) + ⟨1⟩)) hPostAccounts
                    simpa [tabWord, evmPriceStele, clipperGetStatusTabWord, initState,
                      Stele.EVM.storageLoad, State.lookupAccount, Account.lookupStorage,
                      solcSlotWord, clipperGetStatusSalesTabSlot, hbaseSlot] using hslot
                  have hcuspWordStele : cuspWord = clipperStatusCuspWord evmPriceStele := by
                    have hslot :=
                      congrArg (fun m => solcSlotWord m I ⟨7⟩) hPostAccounts
                    simpa [cuspWord, evmPriceStele, clipperStatusCuspWord, initState,
                      Stele.EVM.storageLoad, State.lookupAccount, Account.lookupStorage,
                      solcSlotWord] using hslot
                  have hratioWordStele :
                      ratioWord =
                        UInt256.div (UInt256.mul priceWord clipperRayWord)
                          (clipperGetStatusTopWord evmStele I) := by
                    simp [ratioWord, htopWordStele]
                  by_cases hratio : ratioWord.toNat < (clipperStatusCuspWord evmPriceStele).toNat
                  · have hdoneEval :
                        evalExpr? config
                          { contract := contract,
                            locals := clipperStatusRatioLocals
                              (clipperGetStatusTicWord evmStele I)
                              (clipperGetStatusTopWord evmStele I)
                              (UInt256.sub (clipperTimestampWord evmStele)
                                (clipperGetStatusTicWord evmStele I)) priceWord
                              (UInt256.sub (clipperTimestampWord evmPriceStele)
                                (clipperGetStatusTicWord evmStele I))
                              (UInt256.div (UInt256.mul priceWord clipperRayWord)
                                (clipperGetStatusTopWord evmStele I)), immutables := immStore v }
                          evmPriceStele (.binary .lt (.var "ratio") (.storage cuspRef)) =
                            .ok (.bool true) := by
                      rw [← hratioWordStele]
                      exact clipperEvalStatusRatioCuspCond_true v evmPriceStele
                        (clipperGetStatusTicWord evmStele I)
                        (clipperGetStatusTopWord evmStele I)
                        (UInt256.sub (clipperTimestampWord evmStele)
                          (clipperGetStatusTicWord evmStele I)) priceWord
                        (UInt256.sub (clipperTimestampWord evmPriceStele)
                          (clipperGetStatusTicWord evmStele I)) ratioWord hratio
                    have hdoneWordOne : doneWord = ⟨1⟩ := by
                      unfold doneWord
                      exact ult_one (by simpa [ratioWord, cuspWord, hcuspWordStele] using hratio)
                    have hdoneNorm :
                        UInt256.isZero (UInt256.isZero doneWord) = true.toUInt256 := by
                      rw [hdoneWordOne]
                      native_decide
                    have hneedsNorm :
                        UInt256.isZero (UInt256.isZero needsWord) =
                          (clipperGetStatusNeedsRedo evmStele I true).toUInt256 := by
                      simpa [needsWord, usrWord, evmStele, initState, clipperGetStatusNeedsRedo,
                        clipperGetStatusUsrWord, Stele.EVM.storageLoad, State.lookupAccount,
                        Account.lookupStorage, solcSlotWord, clipperGetStatusSalesPackedSlot,
                        hbaseSlot, packed] using
                          clipperGetStatusNeedsRedoWord_bool usrWord doneWord true hdoneNorm
                    have hbody :=
                      clipperGetStatusBodyReturnsRdivBranch v (evm := evmStele)
                        (evmPrice := evmPriceStele) I priceWord (out := o)
                        (by simpa [-Std.ExtTreeMap.get?_eq_getElem?, evmStele, initState] using hwv)
                        hlePriceStele hcalcCodeStele hcallPriceStele hdecPrice hleDoneStele
                        htailStele hmul htopSteleNe true hdoneEval
                    have henc :
                        returnEquiv
                          (clipperGetStatusReturnBytes needsWord priceWord lotWord tabWord)
                          (some [.bool (clipperGetStatusNeedsRedo evmStele I true),
                            .int (Int.ofNat priceWord.toNat),
                            .int (Int.ofNat (clipperGetStatusLotWord evmPriceStele I).toNat),
                            .int (Int.ofNat (clipperGetStatusTabWord evmPriceStele I).toNat)])
                          getStatusTransition.returnType := by
                      rw [← hlotWordStele, ← htabWordStele]
                      exact clipperGetStatusReturnEquiv needsWord
                        (clipperGetStatusNeedsRedo evmStele I true) priceWord lotWord tabWord
                        hneedsNorm
                    exact clipperGetStatusPostCallReturnRuntime hcode hdispatch hdec hret hbody
                      (by simpa [evmPriceStele] using hPostAccounts) henc
                  · have hratioLe :
                        (clipperStatusCuspWord evmPriceStele).toNat ≤ ratioWord.toNat := by
                      exact Nat.le_of_not_gt hratio
                    have hdoneEval :
                        evalExpr? config
                          { contract := contract,
                            locals := clipperStatusRatioLocals
                              (clipperGetStatusTicWord evmStele I)
                              (clipperGetStatusTopWord evmStele I)
                              (UInt256.sub (clipperTimestampWord evmStele)
                                (clipperGetStatusTicWord evmStele I)) priceWord
                              (UInt256.sub (clipperTimestampWord evmPriceStele)
                                (clipperGetStatusTicWord evmStele I))
                              (UInt256.div (UInt256.mul priceWord clipperRayWord)
                                (clipperGetStatusTopWord evmStele I)), immutables := immStore v }
                          evmPriceStele (.binary .lt (.var "ratio") (.storage cuspRef)) =
                            .ok (.bool false) := by
                      rw [← hratioWordStele]
                      exact clipperEvalStatusRatioCuspCond_false v evmPriceStele
                        (clipperGetStatusTicWord evmStele I)
                        (clipperGetStatusTopWord evmStele I)
                        (UInt256.sub (clipperTimestampWord evmStele)
                          (clipperGetStatusTicWord evmStele I)) priceWord
                        (UInt256.sub (clipperTimestampWord evmPriceStele)
                          (clipperGetStatusTicWord evmStele I)) ratioWord hratioLe
                    have hdoneWordZero : doneWord = ⟨0⟩ := by
                      unfold doneWord
                      exact ult_zero (by simpa [ratioWord, cuspWord, hcuspWordStele] using hratioLe)
                    have hdoneNorm :
                        UInt256.isZero (UInt256.isZero doneWord) = false.toUInt256 := by
                      rw [hdoneWordZero]
                      native_decide
                    have hneedsNorm :
                        UInt256.isZero (UInt256.isZero needsWord) =
                          (clipperGetStatusNeedsRedo evmStele I false).toUInt256 := by
                      simpa [needsWord, usrWord, evmStele, initState, clipperGetStatusNeedsRedo,
                        clipperGetStatusUsrWord, Stele.EVM.storageLoad, State.lookupAccount,
                        Account.lookupStorage, solcSlotWord, clipperGetStatusSalesPackedSlot,
                        hbaseSlot, packed] using
                          clipperGetStatusNeedsRedoWord_bool usrWord doneWord false hdoneNorm
                    have hbody :=
                      clipperGetStatusBodyReturnsRdivBranch v (evm := evmStele)
                        (evmPrice := evmPriceStele) I priceWord (out := o)
                        (by simpa [-Std.ExtTreeMap.get?_eq_getElem?, evmStele, initState] using hwv)
                        hlePriceStele hcalcCodeStele hcallPriceStele hdecPrice hleDoneStele
                        htailStele hmul htopSteleNe false hdoneEval
                    have henc :
                        returnEquiv
                          (clipperGetStatusReturnBytes needsWord priceWord lotWord tabWord)
                          (some [.bool (clipperGetStatusNeedsRedo evmStele I false),
                            .int (Int.ofNat priceWord.toNat),
                            .int (Int.ofNat (clipperGetStatusLotWord evmPriceStele I).toNat),
                            .int (Int.ofNat (clipperGetStatusTabWord evmPriceStele I).toNat)])
                          getStatusTransition.returnType := by
                      rw [← hlotWordStele, ← htabWordStele]
                      exact clipperGetStatusReturnEquiv needsWord
                        (clipperGetStatusNeedsRedo evmStele I false) priceWord lotWord tabWord
                        hneedsNorm
                    exact clipperGetStatusPostCallReturnRuntime hcode hdispatch hdec hret hbody
                      (by simpa [evmPriceStele] using hPostAccounts)
                      henc
              · have hover :
                    UInt256.size ≤ priceWord.toNat * clipperRayWord.toNat := by
                  exact Nat.le_of_not_gt hmul
                have hrev :=
                  Benchmarks.Dss.Clipper.Reasoning.Reach.RD.clipperStatusAfterPriceRdivMulRevert
                    (v := v) (hpatch := hpatch) _rd8606 hleDone htailLe
                    (by simpa [priceWord] using hover)
                    (by simp only [List.length_cons, List.length_nil]; omega)
                have hbody :=
                  clipperGetStatusBodyRevertsRdivMul v (evm := evmStele)
                    (evmPrice := evmPriceStele) I priceWord (out := o)
                    (by simpa [-Std.ExtTreeMap.get?_eq_getElem?, evmStele, initState] using hwv)
                    hlePriceStele hcalcCodeStele hcallPriceStele hdecPrice
                    hleDoneStele htailStele hover
                exact hrev.reEquivExecutionRevert hcode hdispatch hdec hbody
          · have hltDone :
                (UInt256.ofNat I.header.timestamp).toNat <
                  (UInt256.land tic clipperSalesUint96Mask).toNat := by
              exact Nat.lt_of_not_ge hleDone
            have hrev :=
              Benchmarks.Dss.Clipper.Reasoning.Reach.RD.clipperStatusAgeForDoneRevert
                (v := v) (hpatch := hpatch) _rd8606 hltDone
                (by simp only [List.length_cons, List.length_nil]; omega)
            have hltDoneStele :
                (clipperTimestampWord evmPriceStele).toNat <
                  (clipperGetStatusTicWord evmStele I).toNat := by
              simpa [-Std.ExtTreeMap.get?_eq_getElem?, evmStele, evmPriceStele, initState, clipperGetStatusTicWord,
                clipperTimestampWord, Stele.EVM.storageLoad, State.lookupAccount,
                Account.lookupStorage, solcSlotWord, clipperGetStatusSalesPackedSlot,
                hbaseSlot, tic, packed, hticClean, hticCleanStele] using
                hltDone
            have hbody :=
              clipperGetStatusBodyRevertsAgeForDone v (evm := evmStele)
                (evmPrice := evmPriceStele) I priceWord (out := o)
                (by simpa [-Std.ExtTreeMap.get?_eq_getElem?, evmStele, initState] using hwv)
                hlePriceStele hcalcCodeStele hcallPriceStele hdecPrice hltDoneStele
            exact hrev.reEquivExecutionRevert hcode hdispatch hdec hbody
    by_cases hle :
        (UInt256.land tic clipperSalesUint96Mask).toNat ≤
          (UInt256.ofNat I.header.timestamp).toNat
    · obtain ⟨_, _, rd8502⟩ :=
        Benchmarks.Dss.Clipper.Reasoning.Reach.RD.clipperStatusAgeForPrice
          (v := v) (hpatch := hpatch) rd8460 (by simpa [tic, packed, id] using hle)
          (by simp only [List.length_cons, List.length_nil]; omega)
      obtain ⟨_, _, rd8549⟩ :=
        Benchmarks.Dss.Clipper.Reasoning.Reach.RD.clipperStatusPriceExtcodesizeGuard
          (v := v) (hpatch := hpatch) rd8502
          (by simpa [id] using hhashMload64)
          (by simpa [id] using hhashMem)
          (by simpa [id] using hhashRead64)
          (by simp only [List.length_cons, List.length_nil]; omega)
      have hlePriceStele :
          (clipperGetStatusTicWord evmStele I).toNat ≤
            (clipperTimestampWord evmStele).toNat := by
        simpa [-Std.ExtTreeMap.get?_eq_getElem?, evmStele, initState, clipperGetStatusTicWord, clipperTimestampWord,
          Stele.EVM.storageLoad, State.lookupAccount, Account.lookupStorage,
          solcSlotWord, clipperGetStatusSalesPackedSlot, hbaseSlot,
          tic, packed, hticClean, hticCleanStele] using hle
      by_cases hcalcCode :
          Reasoning.Theory.extCodeSizeWord σ calcAddr ≠ ⟨0⟩
      · by_cases hdepth : I.depth.val < 1024
        · exact _hstatusPricePostCall hle hcalcCode hdepth
        · have hdepthEq : I.depth = (1024 : Fin 1025) := by
            have hval : I.depth.val = 1024 := by
              have hleDepth : I.depth.val ≤ 1024 := Nat.le_of_lt_succ I.depth.isLt
              have hgeDepth : 1024 ≤ I.depth.val := Nat.le_of_not_gt hdepth
              exact Nat.le_antisymm hleDepth hgeDepth
            apply Fin.ext
            simpa using hval
          let ageForPrice : UInt256 :=
            UInt256.sub (UInt256.ofNat I.header.timestamp) (UInt256.land tic clipperSalesUint96Mask)
          let priceCallMem : ByteArray := twoWordHashMem id (⟨12⟩ : UInt256) solcFreePtrMem
          obtain ⟨_, _, rd8565⟩ :=
            Benchmarks.Dss.Clipper.Reasoning.Reach.RD.clipperStatusPriceCallDepthLimit
              (v := v) (hpatch := hpatch) rd8549
              (by simpa [calcAddr] using hcalcCode) hdepthEq
              (by simp only [List.length_cons, List.length_nil]; omega)
          have hrev :=
            Benchmarks.Dss.Clipper.Reasoning.Reach.RD.clipperStatusPriceCallFailure
              (v := v) (hpatch := hpatch) rd8565 (by native_decide)
              (by simp only [List.length_cons, List.length_nil]; omega)
          have hcalcAddrStele :
              clipperStatusCalcAddress evmStele = AccountAddress.ofUInt256 calcAddr := by
            simp [evmStele, clipperStatusCalcAddress, clipperStatusCalcWord, calcAddr,
              initState, Stele.EVM.storageLoad, State.lookupAccount, Account.lookupStorage,
              solcSlotWord]
          have hcalcCodeSteleNE :
              Reasoning.Theory.extCodeSizeWord σ calcAddr ≠ ⟨0⟩ := by
            exact hcalcCode
          have hcalcCodeStele :
              0 < (UInt256.ofNat
                ((evmStele.lookupAccount (clipperStatusCalcAddress evmStele)).option 0
                  (fun acc => acc.code.size))).toNat := by
            simpa [-Std.ExtTreeMap.get?_eq_getElem?, evmStele, State.lookupAccount, initState] using
              extCodeSizeWord_ne_zero_lookup_code_pos
                (σ := σ) (target := calcAddr)
                (addr := clipperStatusCalcAddress evmStele)
                hcalcAddrStele hcalcCodeSteleNE
          have hdepthInit : evmStele.executionEnv.depth = 1024 := by
            simpa [-Std.ExtTreeMap.get?_eq_getElem?, evmStele, initState] using hdepthEq
          let evmPriceStele : EVM.State :=
            { evmStele with
              substate :=
                (Ethereum.EVM.callSubstate fork evmStele.accountMap
                  (EVM.address (clipperStatusCalcAddress evmStele)) evmStele.substate) }
          have hcd :
              config.externalABI.encode? "price"
                [.int (Int.ofNat (clipperGetStatusTopWord evmStele I).toNat),
                  .int (Int.ofNat
                    (UInt256.sub (clipperTimestampWord evmStele)
                      (clipperGetStatusTicWord evmStele I)).toNat)] =
                some ((clipperStatusPriceCalldataMem top ageForPrice priceCallMem)
                  |>.readWithPadding 128 68) := by
            have hcdRaw :
                config.externalABI.encode? "price"
                    [.int (Int.ofNat top.toNat), .int (Int.ofNat ageForPrice.toNat)] =
                  some ((clipperStatusPriceCalldataMem top ageForPrice priceCallMem)
                    |>.readWithPadding 128 68) := by
              simpa [priceCallMem, ageForPrice, top, id] using
                clipperStatusPriceEncode_eq top ageForPrice hhashMem
            have htopWordStele : clipperGetStatusTopWord evmStele I = top := by
              simpa [-Std.ExtTreeMap.get?_eq_getElem?, evmStele, initState, clipperGetStatusTopWord, Stele.EVM.storageLoad,
                State.lookupAccount, Account.lookupStorage, solcSlotWord,
                clipperGetStatusSalesTopSlot, hbaseSlot] using htopStele.symm
            have hticWordStele : clipperGetStatusTicWord evmStele I = tic := by
              have hpackedWord := congrArg clipperSalesPackedTicWord hpackedStele.symm
              simpa [-Std.ExtTreeMap.get?_eq_getElem?, evmStele, initState, clipperGetStatusTicWord, Stele.EVM.storageLoad,
                State.lookupAccount, Account.lookupStorage, solcSlotWord,
                clipperGetStatusSalesPackedSlot, hbaseSlot, tic] using hpackedWord
            have htimestampStele :
                clipperTimestampWord evmStele = UInt256.ofNat I.header.timestamp := by
              simp [evmStele, initState, clipperTimestampWord]
            have hageForPriceStele :
                UInt256.sub (clipperTimestampWord evmStele) (clipperGetStatusTicWord evmStele I) =
                  ageForPrice := by
              simp [htimestampStele, hticWordStele, ageForPrice, hticClean]
            rw [htopWordStele, hageForPriceStele]
            exact hcdRaw
          have hcallPriceStele :
              typedCallViaEVM fork config evmStele
                (EVM.address (clipperStatusCalcAddress evmStele)) "price" 0
                [.int (Int.ofNat (clipperGetStatusTopWord evmStele I).toNat),
                  .int (Int.ofNat
                    (UInt256.sub (clipperTimestampWord evmStele)
                      (clipperGetStatusTicWord evmStele I)).toNat)]
                (false, evmPriceStele, ByteArray.empty) false := by
            simpa [evmPriceStele] using
              (callNotMade_depthLimit (cfg := config) (evm := evmStele)
                (tgt := EVM.address (clipperStatusCalcAddress evmStele))
                (name := "price")
                (args :=
                  [.int (Int.ofNat (clipperGetStatusTopWord evmStele I).toNat),
                    .int (Int.ofNat
                      (UInt256.sub (clipperTimestampWord evmStele)
                        (clipperGetStatusTicWord evmStele I)).toNat)])
                (callPerm := false)
                (calldata :=
                  (clipperStatusPriceCalldataMem top ageForPrice priceCallMem)
                    |>.readWithPadding 128 68)
                hcd hdepthInit)
          have hbody :=
            clipperGetStatusBodyRevertsPriceCallFailure v (evm := evmStele)
              (evmPrice := evmPriceStele) I (out := ByteArray.empty)
              (by simpa [-Std.ExtTreeMap.get?_eq_getElem?, evmStele, initState] using hwv)
              hlePriceStele hcalcCodeStele hcallPriceStele
          exact hrev.reEquivExecutionRevert hcode hdispatch hdec hbody
      · have hcalcZero :
            Reasoning.Theory.extCodeSizeWord σ calcAddr = ⟨0⟩ :=
          not_ne_iff.mp hcalcCode
        have hrev :=
          Benchmarks.Dss.Clipper.Reasoning.Reach.RD.clipperStatusPriceNoCode
            (v := v) hpatch rd8549
            (by simpa [calcAddr] using hcalcZero)
            (by simp only [List.length_cons, List.length_nil]; omega)
        have hcalcAddrStele :
            clipperStatusCalcAddress evmStele = AccountAddress.ofUInt256 calcAddr := by
          simp [evmStele, clipperStatusCalcAddress, clipperStatusCalcWord, calcAddr,
            initState, Stele.EVM.storageLoad, State.lookupAccount, Account.lookupStorage,
            solcSlotWord]
        have hcalcZeroStele :
            Reasoning.Theory.extCodeSizeWord σ calcAddr = ⟨0⟩ := by
          exact hcalcZero
        have hnoCodeStele :
            (UInt256.ofNat
              ((evmStele.lookupAccount (clipperStatusCalcAddress evmStele)).option 0
                (fun acc => acc.code.size))).toNat = 0 := by
          rw [hcalcAddrStele]
          unfold Reasoning.Theory.extCodeSizeWord at hcalcZeroStele
          simp [-Std.ExtTreeMap.get?_eq_getElem?, evmStele, State.lookupAccount, initState] at hcalcZeroStele ⊢
          cases hacc : σ.get? (AccountAddress.ofUInt256 calcAddr) with
          | none =>
              native_decide
          | some acc =>
              simp [-Std.ExtTreeMap.get?_eq_getElem?, hacc] at hcalcZeroStele ⊢
              exact congrArg UInt256.toNat hcalcZeroStele
        have hbody :=
          clipperGetStatusBodyRevertsPriceNoCode (fork := fork) v evmStele I
            (by simpa [-Std.ExtTreeMap.get?_eq_getElem?, evmStele, initState] using hwv)
            hlePriceStele hnoCodeStele
        exact hrev.reEquivExecutionRevert hcode hdispatch hdec hbody
    · have hlt :
          (UInt256.ofNat I.header.timestamp).toNat <
            (UInt256.land tic clipperSalesUint96Mask).toNat := by
        exact Nat.lt_of_not_ge hle
      have hrev :=
        Benchmarks.Dss.Clipper.Reasoning.Reach.RD.clipperStatusAgeForPriceRevert
          (v := v) (hpatch := hpatch) rd8460
          (by simpa [tic, packed, id] using hlt)
          (by simp only [List.length_cons, List.length_nil]; omega)
      have hltStele :
          (clipperTimestampWord evmStele).toNat <
            (clipperGetStatusTicWord evmStele I).toNat := by
        simpa [-Std.ExtTreeMap.get?_eq_getElem?, evmStele, initState, clipperGetStatusTicWord, clipperTimestampWord,
          Stele.EVM.storageLoad, State.lookupAccount, Account.lookupStorage,
          solcSlotWord, clipperGetStatusSalesPackedSlot, hbaseSlot,
          tic, packed, hticClean, hticCleanStele] using hlt
      have hbody :=
        clipperGetStatusBodyRevertsAgeForPrice (fork := fork) v evmStele I
          (by simpa [-Std.ExtTreeMap.get?_eq_getElem?, evmStele, initState] using hwv)
          hltStele
      exact hrev.reEquivExecutionRevert hcode hdispatch hdec hbody
  · exact clipperGetStatusBodyCoreDecodeFailed_short (v := v) hpatch hcode hsize hsz4
      (by omega) hdispatch hreach

end Benchmarks.Dss.Clipper
