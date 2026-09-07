import Benchmarks.Dss.Clipper.Fallback

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Benchmarks.Dss.Clipper.Immutables

namespace Benchmarks.Dss.Clipper

set_option linter.unusedTactic false

/-! ## ABI decode and source-level body for `wards(address)` -/

/-- The raw ABI word for `wards`'s `arg0` argument. -/
abbrev clipperWardsArgWord (I : ExecutionEnv) : UInt256 :=
  calldataWord I.calldata 4

abbrev clipperWardsArgMaskedWord (I : ExecutionEnv) : UInt256 :=
  UInt256.land solcAddrMask (clipperWardsArgWord I)

abbrev clipperWardsArgValue (I : ExecutionEnv) : Value :=
  .address (AccountAddress.ofNat (clipperWardsArgWord I).toNat)

abbrev clipperWardsArgKey (I : ExecutionEnv) : KeyValue :=
  .address (AccountAddress.ofNat (clipperWardsArgWord I).toNat)

abbrev clipperWardsStore (I : ExecutionEnv) : Store :=
  (∅ : Store).insert "arg0" (clipperWardsArgValue I)

def clipperWardsStorageSlot (I : ExecutionEnv) : UInt256 :=
  wardsSlot (clipperWardsArgKey I)

def clipperWardsWord (σ : AccountMap) (I : ExecutionEnv) : UInt256 :=
  σ.find? I.codeOwner |>.option ⟨0⟩
    (fun acc => acc.storage.findD (clipperWardsStorageSlot I) ⟨0⟩)

theorem clipperWardsStorageSlot_eq_mapSlot_masked (I : ExecutionEnv) :
    clipperWardsStorageSlot I = mapSlot (clipperWardsArgMaskedWord I) ⟨0⟩ := by
  unfold clipperWardsStorageSlot wardsSlot clipperWardsArgKey clipperWardsArgMaskedWord
  rw [keyValueToWord_address_ofNat_mask]

theorem clipperWardsSelectorWord {I : ExecutionEnv} (hsz : 4 ≤ I.calldata.size)
    (hsel : selIs I (clipperSelBytes 27)) :
    clipperSelWord I = clipperSelNat 27 := by
  simpa [clipperSelWord, solcSelectorWord, clipperSelNat] using
    solcSelectorWord_eq_of_beq I hsz 0xbf 0x35 0x3d 0xbb (clipperSelNat 27)
      (by native_decide) (by simpa [clipperSelBytes, selIs] using hsel)

theorem clipperDispatch_wards (v : ClipperImmutables) {I : ExecutionEnv}
    (hsel : selIs I (clipperSelBytes 27)) :
    dispatchMsg (contract v) I.calldata = some wardsTransition := by
  refine dispatchMsg_eq_some_of_split (contract := contract v)
    (pre :=
      [activeTransition, bufTransition, calcTransition, chipTransition, chostTransition,
        countTransition, cuspTransition, denyTransition, dogTransition, fileUintTransition,
        fileAddressTransition, getStatusTransition, ilkTransition v, kickTransition v,
        kicksTransition, listTransition, redoTransition v, relyTransition, salesTransition,
        spotterTransition, stoppedTransition, tailTransition, takeTransition v, tipTransition,
        upchostTransition v, vatTransition v, vowTransition])
    (post := [yankTransition v])
    (ti := wardsTransition) (cd := I.calldata) (by rfl) ?_ ?_ ?_ (by rfl)
  · rfl
  · intro t ht
    simp only [List.mem_cons, List.mem_nil_iff] at ht
    rcases ht with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      | rfl | rfl | rfl | rfl | hfalse
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
    · rw [selectorOf, getStatusSelectorBytes, ← byteArray_eq_of_beq hsel]
      native_decide
    · rw [selectorOf, ilkSelectorBytes v, ← byteArray_eq_of_beq hsel]
      native_decide
    · rw [selectorOf, kickSelectorBytes v, ← byteArray_eq_of_beq hsel]
      native_decide
    · rw [selectorOf, kicksSelectorBytes, ← byteArray_eq_of_beq hsel]
      native_decide
    · rw [selectorOf, listSelectorBytes, ← byteArray_eq_of_beq hsel]
      native_decide
    · rw [selectorOf, redoSelectorBytes v, ← byteArray_eq_of_beq hsel]
      native_decide
    · rw [selectorOf, relySelectorBytes, ← byteArray_eq_of_beq hsel]
      native_decide
    · rw [selectorOf, salesSelectorBytes, ← byteArray_eq_of_beq hsel]
      native_decide
    · rw [selectorOf, spotterSelectorBytes, ← byteArray_eq_of_beq hsel]
      native_decide
    · rw [selectorOf, stoppedSelectorBytes, ← byteArray_eq_of_beq hsel]
      native_decide
    · rw [selectorOf, tailSelectorBytes, ← byteArray_eq_of_beq hsel]
      native_decide
    · rw [selectorOf, takeSelectorBytes v, ← byteArray_eq_of_beq hsel]
      native_decide
    · rw [selectorOf, tipSelectorBytes, ← byteArray_eq_of_beq hsel]
      native_decide
    · rw [selectorOf, upchostSelectorBytes v, ← byteArray_eq_of_beq hsel]
      native_decide
    · rw [selectorOf, vatSelectorBytes v, ← byteArray_eq_of_beq hsel]
      native_decide
    · rw [selectorOf, vowSelectorBytes, ← byteArray_eq_of_beq hsel]
      native_decide
    · cases hfalse
  · rw [selectorOf, wardsSelectorBytes]
    simpa [clipperSelBytes] using hsel

theorem clipperDecode_wards_ok (v : ClipperImmutables) {I : ExecutionEnv}
    (hsz36 : 36 ≤ I.calldata.size) :
    decodeCalldataWithMode (config v).abiDecodeMode (wardsTransition.params.map Param.name)
      (transitionSignature wardsTransition).paramTypes I.calldata =
        some (clipperWardsStore I) := by
  show decodeCalldataWithMode (config v).abiDecodeMode ["arg0"] [addr] I.calldata = _
  simpa [config, clipperWardsStore, clipperWardsArgValue, clipperWardsArgWord,
    calldataWord] using
      decodeCalldata_legacyAddress_ok (cd := I.calldata) (x := "arg0") hsz36

theorem clipperDecode_wards_none_short (v : ClipperImmutables) {I : ExecutionEnv}
    (hsz4 : 4 ≤ I.calldata.size) (hshort : I.calldata.size < 36) :
    decodeCalldataWithMode (config v).abiDecodeMode (wardsTransition.params.map Param.name)
      (transitionSignature wardsTransition).paramTypes I.calldata = none := by
  show decodeCalldataWithMode (config v).abiDecodeMode ["arg0"] [addr] I.calldata = none
  simpa [config] using
    decodeCalldata_legacyAddress_none_short (cd := I.calldata) (x := "arg0") hsz4 hshort

/-- The Solm `wards(address)` body returns `wards[arg0]`. -/
theorem clipperWardsBodyReturns (v : ClipperImmutables) (evm : EVM.State)
    (I : ExecutionEnv) (h : evm.executionEnv.weiValue = ⟨0⟩) :
    ExecTransitionBody (config v) (contract v) evm (clipperWardsStore I)
      wardsTransition.body
      (.returned { contract := contract v, locals := clipperWardsStore I } evm
        (some [(.int (Int.ofNat
          (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner
            (clipperWardsStorageSlot I)).toNat))])) := by
  exact ExecFuncBody.execBlockRet <|
    (ABlock.start.requireStep (evalCallvalueEq_true h)).returns (by
      rw [evalExpr_storage_scalar_value
        (cfg := config v)
        (solm := { contract := contract v, locals := clipperWardsStore I })
        (slot := wardsRef (.var "arg0"))
        (er := ({ base := "wards", steps := [.mindex (clipperWardsArgKey I)] } :
          EvaledStorageRef))
        (t := .int uint256Int)
        (loc := wordLoc (clipperWardsStorageSlot I))
        (value := .int (Int.ofNat
          (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner
            (clipperWardsStorageSlot I)).toNat))
        (hbase := by
          simp [clipperWardsStore, wardsRef])
        (her := by
          simp [evalStorageRef, evalStorageRefStep, wardsRef, clipperWardsStore,
            clipperWardsArgValue, clipperWardsArgKey, valueToKey?, EvalResult.bind,
            EvalResult.ofOption, bind, pure, evalExpr?])
        (hty := by
          simp [storageTypeAt?, storageTypeStep?, contract, storageDecls,
            clipperWardsArgKey, uint256St])
        (hloc := by rfl)
        (hload := by
          simpa [wordLoc, uint256Loc] using
            clipperStorageLocLoad_uint256 evm (clipperWardsStorageSlot I))])

/-! ## EVM trace -/

set_option maxHeartbeats 1000000 in
theorem clipperReachWardsBody {cA gh bl σ σ₀ A I} {g : Sat256} (v : ClipperImmutables)
    {code : ByteArray} (hpatch : patchRuntime clipperBytecode (patches v) = some code)
    (hcode : I.code = code) (hwv : I.weiValue = ⟨0⟩)
    (hsz : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hsel : selIs I (clipperSelBytes 27)) :
    ∃ k C, RD code I g (initState cA gh bl σ σ₀ g A I) (⟨1303⟩ : UInt256)
      [clipperSelWord I] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
  obtain ⟨_, _, h32⟩ := clipperReachRoot (cA := cA) (gh := gh) (bl := bl)
    (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := g) v hpatch hcode hwv hsz hsize
  have hword := clipperWardsSelectorWord hsz hsel
  have h43 := clipperSplitNotTaken (pc := (⟨32⟩ : UInt256))
    (next := (⟨43⟩ : UInt256)) (pivot := clipperSelNat 20)
    (tgt := (⟨260⟩ : UInt256)) h32
    (by
        change decode code (⟨32⟩ : UInt256) = some (.DUP1, .none)
        clipper_decode)
    (by
        change decode code (selArmPush4Pc (⟨32⟩ : UInt256)) =
          some (.Push .PUSH4, some (clipperSelNat 20, 4))
        clipper_decode)
    (by
        change decode code (selArmEqPc (⟨32⟩ : UInt256)) = some (.GT, .none)
        clipper_decode)
    (by decide)
    (by
        change decode code (selArmPushTgtPc (⟨32⟩ : UInt256)) =
          some (.Push .PUSH2, some (⟨260⟩, 2))
        clipper_decode)
    (by
        change decode code (selArmJumpiPc (⟨32⟩ : UInt256) 2) = some (.JUMPI, .none)
        clipper_decode)
    (by rw [hword]; native_decide)
    (by native_decide)
    (by simp)
  have h54 := clipperSplitNotTaken (pc := (⟨43⟩ : UInt256))
    (next := (⟨54⟩ : UInt256)) (pivot := clipperSelNat 3)
    (tgt := (⟨162⟩ : UInt256)) h43
    (by
        change decode code (⟨43⟩ : UInt256) = some (.DUP1, .none)
        clipper_decode)
    (by
        change decode code (selArmPush4Pc (⟨43⟩ : UInt256)) =
          some (.Push .PUSH4, some (clipperSelNat 3, 4))
        clipper_decode)
    (by
        change decode code (selArmEqPc (⟨43⟩ : UInt256)) = some (.GT, .none)
        clipper_decode)
    (by decide)
    (by
        change decode code (selArmPushTgtPc (⟨43⟩ : UInt256)) =
          some (.Push .PUSH2, some (⟨162⟩, 2))
        clipper_decode)
    (by
        change decode code (selArmJumpiPc (⟨43⟩ : UInt256) 2) = some (.JUMPI, .none)
        clipper_decode)
    (by rw [hword]; native_decide)
    (by native_decide)
    (by simp)
  have h113 := clipperSplitTaken (pc := (⟨54⟩ : UInt256)) (pivot := clipperSelNat 12)
    (tgt := (⟨113⟩ : UInt256)) h54
    (by
        change decode code (⟨54⟩ : UInt256) = some (.DUP1, .none)
        clipper_decode)
    (by
        change decode code (selArmPush4Pc (⟨54⟩ : UInt256)) =
          some (.Push .PUSH4, some (clipperSelNat 12, 4))
        clipper_decode)
    (by
        change decode code (selArmEqPc (⟨54⟩ : UInt256)) = some (.GT, .none)
        clipper_decode)
    (by decide)
    (by
        change decode code (selArmPushTgtPc (⟨54⟩ : UInt256)) =
          some (.Push .PUSH2, some (⟨113⟩, 2))
        clipper_decode)
    (by
        change decode code (selArmJumpiPc (⟨54⟩ : UInt256) 2) = some (.JUMPI, .none)
        clipper_decode)
    (by rw [hword]; native_decide)
    (clipperJumpDestBeforeFirstPatch v hpatch (⟨113⟩ : UInt256) (by native_decide))
    (by simp)
  have h125 := clipperArmNotTaken (pc := (⟨114⟩ : UInt256))
    (next := (⟨125⟩ : UInt256)) (sel := clipperSelNat 3)
    (tgt := (⟨1258⟩ : UInt256))
    (h113.jumpdest
      (by
          change decode code (⟨113⟩ : UInt256) = some (.JUMPDEST, .none)
          clipper_decode)
      (by simp))
    (by
        change decode code (⟨114⟩ : UInt256) = some (.DUP1, .none)
        clipper_decode)
    (by
        change decode code (selArmPush4Pc (⟨114⟩ : UInt256)) =
          some (.Push .PUSH4, some (clipperSelNat 3, 4))
        clipper_decode)
    (by
        change decode code (selArmEqPc (⟨114⟩ : UInt256)) = some (.EQ, .none)
        clipper_decode)
    (by decide)
    (by
        change decode code (selArmPushTgtPc (⟨114⟩ : UInt256)) =
          some (.Push .PUSH2, some (⟨1258⟩, 2))
        clipper_decode)
    (by
        change decode code (selArmJumpiPc (⟨114⟩ : UInt256) 2) = some (.JUMPI, .none)
        clipper_decode)
    (by rw [hword]; native_decide)
    (by native_decide)
    (by simp)
  have h136 := clipperArmNotTaken (pc := (⟨125⟩ : UInt256))
    (next := (⟨136⟩ : UInt256)) (sel := clipperSelNat 4)
    (tgt := (⟨1295⟩ : UInt256)) h125
    (by
        change decode code (⟨125⟩ : UInt256) = some (.DUP1, .none)
        clipper_decode)
    (by
        change decode code (selArmPush4Pc (⟨125⟩ : UInt256)) =
          some (.Push .PUSH4, some (clipperSelNat 4, 4))
        clipper_decode)
    (by
        change decode code (selArmEqPc (⟨125⟩ : UInt256)) = some (.EQ, .none)
        clipper_decode)
    (by decide)
    (by
        change decode code (selArmPushTgtPc (⟨125⟩ : UInt256)) =
          some (.Push .PUSH2, some (⟨1295⟩, 2))
        clipper_decode)
    (by
        change decode code (selArmJumpiPc (⟨125⟩ : UInt256) 2) = some (.JUMPI, .none)
        clipper_decode)
    (by rw [hword]; native_decide)
    (by native_decide)
    (by simp)
  have h1303 := clipperArmTaken (pc := (⟨136⟩ : UInt256)) (sel := clipperSelNat 27)
    (tgt := (⟨1303⟩ : UInt256)) h136
    (by
        change decode code (⟨136⟩ : UInt256) = some (.DUP1, .none)
        clipper_decode)
    (by
        change decode code (selArmPush4Pc (⟨136⟩ : UInt256)) =
          some (.Push .PUSH4, some (clipperSelNat 27, 4))
        clipper_decode)
    (by
        change decode code (selArmEqPc (⟨136⟩ : UInt256)) = some (.EQ, .none)
        clipper_decode)
    (by decide)
    (by
        change decode code (selArmPushTgtPc (⟨136⟩ : UInt256)) =
          some (.Push .PUSH2, some (⟨1303⟩, 2))
        clipper_decode)
    (by
        change decode code (selArmJumpiPc (⟨136⟩ : UInt256) 2) = some (.JUMPI, .none)
        clipper_decode)
    (by rw [hword]; native_decide)
    (clipperJumpDestBeforeFirstPatch v hpatch (⟨1303⟩ : UInt256) (by native_decide))
    (by simp)
  exact ⟨_, _, h1303⟩

theorem clipperWardsExternalEntryWf (v : ClipperImmutables) {code : ByteArray}
    (hpatch : patchRuntime clipperBytecode (patches v) = some code) :
    solcOneAddressExternalEntryWf code (⟨1303⟩ : UInt256)
      (⟨476⟩ : UInt256) (⟨6765⟩ : UInt256) := by
  unfold solcOneAddressExternalEntryWf solcOneAddressExternalDecodedPc
  repeat' first | apply And.intro
  all_goals
    rw [clipperDecodeBeforeFirstPatch v hpatch _ (by native_decide)]
    native_decide

theorem clipperWardsPatchesWindowDisjoint32 (v : ClipperImmutables) (lo hi : Nat)
    (hwin : (lo, hi) ∈
      [(6765, 6766), (6766, 6766), (6766, 6767), (6767, 6768),
        (6768, 6769), (6769, 6770), (6770, 6771), (6771, 6771),
        (6771, 6772), (6772, 6772), (6772, 6773), (6773, 6773),
        (6773, 6774), (6774, 6774), (6774, 6775), (6775, 6775),
        (6775, 6776), (6776, 6776), (6776, 6777), (6777, 6778),
        (6778, 6779), (6779, 6779), (6779, 6780), (6780, 6780),
        (6780, 6781), (6781, 6781), (6781, 6782), (6782, 6782),
        (6782, 6783), (6783, 6783)]) :
    PatchesWindowDisjoint32 lo hi (patches v) := by
  unfold PatchesWindowDisjoint32 PatchWindowDisjoint32 patches patchesFrom offsets immValues
  simp only [List.foldrM_cons, List.foldrM_nil, List.lookup_cons]
  cases hIlk : wordBytes? v.ilk with
  | none =>
      simp [hIlk] at hwin ⊢
      try omega
  | some bs =>
      simp [hIlk] at hwin ⊢
      try omega

theorem clipperWardsSlotGetterWf (v : ClipperImmutables) {code : ByteArray}
    (hpatch : patchRuntime clipperBytecode (patches v) = some code) :
    solcZeroSlotSingleMappingGetterWf code (⟨6765⟩ : UInt256) := by
  unfold solcZeroSlotSingleMappingGetterWf
  repeat' first | apply And.intro
  all_goals
    exact patchRuntime_decode_disjoint_of_decode_res hpatch
      (by apply clipperWardsPatchesWindowDisjoint32 v; native_decide)
      (by apply clipperWardsPatchesWindowDisjoint32 v; native_decide)
      (by native_decide)
      (by native_decide)
      (by native_decide)

theorem clipperJumpDest6765 (v : ClipperImmutables) {code : ByteArray}
    (hpatch : patchRuntime clipperBytecode (patches v) = some code) :
    (D_J code 0).contains (⟨6765⟩ : UInt256) = true := by
  apply patchRuntime_D_J_contains_of_patchScanReaches (fuel := 7000) hpatch
  unfold patches patchesFrom offsets immValues
  simp only [List.foldrM_cons, List.foldrM_nil, List.lookup_cons]
  cases hIlk : wordBytes? v.ilk with
  | none =>
      simp [hIlk]
      native_decide
  | some bs =>
      simp [hIlk]
      native_decide

theorem clipperWardsX_decoded {cA gh bl σ σ₀ A I} {g : Sat256} {sel : UInt256}
    (v : ClipperImmutables) {code : ByteArray}
    (hpatch : patchRuntime clipperBytecode (patches v) = some code)
    (hsz36 : 36 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hreach : ∃ k C, RD code I g
      (initState cA gh bl σ σ₀ g A I) (⟨1303⟩ : UInt256) [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    ∃ k C, RD code I g (initState cA gh bl σ σ₀ g A I) (⟨6765⟩ : UInt256)
        [clipperWardsArgMaskedWord I, ⟨476⟩, sel]
        solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
  obtain ⟨_, _, rd1325⟩ := solcOneAddressExternalLenOk
    (entry := (⟨1303⟩ : UInt256)) (ret := (⟨476⟩ : UInt256))
    (routine := (⟨6765⟩ : UInt256)) hreach
    (clipperWardsExternalEntryWf v hpatch)
    (by
      simpa [solcOneAddressExternalDecodedPc] using
        clipperJumpDestBeforeFirstPatch v hpatch (⟨1325⟩ : UInt256) (by native_decide))
    hsz36 hsize
  obtain ⟨_, _, rd6765⟩ := solcOneAddressExternalMaskAndJumpMasked
    (entry := (⟨1303⟩ : UInt256)) (ret := (⟨476⟩ : UInt256))
    (routine := (⟨6765⟩ : UInt256)) (R := [sel])
    rd1325 (clipperWardsExternalEntryWf v hpatch) (clipperJumpDest6765 v hpatch)
    (by simp only [List.length_singleton]; omega)
  exact ⟨_, _, by simpa [clipperWardsArgMaskedWord, clipperWardsArgWord] using rd6765⟩

theorem clipperWardsX_shortarg {cA gh bl σ σ₀ A I} {g : Sat256} {sel : UInt256}
    (v : ClipperImmutables) {code : ByteArray}
    (hpatch : patchRuntime clipperBytecode (patches v) = some code)
    (hsz4 : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hshort : I.calldata.size < 36)
    (hreach : ∃ k C, RD code I g
      (initState cA gh bl σ σ₀ g A I) (⟨1303⟩ : UInt256) [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    RDrev code g (initState cA gh bl σ σ₀ g A I) := by
  exact solcOneAddressExternalShort
    (entry := (⟨1303⟩ : UInt256)) (ret := (⟨476⟩ : UInt256))
    (routine := (⟨6765⟩ : UInt256)) hreach
    (clipperWardsExternalEntryWf v hpatch) hsz4 hsize hshort

theorem clipperX_wards_ok {cA gh bl σ σ₀ A I} {g : Sat256} {sel : UInt256}
    (v : ClipperImmutables) {code : ByteArray}
    (hpatch : patchRuntime clipperBytecode (patches v) = some code)
    (hsz36 : 36 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hreach : ∃ k C, RD code I g
      (initState cA gh bl σ σ₀ g A I) (⟨1303⟩ : UInt256) [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    RDret code g (initState cA gh bl σ σ₀ g A I) (cA, σ)
      (UInt256.toByteArray (clipperWardsWord σ I)) := by
  obtain ⟨_, _, rd6765⟩ := clipperWardsX_decoded (v := v) hpatch hsz36 hsize hreach
  obtain ⟨k476, C476, rd476raw⟩ := solcZeroSlotSingleMappingGetter (pc := ⟨6765⟩)
    (key := clipperWardsArgMaskedWord I) (ret := ⟨476⟩) (R := [sel])
    rd6765 (clipperWardsSlotGetterWf v hpatch)
    (clipperJumpDestBeforeFirstPatch v hpatch (⟨476⟩ : UInt256) (by native_decide))
    (by simp only [List.length_singleton]; omega)
  have hword :
      solcSlotWord σ I (solcMappingSlot ⟨0⟩ (clipperWardsArgMaskedWord I)) =
        clipperWardsWord σ I := by
    simp [clipperWardsWord, solcSlotWord, clipperWardsStorageSlot_eq_mapSlot_masked,
      mapSlot, solcMappingSlot]
  have rd476 : RD code I g (initState cA gh bl σ σ₀ g A I) (⟨476⟩ : UInt256)
      (clipperWardsWord σ I :: ⟨476⟩ :: [sel])
      (solcMappingHashMem ⟨0⟩ (clipperWardsArgMaskedWord I))
      (UInt256.ofNat 3) ByteArray.empty (cA, σ) k476 C476 := by
    simpa [hword] using rd476raw
  exact RD.solcReturnWordFromMem
    (val := clipperWardsWord σ I) (ret := ⟨476⟩) (R := [sel])
    (mem := solcMappingHashMem ⟨0⟩ (clipperWardsArgMaskedWord I))
    (memout := solcScratchReturnMem
      (solcMappingHashMem ⟨0⟩ (clipperWardsArgMaskedWord I)) (clipperWardsWord σ I))
    rd476
    (clipperReturnWord476Wf v hpatch)
    (solcMappingHashMem_mload64 ⟨0⟩ (clipperWardsArgMaskedWord I))
    (by rfl)
    (solcScratchReturnMem_mload64 (clipperWardsWord σ I)
      (solcMappingHashMem_size ⟨0⟩ (clipperWardsArgMaskedWord I))
      (solcMappingHashMem_read64 ⟨0⟩ (clipperWardsArgMaskedWord I)))
    (solcScratchReturnMem_read128 (clipperWardsWord σ I)
      (solcMappingHashMem_size ⟨0⟩ (clipperWardsArgMaskedWord I)))
    (by simp only [List.length_singleton]; omega)

theorem clipperWardsBodyCoreOk
    {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256} {sel : UInt256}
    (v : ClipperImmutables) {code : ByteArray}
    (hpatch : patchRuntime clipperBytecode (patches v) = some code)
    (hcode : I.code = code) (hsize : I.calldata.size < UInt256.size)
    (hwv : I.weiValue = ⟨0⟩)
    (hsz36 : 36 ≤ I.calldata.size)
    (hdispatch : dispatchMsg (contract v) I.calldata = some wardsTransition)
    (hdecode :
      decodeCalldataWithMode (config v).abiDecodeMode (wardsTransition.params.map Param.name)
        (transitionSignature wardsTransition).paramTypes I.calldata =
          some (clipperWardsStore I))
    (hreach : ∃ k C, RD code I (Sat256.ofUInt256 g)
      (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) (⟨1303⟩ : UInt256)
      [sel] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ_evm) k C)
    (hAccounts : accountMapEquiv σ_evm σ_solm) :
    runtimeEquivalenceFor (config v) (contract v) cA gh bl σ_evm σ_solm σ₀ g A I := by
  have hword : clipperWardsWord σ_evm I = clipperWardsWord σ_solm I :=
    accountMapEquiv_storage_findD hAccounts I.codeOwner (clipperWardsStorageSlot I) ⟨0⟩
  have hbody :
      ExecTransitionBody (config v) (contract v)
        (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)
        (clipperWardsStore I)
        wardsTransition.body
        (.returned { contract := contract v, locals := clipperWardsStore I }
          (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)
          (some [(.int (Int.ofNat (clipperWardsWord σ_solm I).toNat))])) := by
    simpa [clipperWardsWord, initState, Solm.EVM.storageLoad, State.lookupAccount] using
      clipperWardsBodyReturns v
        (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I) I
        (by simp only [initState]; exact hwv)
  exact (clipperX_wards_ok (v := v) (g := Sat256.ofUInt256 g) hpatch hsz36 hsize hreach)
    |>.reEquivExecutionTransport hcode hdispatch hdecode hbody (by rw [← hword])
      hAccounts
      (returnEquiv_of_encode
        (by simpa [uint256] using uint256ReturnEncoding (clipperWardsWord σ_evm I)))

theorem clipperWardsBodyCoreDecodeFailed_short
    {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256} {sel : UInt256}
    (v : ClipperImmutables) {code : ByteArray}
    (hpatch : patchRuntime clipperBytecode (patches v) = some code)
    (hcode : I.code = code) (hsize : I.calldata.size < UInt256.size)
    (hsz4 : 4 ≤ I.calldata.size) (hshort : I.calldata.size < 36)
    (hdispatch : dispatchMsg (contract v) I.calldata = some wardsTransition)
    (hreach : ∃ k C, RD code I (Sat256.ofUInt256 g)
      (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) (⟨1303⟩ : UInt256)
      [sel] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ_evm) k C) :
    runtimeEquivalenceFor (config v) (contract v) cA gh bl σ_evm σ_solm σ₀ g A I := by
  have hdec := clipperDecode_wards_none_short v (I := I) hsz4 hshort
  exact (clipperWardsX_shortarg (v := v) (g := Sat256.ofUInt256 g) hpatch hsz4
    hsize hshort hreach)
    |>.reEquivDecodingFailed hcode hdispatch hdec

/-- `wards(address)` body refines its Solm transition. -/
theorem clipperWardsBody (v : ClipperImmutables) {code : ByteArray}
    (hpatch : patchRuntime clipperBytecode (patches v) = some code)
    {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256}
    (hcode : I.code = code) (hsize : I.calldata.size < UInt256.size)
    (_hperm : I.perm = true) (hwv : I.weiValue = ⟨0⟩)
    (hsel : selIs I (clipperSelBytes 27))
    (hAccounts : accountMapEquiv σ_evm σ_solm) :
    runtimeEquivalenceFor (config v) (contract v) cA gh bl σ_evm σ_solm σ₀ g A I := by
  have hsz4 : 4 ≤ I.calldata.size :=
    calldata_size_ge_of_selIs I (clipperSelBytes 27) (by native_decide) hsel
  have hdispatch : dispatchMsg (contract v) I.calldata = some wardsTransition :=
    clipperDispatch_wards v hsel
  have hreach := clipperReachWardsBody (cA := cA) (gh := gh) (bl := bl)
    (σ := σ_evm) (σ₀ := σ₀) (A := A) (I := I) (g := Sat256.ofUInt256 g)
    (v := v) hpatch hcode hwv hsz4 hsize hsel
  by_cases hsz36 : 36 ≤ I.calldata.size
  · exact clipperWardsBodyCoreOk (v := v) hpatch hcode hsize hwv hsz36 hdispatch
      (clipperDecode_wards_ok v hsz36) hreach hAccounts
  · exact clipperWardsBodyCoreDecodeFailed_short (v := v) hpatch hcode hsize hsz4
      (by omega) hdispatch hreach

end Benchmarks.Dss.Clipper
