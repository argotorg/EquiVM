import Benchmarks.Dss.Clipper.UintEntry
import Benchmarks.Dss.Clipper.Invalid
import Ethereum.Theory.OpcodeLemmas

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Benchmarks.Dss.Clipper.Immutables

namespace Benchmarks.Dss.Clipper

set_option linter.unusedTactic false

/-! ## ABI decode and source-level body for `active(uint256)` -/

abbrev clipperActiveArgWord (I : ExecutionEnv) : UInt256 :=
  calldataWord I.calldata 4

abbrev clipperActiveArgValue (I : ExecutionEnv) : Value :=
  .int (Int.ofNat (clipperActiveArgWord I).toNat)

abbrev clipperActiveArgKey (I : ExecutionEnv) : KeyValue :=
  .int (Int.ofNat (clipperActiveArgWord I).toNat)

abbrev clipperActiveStore (I : ExecutionEnv) : Store :=
  (∅ : Store).insert "arg0" (clipperActiveArgValue I)

abbrev clipperActiveSlot (I : ExecutionEnv) : UInt256 :=
  activeSlot (clipperActiveArgKey I)

def clipperActiveWord (σ : AccountMap) (I : ExecutionEnv) : UInt256 :=
  σ.find? I.codeOwner |>.option ⟨0⟩
    (fun acc => acc.storage.findD (clipperActiveSlot I) ⟨0⟩)

theorem clipperActiveSlot_eq (I : ExecutionEnv) :
    clipperActiveSlot I = activeDataSlot + clipperActiveArgWord I := by
  unfold clipperActiveSlot activeSlot clipperActiveArgKey
  rw [keyValueToWord_uint256]

theorem clipperActiveSelectorWord {I : ExecutionEnv} (hsz : 4 ≤ I.calldata.size)
    (hsel : selIs I (clipperSelBytes 0)) :
    clipperSelWord I = clipperSelNat 0 := by
  simpa [clipperSelWord, solcSelectorWord, clipperSelNat] using
    solcSelectorWord_eq_of_beq I hsz 0x80 0x33 0xd5 0x81 (clipperSelNat 0)
      (by native_decide) (by simpa [clipperSelBytes, selIs] using hsel)

theorem clipperDispatch_active (v : ClipperImmutables) {I : ExecutionEnv}
    (hsel : selIs I (clipperSelBytes 0)) :
    dispatchMsg (contract v) I.calldata = some activeTransition := by
  refine dispatchMsg_eq_some_of_split (contract := contract v)
    (pre := [])
    (post :=
      [bufTransition, calcTransition, chipTransition, chostTransition, countTransition,
        cuspTransition, denyTransition, dogTransition, fileUintTransition, fileAddressTransition,
        getStatusTransition, ilkTransition v, kickTransition v, kicksTransition, listTransition,
        redoTransition v, relyTransition, salesTransition, spotterTransition, stoppedTransition,
        tailTransition, takeTransition v, tipTransition, upchostTransition v, vatTransition v,
        vowTransition, wardsTransition, yankTransition v])
    (ti := activeTransition) (cd := I.calldata) (by rfl) ?_ ?_ ?_ (by rfl)
  · rfl
  · intro t ht
    cases ht
  · rw [selectorOf, activeSelectorBytes]
    simpa [clipperSelBytes] using hsel

theorem clipperDecode_active_ok (v : ClipperImmutables) {I : ExecutionEnv}
    (hsz36 : 36 ≤ I.calldata.size) :
    decodeCalldataWithMode (config v).abiDecodeMode (activeTransition.params.map Param.name)
      (transitionSignature activeTransition).paramTypes I.calldata =
        some (clipperActiveStore I) := by
  show decodeCalldataWithMode (config v).abiDecodeMode ["arg0"] [uint256] I.calldata = _
  simpa [config, clipperActiveStore, clipperActiveArgValue, clipperActiveArgWord] using
    decodeCalldataWithMode_legacyUint256_ok (cd := I.calldata) (x := "arg0") hsz36

theorem clipperDecode_active_none_short (v : ClipperImmutables) {I : ExecutionEnv}
    (hsz4 : 4 ≤ I.calldata.size) (hshort : I.calldata.size < 36) :
    decodeCalldataWithMode (config v).abiDecodeMode (activeTransition.params.map Param.name)
      (transitionSignature activeTransition).paramTypes I.calldata = none := by
  show decodeCalldataWithMode (config v).abiDecodeMode ["arg0"] [uint256] I.calldata = none
  simpa [config] using
    decodeCalldataWithMode_legacyUint256_none_short (cd := I.calldata) (x := "arg0")
      hsz4 hshort

theorem clipperEvalActiveElem_ok (v : ClipperImmutables) (evm : EVM.State)
    (I : ExecutionEnv)
    (hbound :
      (clipperActiveArgWord I).toNat <
        (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨11⟩).toNat) :
    evalExpr? (config v) { contract := contract v, locals := clipperActiveStore I } evm
      (.storage (activeElemRef (.var "arg0"))) =
      .ok (.int (Int.ofNat
        (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner (clipperActiveSlot I)).toNat)) := by
  have hbounds :
      0 ≤ Int.ofNat (clipperActiveArgWord I).toNat ∧
        Int.ofNat (clipperActiveArgWord I).toNat <
          Int.ofNat (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨11⟩).toNat := by
    constructor
    · exact Int.natCast_nonneg _
    · exact Int.ofNat_lt.mpr hbound
  rw [evalExpr_storage_scalar_value
    (cfg := config v)
    (solm := { contract := contract v, locals := clipperActiveStore I })
    (slot := activeElemRef (.var "arg0"))
    (er := ({ base := "active", steps := [.aindex (clipperActiveArgKey I)] } :
      EvaledStorageRef))
    (t := .int uint256Int)
    (loc := wordLoc (clipperActiveSlot I))
    (value := .int (Int.ofNat
      (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner (clipperActiveSlot I)).toNat))
    (hbase := by
      simp [clipperActiveStore, activeElemRef])
    (her := by
      simp [evalStorageRef, evalStorageRefStep, activeElemRef, clipperActiveStore,
        clipperActiveArgValue, clipperActiveArgKey, valueToKey?, EvalResult.bind,
        EvalResult.ofOption, bind, pure, evalExpr?, config, storageLayout, solidityStorageLayout,
        storageLayoutRaw, storageTypeAt?, contract, storageDecls, clipperStorageLocLoad_uint256,
        hbound])
    (hty := by
      simp [storageTypeAt?, storageTypeStep?, contract, storageDecls, clipperActiveArgKey,
        uint256St])
    (hloc := by rfl)
    (hload := by
      simpa [wordLoc, uint256Loc] using
        clipperStorageLocLoad_uint256 evm (clipperActiveSlot I))]

theorem clipperEvalActiveElem_revert (v : ClipperImmutables) (evm : EVM.State)
    (I : ExecutionEnv)
    (hbound :
      (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨11⟩).toNat ≤
        (clipperActiveArgWord I).toNat) :
    evalExpr? (config v) { contract := contract v, locals := clipperActiveStore I } evm
      (.storage (activeElemRef (.var "arg0"))) = .revert := by
  have hbounds :
      ¬ (0 ≤ Int.ofNat (clipperActiveArgWord I).toNat ∧
        Int.ofNat (clipperActiveArgWord I).toNat <
          Int.ofNat (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨11⟩).toNat) := by
    intro h
    have hlt : (clipperActiveArgWord I).toNat <
        (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨11⟩).toNat := by
      exact Int.ofNat_lt.mp h.2
    exact Nat.not_lt_of_ge hbound hlt
  have hnot :
      ¬ (clipperActiveArgWord I).toNat <
        (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨11⟩).toNat :=
    Nat.not_lt_of_ge hbound
  simp [evalExpr?, resolveStorageRef?, evalStorageRef, evalStorageRefStep, activeElemRef,
    clipperActiveStore, clipperActiveArgValue, valueToKey?,
    EvalResult.bind, EvalResult.ofOption, bind, pure, config, storageLayout, solidityStorageLayout,
    storageLayoutRaw, storageTypeAt?, contract, storageDecls, clipperStorageLocLoad_uint256,
    hnot]

theorem clipperActiveBodyReturns (v : ClipperImmutables) (evm : EVM.State)
    (I : ExecutionEnv) (h : evm.executionEnv.weiValue = ⟨0⟩)
    (hbound :
      (clipperActiveArgWord I).toNat <
        (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨11⟩).toNat) :
    ExecTransitionBody (config v) (contract v) evm (clipperActiveStore I)
      activeTransition.body
      (.returned { contract := contract v, locals := clipperActiveStore I } evm
        (some [(.int (Int.ofNat
          (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner
            (clipperActiveSlot I)).toNat))])) := by
  simpa [activeTransition] using
    nonpayableReturnExprBodyReturns (cfg := config v) (contract := contract v) h
      (clipperEvalActiveElem_ok v evm I hbound)

theorem clipperActiveBodyReverts (v : ClipperImmutables) (evm : EVM.State)
    (I : ExecutionEnv) (h : evm.executionEnv.weiValue = ⟨0⟩)
    (hbound :
      (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨11⟩).toNat ≤
        (clipperActiveArgWord I).toNat) :
    ExecTransitionBody (config v) (contract v) evm (clipperActiveStore I)
      activeTransition.body .reverted := by
  refine ExecFuncBody.execBlockRevert ?_
  refine ExecBlock.consNormal (ExecStmt.requireTrue (evalCallvalueEq_true h)) ?_
  exact ExecBlock.consRevert (ExecStmt.returnRevert (by
    simp [evalExprs?, clipperEvalActiveElem_revert v evm I hbound, EvalResult.bind, bind]))

/-! ## EVM trace -/

set_option maxHeartbeats 1000000 in
theorem clipperReachActiveBody {cA gh bl σ σ₀ A I} {g : Sat256} (v : ClipperImmutables)
    {code : ByteArray} (hpatch : patchRuntime clipperBytecode (patches v) = some code)
    (hcode : I.code = code) (hwv : I.weiValue = ⟨0⟩)
    (hsz : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hsel : selIs I (clipperSelBytes 0)) :
    ∃ k C, RD code I g (initState cA gh bl σ σ₀ g A I) (⟨883⟩ : UInt256)
      [clipperSelWord I] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
  obtain ⟨_, _, h32⟩ := clipperReachRoot (cA := cA) (gh := gh) (bl := bl)
    (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := g) v hpatch hcode hwv hsz hsize
  have hword := clipperActiveSelectorWord hsz hsel
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
  have h162 := clipperSplitTaken (pc := (⟨43⟩ : UInt256)) (pivot := clipperSelNat 3)
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
    (clipperJumpDestBeforeFirstPatch v hpatch (⟨162⟩ : UInt256) (by native_decide))
    (by simp)
  have h222 := clipperSplitTaken (pc := (⟨163⟩ : UInt256)) (pivot := clipperSelNat 13)
    (tgt := (⟨222⟩ : UInt256))
    (h162.jumpdest
      (by
          change decode code (⟨162⟩ : UInt256) = some (.JUMPDEST, .none)
          clipper_decode)
      (by simp))
    (by
        change decode code (⟨163⟩ : UInt256) = some (.DUP1, .none)
        clipper_decode)
    (by
        change decode code (selArmPush4Pc (⟨163⟩ : UInt256)) =
          some (.Push .PUSH4, some (clipperSelNat 13, 4))
        clipper_decode)
    (by
        change decode code (selArmEqPc (⟨163⟩ : UInt256)) = some (.GT, .none)
        clipper_decode)
    (by decide)
    (by
        change decode code (selArmPushTgtPc (⟨163⟩ : UInt256)) =
          some (.Push .PUSH2, some (⟨222⟩, 2))
        clipper_decode)
    (by
        change decode code (selArmJumpiPc (⟨163⟩ : UInt256) 2) = some (.JUMPI, .none)
        clipper_decode)
    (by rw [hword]; native_decide)
    (clipperJumpDestBeforeFirstPatch v hpatch (⟨222⟩ : UInt256) (by native_decide))
    (by simp)
  have h234 := clipperArmNotTaken (pc := (⟨223⟩ : UInt256))
    (next := (⟨234⟩ : UInt256)) (sel := clipperSelNat 20)
    (tgt := (⟨875⟩ : UInt256))
    (h222.jumpdest
      (by
          change decode code (⟨222⟩ : UInt256) = some (.JUMPDEST, .none)
          clipper_decode)
      (by simp))
    (by
        change decode code (⟨223⟩ : UInt256) = some (.DUP1, .none)
        clipper_decode)
    (by
        change decode code (selArmPush4Pc (⟨223⟩ : UInt256)) =
          some (.Push .PUSH4, some (clipperSelNat 20, 4))
        clipper_decode)
    (by
        change decode code (selArmEqPc (⟨223⟩ : UInt256)) = some (.EQ, .none)
        clipper_decode)
    (by decide)
    (by
        change decode code (selArmPushTgtPc (⟨223⟩ : UInt256)) =
          some (.Push .PUSH2, some (⟨875⟩, 2))
        clipper_decode)
    (by
        change decode code (selArmJumpiPc (⟨223⟩ : UInt256) 2) = some (.JUMPI, .none)
        clipper_decode)
    (by rw [hword]; native_decide)
    (by native_decide)
    (by simp)
  have h883 := clipperArmTaken (pc := (⟨234⟩ : UInt256)) (sel := clipperSelNat 0)
    (tgt := (⟨883⟩ : UInt256)) h234
    (by
        change decode code (⟨234⟩ : UInt256) = some (.DUP1, .none)
        clipper_decode)
    (by
        change decode code (selArmPush4Pc (⟨234⟩ : UInt256)) =
          some (.Push .PUSH4, some (clipperSelNat 0, 4))
        clipper_decode)
    (by
        change decode code (selArmEqPc (⟨234⟩ : UInt256)) = some (.EQ, .none)
        clipper_decode)
    (by decide)
    (by
        change decode code (selArmPushTgtPc (⟨234⟩ : UInt256)) =
          some (.Push .PUSH2, some (⟨883⟩, 2))
        clipper_decode)
    (by
        change decode code (selArmJumpiPc (⟨234⟩ : UInt256) 2) = some (.JUMPI, .none)
        clipper_decode)
    (by rw [hword]; native_decide)
    (clipperJumpDestBeforeFirstPatch v hpatch (⟨883⟩ : UInt256) (by native_decide))
    (by simp)
  exact ⟨_, _, h883⟩

theorem clipperActiveExternalEntryWf (v : ClipperImmutables) {code : ByteArray}
    (hpatch : patchRuntime clipperBytecode (patches v) = some code) :
    solcOneUintExternalEntryWf code (⟨883⟩ : UInt256)
      (⟨476⟩ : UInt256) (⟨3497⟩ : UInt256) := by
  unfold solcOneUintExternalEntryWf solcOneUintExternalDecodedPc
    solcOneAddressExternalDecodedPc
  repeat' first | apply And.intro
  all_goals
    rw [clipperDecodeBeforeFirstPatch v hpatch _ (by native_decide)]
    native_decide

theorem clipperActivePatchesWindowDisjoint32 (v : ClipperImmutables) {lo hi : Nat}
    (hlo : 3497 ≤ lo) (hhi : hi ≤ 3528) :
    PatchesWindowDisjoint32 lo hi (patches v) := by
  unfold PatchesWindowDisjoint32 PatchWindowDisjoint32 patches patchesFrom offsets immValues
  simp only [List.foldrM_cons, List.foldrM_nil, List.lookup_cons]
  cases hIlk : wordBytes? v.ilk with
  | none =>
      simp [hIlk]
      try omega
  | some bs =>
      simp [hIlk]
      omega

theorem clipperJumpDest3497 (v : ClipperImmutables) {code : ByteArray}
    (hpatch : patchRuntime clipperBytecode (patches v) = some code) :
    (D_J code 0).contains (⟨3497⟩ : UInt256) = true := by
  apply patchRuntime_D_J_contains_of_patchScanReaches (fuel := 4000) hpatch
  unfold patches patchesFrom offsets immValues
  simp only [List.foldrM_cons, List.foldrM_nil, List.lookup_cons]
  cases hIlk : wordBytes? v.ilk with
  | none =>
      simp [hIlk]
      native_decide
  | some bs =>
      simp [hIlk]
      native_decide

theorem clipperJumpDest3510 (v : ClipperImmutables) {code : ByteArray}
    (hpatch : patchRuntime clipperBytecode (patches v) = some code) :
    (D_J code 0).contains (⟨3510⟩ : UInt256) = true := by
  apply patchRuntime_D_J_contains_of_patchScanReaches (fuel := 4000) hpatch
  unfold patches patchesFrom offsets immValues
  simp only [List.foldrM_cons, List.foldrM_nil, List.lookup_cons]
  cases hIlk : wordBytes? v.ilk with
  | none =>
      simp [hIlk]
      native_decide
  | some bs =>
      simp [hIlk]
      native_decide

@[reducible] def clipperActiveArrayGetterWf (code : ByteArray) : Prop :=
  decode code (⟨3497⟩ : UInt256) = some (.JUMPDEST, .none)
  ∧ decode code (⟨3498⟩ : UInt256) = some (.Push .PUSH1, some (⟨11⟩, 1))
  ∧ decode code (⟨3500⟩ : UInt256) = some (.DUP2, .none)
  ∧ decode code (⟨3501⟩ : UInt256) = some (.DUP2, .none)
  ∧ decode code (⟨3502⟩ : UInt256) = some (.SLOAD, .none)
  ∧ decode code (⟨3503⟩ : UInt256) = some (.DUP2, .none)
  ∧ decode code (⟨3504⟩ : UInt256) = some (.LT, .none)
  ∧ decode code (⟨3505⟩ : UInt256) = some (.Push .PUSH2, some (⟨3510⟩, 2))
  ∧ decode code (⟨3508⟩ : UInt256) = some (.JUMPI, .none)
  ∧ decode code (⟨3509⟩ : UInt256) = some (.INVALID, .none)
  ∧ decode code (⟨3510⟩ : UInt256) = some (.JUMPDEST, .none)
  ∧ decode code (⟨3511⟩ : UInt256) = some (.Push .PUSH1, some (⟨0⟩, 1))
  ∧ decode code (⟨3513⟩ : UInt256) = some (.SWAP2, .none)
  ∧ decode code (⟨3514⟩ : UInt256) = some (.DUP3, .none)
  ∧ decode code (⟨3515⟩ : UInt256) = some (.MSTORE, .none)
  ∧ decode code (⟨3516⟩ : UInt256) = some (.Push .PUSH1, some (⟨32⟩, 1))
  ∧ decode code (⟨3518⟩ : UInt256) = some (.SWAP1, .none)
  ∧ decode code (⟨3519⟩ : UInt256) = some (.SWAP2, .none)
  ∧ decode code (⟨3520⟩ : UInt256) = some (.KECCAK256, .none)
  ∧ decode code (⟨3521⟩ : UInt256) = some (.ADD, .none)
  ∧ decode code (⟨3522⟩ : UInt256) = some (.SLOAD, .none)
  ∧ decode code (⟨3523⟩ : UInt256) = some (.SWAP1, .none)
  ∧ decode code (⟨3524⟩ : UInt256) = some (.POP, .none)
  ∧ decode code (⟨3525⟩ : UInt256) = some (.DUP2, .none)
  ∧ decode code (⟨3526⟩ : UInt256) = some (.JUMP, .none)

theorem clipperActiveArrayGetterWfPatched (v : ClipperImmutables) {code : ByteArray}
    (hpatch : patchRuntime clipperBytecode (patches v) = some code) :
    clipperActiveArrayGetterWf code := by
  unfold clipperActiveArrayGetterWf
  repeat' first | apply And.intro
  all_goals
    exact patchRuntime_decode_disjoint_of_decode_res hpatch
      (by apply clipperActivePatchesWindowDisjoint32 v <;> native_decide)
      (by apply clipperActivePatchesWindowDisjoint32 v <;> native_decide)
      (by native_decide)
      (by native_decide)
      (by native_decide)

theorem clipperActiveX_decoded {cA gh bl σ σ₀ A I} {g : Sat256} {sel : UInt256}
    (v : ClipperImmutables) {code : ByteArray}
    (hpatch : patchRuntime clipperBytecode (patches v) = some code)
    (hsz36 : 36 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hreach : ∃ k C, RD code I g
      (initState cA gh bl σ σ₀ g A I) (⟨883⟩ : UInt256) [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    ∃ k C, RD code I g (initState cA gh bl σ σ₀ g A I) (⟨3497⟩ : UInt256)
      (clipperActiveArgWord I :: ⟨476⟩ :: [sel])
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
  obtain ⟨_, _, rd905⟩ := solcOneUintExternalLenOk
    (entry := (⟨883⟩ : UInt256)) (ret := (⟨476⟩ : UInt256))
    (routine := (⟨3497⟩ : UInt256)) hreach
    (clipperActiveExternalEntryWf v hpatch)
    (by
      simpa [solcOneUintExternalDecodedPc, solcOneAddressExternalDecodedPc] using
        clipperJumpDestBeforeFirstPatch v hpatch (⟨905⟩ : UInt256) (by native_decide))
    hsz36 hsize
  obtain ⟨_, _, rd3497⟩ := solcOneUintExternalLoadAndJump
    (entry := (⟨883⟩ : UInt256)) (ret := (⟨476⟩ : UInt256))
    (routine := (⟨3497⟩ : UInt256)) (R := [sel])
    rd905 (clipperActiveExternalEntryWf v hpatch) (clipperJumpDest3497 v hpatch)
    (by simp only [List.length_singleton]; omega)
  exact ⟨_, _, by simpa [clipperActiveArgWord] using rd3497⟩

theorem clipperActiveX_shortarg {cA gh bl σ σ₀ A I} {g : Sat256} {sel : UInt256}
    (v : ClipperImmutables) {code : ByteArray}
    (hpatch : patchRuntime clipperBytecode (patches v) = some code)
    (hsz4 : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hshort : I.calldata.size < 36)
    (hreach : ∃ k C, RD code I g
      (initState cA gh bl σ σ₀ g A I) (⟨883⟩ : UInt256) [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    RDrev code g (initState cA gh bl σ σ₀ g A I) := by
  exact solcOneUintExternalShort
    (entry := (⟨883⟩ : UInt256)) (ret := (⟨476⟩ : UInt256))
    (routine := (⟨3497⟩ : UInt256)) hreach
    (clipperActiveExternalEntryWf v hpatch) hsz4 hsize hshort

set_option maxHeartbeats 1000000 in
theorem clipperActiveArrayBounds_ok {code : ByteArray} {g : Sat256} {s0 : State}
    {ee : ExecutionEnv} {k C : ℕ} {ret : UInt256} {R : List UInt256}
    {rdata : ByteArray} {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap}
    (h : RD code ee g s0 (⟨3497⟩ : UInt256)
      (clipperActiveArgWord ee :: ret :: R)
      solcFreePtrMem (UInt256.ofNat 3) rdata (cA, σ) k C)
    (hwf : clipperActiveArrayGetterWf code)
    (h3510 : (D_J code 0).contains (⟨3510⟩ : UInt256) = true)
    (hbound : (clipperActiveArgWord ee).toNat < (solcSlotWord σ ee ⟨11⟩).toNat)
    (hov : R.length + 8 ≤ 1024) :
    ∃ k' C', RD code ee g s0 (⟨3510⟩ : UInt256)
      (clipperActiveArgWord ee :: ⟨11⟩ :: clipperActiveArgWord ee :: ret :: R)
      solcFreePtrMem (UInt256.ofNat 3) rdata (cA, σ) k' C' := by
  rcases hwf with
    ⟨hd3497, hd3498, hd3500, hd3501, hd3502, hd3503, hd3504, hd3505, hd3508,
      _hd3509, _hd3510, _hd3511, _hd3513, _hd3514, _hd3515, _hd3516, _hd3518,
      _hd3519, _hd3520, _hd3521, _hd3522, _hd3523, _hd3524, _hd3525, _hd3526⟩
  have hlt :
      UInt256.lt (clipperActiveArgWord ee) (solcSlotWord σ ee ⟨11⟩) = ⟨1⟩ :=
    ult_one hbound
  have rd3498 := h.jumpdest hd3497 (by evm_ov)
  have rd3500 := rd3498.push1 ⟨11⟩ hd3498 (by evm_ov)
  have rd3501 := rd3500.dup2 hd3500 (by evm_ov)
  have rd3502 := rd3501.dup2 hd3501 (by evm_ov)
  obtain ⟨_, _, rd3503⟩ := rd3502.sload hd3502 (by evm_ov)
  have rd3504 := rd3503.dup2 hd3503 (by evm_ov)
  have rd3505raw := rd3504.lt hd3504 (by evm_ov)
  have rd3505 := by
    simpa [solcSlotWord, hlt] using rd3505raw
  have rd3508 := rd3505.push2 ⟨3510⟩ hd3505 (by evm_ov)
  have rd3510 := rd3508.jumpiT hd3508 (by decide) h3510 (by evm_ov)
  exact ⟨_, _, rd3510⟩

set_option maxHeartbeats 1000000 in
theorem clipperActiveArrayPrepareHash_ok {code : ByteArray} {g : Sat256} {s0 : State}
    {ee : ExecutionEnv} {k C : ℕ} {ret : UInt256} {R : List UInt256}
    {rdata : ByteArray} {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap}
    (h : RD code ee g s0 (⟨3510⟩ : UInt256)
      (clipperActiveArgWord ee :: ⟨11⟩ :: clipperActiveArgWord ee :: ret :: R)
      solcFreePtrMem (UInt256.ofNat 3) rdata (cA, σ) k C)
    (hwf : clipperActiveArrayGetterWf code)
    (hov : R.length + 8 ≤ 1024) :
    ∃ k' C', RD code ee g s0 (⟨3520⟩ : UInt256)
      (⟨0⟩ :: ⟨32⟩ :: clipperActiveArgWord ee :: clipperActiveArgWord ee :: ret :: R)
      clipperActiveHashMem (UInt256.ofNat 3) rdata (cA, σ) k' C' := by
  rcases hwf with
    ⟨_hd3497, _hd3498, _hd3500, _hd3501, _hd3502, _hd3503, _hd3504, _hd3505,
      _hd3508, _hd3509, hd3510, hd3511, hd3513, hd3514, hd3515, hd3516, hd3518,
      hd3519, _hd3520, _hd3521, _hd3522, _hd3523, _hd3524, _hd3525, _hd3526⟩
  have rd3511 := h.jumpdest hd3510 (by evm_ov)
  have rd3513 := rd3511.push1 ⟨0⟩ hd3511 (by evm_ov)
  have rd3514 := rd3513.swap2 hd3513 (by evm_ov)
  have rd3515 := rd3514.dup3 hd3514 (by evm_ov)
  have rd3516 := rd3515.mstore 0 clipperActiveHashMem (UInt256.ofNat 3)
    hd3515 mem_cost (by rfl) (by native_decide) (by evm_ov)
  have rd3518 := rd3516.push1 ⟨32⟩ hd3516 (by evm_ov)
  have rd3519 := rd3518.swap1 hd3518 (by evm_ov)
  have rd3520 := rd3519.swap2 hd3519 (by evm_ov)
  exact ⟨_, _, rd3520⟩

set_option maxHeartbeats 4000000 in
theorem clipperActiveArrayHashSlot_ok {code : ByteArray} {g : Sat256} {s0 : State}
    {ee : ExecutionEnv} {k C : ℕ} {ret : UInt256} {R : List UInt256}
    {rdata : ByteArray} {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap}
    (h : RD code ee g s0 (⟨3520⟩ : UInt256)
      (⟨0⟩ :: ⟨32⟩ :: clipperActiveArgWord ee :: clipperActiveArgWord ee :: ret :: R)
      clipperActiveHashMem (UInt256.ofNat 3) rdata (cA, σ) k C)
    (hwf : clipperActiveArrayGetterWf code)
    (hov : R.length + 8 ≤ 1024) :
    ∃ k' C', RD code ee g s0 (⟨3522⟩ : UInt256)
      (clipperActiveSlot ee :: clipperActiveArgWord ee :: ret :: R)
      clipperActiveHashMem (UInt256.ofNat 3) rdata (cA, σ) k' C' := by
  rcases hwf with
    ⟨_hd3497, _hd3498, _hd3500, _hd3501, _hd3502, _hd3503, _hd3504, _hd3505,
      _hd3508, _hd3509, _hd3510, _hd3511, _hd3513, _hd3514, _hd3515, _hd3516,
      _hd3518, _hd3519, hd3520, hd3521, _hd3522, _hd3523, _hd3524, _hd3525,
      _hd3526⟩
  have rd3521 := h.keccak256 0 activeDataSlot (UInt256.ofNat 3)
    hd3520 mem_cost clipperActiveHashMem_keccak_slot (by native_decide) (by evm_ov)
  have rd3522raw := rd3521.add hd3521 (by evm_ov)
  exact ⟨_, _, by
    simpa [clipperActiveSlot_eq,
      show ((⟨3520⟩ : UInt256) + ⟨1⟩ + ⟨1⟩) = (⟨3522⟩ : UInt256) from by
        native_decide] using rd3522raw⟩

theorem clipperActiveArrayHash_ok {code : ByteArray} {g : Sat256} {s0 : State}
    {ee : ExecutionEnv} {k C : ℕ} {ret : UInt256} {R : List UInt256}
    {rdata : ByteArray} {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap}
    (h : RD code ee g s0 (⟨3510⟩ : UInt256)
      (clipperActiveArgWord ee :: ⟨11⟩ :: clipperActiveArgWord ee :: ret :: R)
      solcFreePtrMem (UInt256.ofNat 3) rdata (cA, σ) k C)
    (hwf : clipperActiveArrayGetterWf code)
    (hov : R.length + 8 ≤ 1024) :
    ∃ k' C', RD code ee g s0 (⟨3522⟩ : UInt256)
      (clipperActiveSlot ee :: clipperActiveArgWord ee :: ret :: R)
      clipperActiveHashMem (UInt256.ofNat 3) rdata (cA, σ) k' C' := by
  obtain ⟨_, _, rd3520⟩ := clipperActiveArrayPrepareHash_ok h hwf hov
  exact clipperActiveArrayHashSlot_ok rd3520 hwf hov

theorem clipperActiveArrayFinish_ok {code : ByteArray} {g : Sat256} {s0 : State}
    {ee : ExecutionEnv} {k C : ℕ} {ret : UInt256} {R : List UInt256}
    {rdata : ByteArray} {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap}
    (h : RD code ee g s0 (⟨3522⟩ : UInt256)
      (clipperActiveSlot ee :: clipperActiveArgWord ee :: ret :: R)
      clipperActiveHashMem (UInt256.ofNat 3) rdata (cA, σ) k C)
    (hwf : clipperActiveArrayGetterWf code)
    (hret : (D_J code 0).contains ret = true)
    (hov : R.length + 8 ≤ 1024) :
    ∃ k' C', RD code ee g s0 ret
      (clipperActiveWord σ ee :: ret :: R)
      clipperActiveHashMem (UInt256.ofNat 3) rdata (cA, σ) k' C' := by
  rcases hwf with
    ⟨_hd3497, _hd3498, _hd3500, _hd3501, _hd3502, _hd3503, _hd3504, _hd3505,
      _hd3508, _hd3509, _hd3510, _hd3511, _hd3513, _hd3514, _hd3515, _hd3516,
      _hd3518, _hd3519, _hd3520, _hd3521, hd3522, hd3523, hd3524, hd3525,
      hd3526⟩
  obtain ⟨_, _, rd3523raw⟩ := h.sload hd3522 (by evm_ov)
  have rd3523 := by
    simpa [clipperActiveWord, solcSlotWord] using rd3523raw
  have rd3524 := rd3523.swap1 hd3523 (by evm_ov)
  have rd3525 := rd3524.pop hd3524 (by evm_ov)
  have rd3526 := rd3525.dup2 hd3525 (by evm_ov)
  exact ⟨_, _, rd3526.jump hd3526 hret (by evm_ov)⟩

theorem clipperActiveArrayLoad_ok {code : ByteArray} {g : Sat256} {s0 : State}
    {ee : ExecutionEnv} {k C : ℕ} {ret : UInt256} {R : List UInt256}
    {rdata : ByteArray} {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap}
    (h : RD code ee g s0 (⟨3510⟩ : UInt256)
      (clipperActiveArgWord ee :: ⟨11⟩ :: clipperActiveArgWord ee :: ret :: R)
      solcFreePtrMem (UInt256.ofNat 3) rdata (cA, σ) k C)
    (hwf : clipperActiveArrayGetterWf code)
    (hret : (D_J code 0).contains ret = true)
    (hov : R.length + 8 ≤ 1024) :
    ∃ k' C', RD code ee g s0 ret
      (clipperActiveWord σ ee :: ret :: R)
      clipperActiveHashMem (UInt256.ofNat 3) rdata (cA, σ) k' C' := by
  obtain ⟨_, _, rd3522⟩ := clipperActiveArrayHash_ok h hwf hov
  exact clipperActiveArrayFinish_ok rd3522 hwf hret hov

theorem clipperActiveArrayGetter_ok {code : ByteArray} {g : Sat256} {s0 : State}
    {ee : ExecutionEnv} {k C : ℕ} {ret : UInt256} {R : List UInt256}
    {rdata : ByteArray} {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap}
    (h : RD code ee g s0 (⟨3497⟩ : UInt256)
      (clipperActiveArgWord ee :: ret :: R)
      solcFreePtrMem (UInt256.ofNat 3) rdata (cA, σ) k C)
    (hwf : clipperActiveArrayGetterWf code)
    (hret : (D_J code 0).contains ret = true)
    (h3510 : (D_J code 0).contains (⟨3510⟩ : UInt256) = true)
    (hbound : (clipperActiveArgWord ee).toNat < (solcSlotWord σ ee ⟨11⟩).toNat)
    (hov : R.length + 8 ≤ 1024) :
    ∃ k' C', RD code ee g s0 ret
      (clipperActiveWord σ ee :: ret :: R)
      clipperActiveHashMem (UInt256.ofNat 3) rdata (cA, σ) k' C' := by
  obtain ⟨_, _, rd3510⟩ :=
    clipperActiveArrayBounds_ok h hwf h3510 hbound hov
  exact clipperActiveArrayLoad_ok rd3510 hwf hret hov

set_option maxHeartbeats 1000000 in
theorem clipperActiveArrayGetter_invalid {code : ByteArray} {g : Sat256} {s0 : State}
    {ee : ExecutionEnv} {k C : ℕ} {ret : UInt256} {R : List UInt256}
    {rdata : ByteArray} {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap}
    (h : RD code ee g s0 (⟨3497⟩ : UInt256)
      (clipperActiveArgWord ee :: ret :: R)
      solcFreePtrMem (UInt256.ofNat 3) rdata (cA, σ) k C)
    (hwf : clipperActiveArrayGetterWf code)
    (hbound : (solcSlotWord σ ee ⟨11⟩).toNat ≤ (clipperActiveArgWord ee).toNat)
    (hov : R.length + 8 ≤ 1024) :
    RDinvalid code g s0 := by
  rcases hwf with
    ⟨hd3497, hd3498, hd3500, hd3501, hd3502, hd3503, hd3504, hd3505, hd3508,
      hd3509, _hd3510, _hd3511, _hd3513, _hd3514, _hd3515, _hd3516, _hd3518,
      _hd3519, _hd3520, _hd3521, _hd3522, _hd3523, _hd3524, _hd3525, _hd3526⟩
  have hlt :
      UInt256.lt (clipperActiveArgWord ee) (solcSlotWord σ ee ⟨11⟩) = ⟨0⟩ :=
    ult_zero hbound
  have rd3498 := h.jumpdest hd3497 (by evm_ov)
  have rd3500 := rd3498.push1 ⟨11⟩ hd3498 (by evm_ov)
  have rd3501 := rd3500.dup2 hd3500 (by evm_ov)
  have rd3502 := rd3501.dup2 hd3501 (by evm_ov)
  obtain ⟨_, _, rd3503⟩ := rd3502.sload hd3502 (by evm_ov)
  have rd3504 := rd3503.dup2 hd3503 (by evm_ov)
  have rd3505raw := rd3504.lt hd3504 (by evm_ov)
  have rd3505 := by
    simpa [solcSlotWord, hlt] using rd3505raw
  have rd3508 := rd3505.push2 ⟨3510⟩ hd3505 (by evm_ov)
  have rd3509 := rd3508.jumpiNT hd3508 (by decide) (by evm_ov)
  exact RD.invalidHalt rd3509 hd3509

theorem clipperX_active_ok {cA gh bl σ σ₀ A I} {g : Sat256} {sel : UInt256}
    (v : ClipperImmutables) {code : ByteArray}
    (hpatch : patchRuntime clipperBytecode (patches v) = some code)
    (hsz36 : 36 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hbound : (clipperActiveArgWord I).toNat < (solcSlotWord σ I ⟨11⟩).toNat)
    (hreach : ∃ k C, RD code I g
      (initState cA gh bl σ σ₀ g A I) (⟨883⟩ : UInt256) [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    RDret code g (initState cA gh bl σ σ₀ g A I) (cA, σ)
      (UInt256.toByteArray (clipperActiveWord σ I)) := by
  obtain ⟨_, _, rd3497⟩ := clipperActiveX_decoded (v := v) hpatch hsz36 hsize hreach
  obtain ⟨_, _, rd476⟩ := clipperActiveArrayGetter_ok
    (ret := (⟨476⟩ : UInt256)) (R := [sel]) rd3497
    (clipperActiveArrayGetterWfPatched v hpatch)
    (clipperJumpDestBeforeFirstPatch v hpatch (⟨476⟩ : UInt256) (by native_decide))
    (clipperJumpDest3510 v hpatch) hbound (by simp only [List.length_singleton]; omega)
  exact RD.solcReturnWordFromMem
    (val := clipperActiveWord σ I) (ret := ⟨476⟩) (R := [sel])
    (mem := clipperActiveHashMem)
    (memout := solcScratchReturnMem clipperActiveHashMem (clipperActiveWord σ I))
    rd476
    (clipperReturnWord476Wf v hpatch)
    clipperActiveHashMem_mload64
    (by rfl)
    (solcScratchReturnMem_mload64 (clipperActiveWord σ I)
      clipperActiveHashMem_size clipperActiveHashMem_read64)
    (solcScratchReturnMem_read128 (clipperActiveWord σ I) clipperActiveHashMem_size)
    (by simp only [List.length_singleton]; omega)

theorem clipperX_active_invalid {cA gh bl σ σ₀ A I} {g : Sat256} {sel : UInt256}
    (v : ClipperImmutables) {code : ByteArray}
    (hpatch : patchRuntime clipperBytecode (patches v) = some code)
    (hsz36 : 36 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hbound : (solcSlotWord σ I ⟨11⟩).toNat ≤ (clipperActiveArgWord I).toNat)
    (hreach : ∃ k C, RD code I g
      (initState cA gh bl σ σ₀ g A I) (⟨883⟩ : UInt256) [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    RDinvalid code g (initState cA gh bl σ σ₀ g A I) := by
  obtain ⟨_, _, rd3497⟩ := clipperActiveX_decoded (v := v) hpatch hsz36 hsize hreach
  exact clipperActiveArrayGetter_invalid
    (ret := (⟨476⟩ : UInt256)) (R := [sel]) rd3497
    (clipperActiveArrayGetterWfPatched v hpatch)
    hbound (by simp only [List.length_singleton]; omega)

theorem clipperActiveBody (v : ClipperImmutables) {code : ByteArray}
    (hpatch : patchRuntime clipperBytecode (patches v) = some code)
    {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256}
    (hcode : I.code = code) (hsize : I.calldata.size < UInt256.size)
    (_hperm : I.perm = true) (hwv : I.weiValue = ⟨0⟩)
    (hsel : selIs I (clipperSelBytes 0))
    (hAccounts : accountMapEquiv σ_evm σ_solm) :
    runtimeEquivalenceFor (config v) (contract v) cA gh bl σ_evm σ_solm σ₀ g A I := by
  have hsz4 : 4 ≤ I.calldata.size :=
    calldata_size_ge_of_selIs I (clipperSelBytes 0) (by native_decide) hsel
  have hdispatch : dispatchMsg (contract v) I.calldata = some activeTransition :=
    clipperDispatch_active v hsel
  have hreach := clipperReachActiveBody (cA := cA) (gh := gh) (bl := bl)
    (σ := σ_evm) (σ₀ := σ₀) (A := A) (I := I) (g := Sat256.ofUInt256 g)
    (v := v) hpatch hcode hwv hsz4 hsize hsel
  by_cases hsz36 : 36 ≤ I.calldata.size
  · have hdecode := clipperDecode_active_ok v (I := I) hsz36
    by_cases hbound : (clipperActiveArgWord I).toNat < (solcSlotWord σ_evm I ⟨11⟩).toNat
    · have hlen :
          solcSlotWord σ_evm I ⟨11⟩ = solcSlotWord σ_solm I ⟨11⟩ :=
        accountMapEquiv_storage_findD hAccounts I.codeOwner ⟨11⟩ ⟨0⟩
      have hboundSolm :
          (clipperActiveArgWord I).toNat < (solcSlotWord σ_solm I ⟨11⟩).toNat := by
        rwa [← hlen]
      have hword : clipperActiveWord σ_evm I = clipperActiveWord σ_solm I :=
        accountMapEquiv_storage_findD hAccounts I.codeOwner (clipperActiveSlot I) ⟨0⟩
      have hbody :
          ExecTransitionBody (config v) (contract v)
            (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)
            (clipperActiveStore I) activeTransition.body
            (.returned { contract := contract v, locals := clipperActiveStore I }
              (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)
              (some [(.int (Int.ofNat (clipperActiveWord σ_solm I).toNat))])) := by
        simpa [clipperActiveWord, solcSlotWord, initState, Solm.EVM.storageLoad,
          State.lookupAccount] using
          clipperActiveBodyReturns v
            (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I) I
            (by simp only [initState]; exact hwv) hboundSolm
      exact (clipperX_active_ok (v := v) (g := Sat256.ofUInt256 g) hpatch hsz36
        hsize hbound hreach)
        |>.reEquivExecutionTransport hcode hdispatch hdecode hbody (by rw [← hword])
          hAccounts
          (returnEquiv_of_encode
            (by simpa [uint256] using uint256ReturnEncoding (clipperActiveWord σ_evm I)))
    · have hlen :
          solcSlotWord σ_evm I ⟨11⟩ = solcSlotWord σ_solm I ⟨11⟩ :=
        accountMapEquiv_storage_findD hAccounts I.codeOwner ⟨11⟩ ⟨0⟩
      have hboundEvm :
          (solcSlotWord σ_evm I ⟨11⟩).toNat ≤ (clipperActiveArgWord I).toNat := by
        omega
      have hboundSolm :
          (solcSlotWord σ_solm I ⟨11⟩).toNat ≤ (clipperActiveArgWord I).toNat := by
        rwa [← hlen]
      have hbody :
          ExecTransitionBody (config v) (contract v)
            (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)
            (clipperActiveStore I) activeTransition.body .reverted := by
        simpa [solcSlotWord, initState, Solm.EVM.storageLoad, State.lookupAccount] using
          clipperActiveBodyReverts v
            (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I) I
            (by simp only [initState]; exact hwv) hboundSolm
      exact RDinvalid.reEquivExecutionInvalid hcode
        (clipperX_active_invalid (v := v) (g := Sat256.ofUInt256 g) hpatch hsz36 hsize
          hboundEvm hreach)
        hdispatch hdecode hbody
  · exact (clipperActiveX_shortarg (v := v) (g := Sat256.ofUInt256 g) hpatch hsz4
      hsize (by omega) hreach)
      |>.reEquivDecodingFailed hcode hdispatch
        (clipperDecode_active_none_short v hsz4 (by omega))

end Benchmarks.Dss.Clipper
