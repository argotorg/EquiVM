import Benchmarks.Dss.Clipper.Fallback

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach Reasoning.Refinement
open Benchmarks.Dss.Clipper.Immutables

namespace Benchmarks.Dss.Clipper

set_option linter.unusedTactic false

theorem clipperVowSelectorWord {I : ExecutionEnv} (hsz : 4 ≤ I.calldata.size)
    (hsel : selIs I (clipperSelBytes 26)) :
    clipperSelWord I = clipperSelNat 26 := by
  simpa [clipperSelWord, solcSelectorWord, clipperSelNat] using
    solcSelectorWord_eq_of_beq I hsz 0x62 0x6c 0xb3 0xc5 (clipperSelNat 26)
      (by native_decide) (by simpa [clipperSelBytes, selIs] using hsel)

theorem clipperDispatch_vow (v : ClipperImmutables) {I : ExecutionEnv}
    (hsel : selIs I (clipperSelBytes 26)) :
    dispatchMsg (contract v) I.calldata = some vowTransition := by
  refine dispatchMsg_eq_some_of_split (contract := contract v)
    (pre :=
      [activeTransition, bufTransition, calcTransition, chipTransition, chostTransition,
        countTransition, cuspTransition, denyTransition, dogTransition, fileUintTransition,
        fileAddressTransition, getStatusTransition, ilkTransition v, kickTransition v,
        kicksTransition, listTransition, redoTransition v, relyTransition, salesTransition,
        spotterTransition, stoppedTransition, tailTransition, takeTransition v, tipTransition,
        upchostTransition v, vatTransition v])
    (post := [wardsTransition, yankTransition v])
    (ti := vowTransition) (cd := I.calldata) (by rfl) ?_ ?_ ?_ (by rfl)
  · rfl
  · intro t ht
    simp only [List.mem_cons, List.mem_nil_iff] at ht
    rcases ht with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      | rfl | rfl | hfalse
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
    · cases hfalse
  · rw [selectorOf, vowSelectorBytes]
    simpa [clipperSelBytes] using hsel

theorem clipperDecode_vow (v : ClipperImmutables) {I : ExecutionEnv}
    (hsz : 4 ≤ I.calldata.size) :
    decodeCalldataWithMode (config v).abiDecodeMode (vowTransition.params.map Param.name)
      (transitionSignature vowTransition).paramTypes I.calldata = some ∅ := by
  show decodeCalldataWithMode (config v).abiDecodeMode [] [] I.calldata = some ∅
  exact decodeCalldataWithMode_empty_ok hsz

theorem clipperEvalVow (v : ClipperImmutables) (evm : EVM.State) (locals : Store)
    (hbase : locals.get? "vow" = none) :
    evalExpr? (config v) { contract := contract v, locals := locals } evm
      (.storage vowRef) =
      .ok (.address (AccountAddress.ofNat
        (UInt256.land (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨2⟩)
          solcAddrMask).toNat)) := by
  let er : EvaledStorageRef := { base := "vow", steps := [] }
  have her : evalStorageRef (config v)
      { contract := contract v, locals := locals } evm vowRef = .ok er := by
    unfold evalStorageRef vowRef
    simp only [evalStorageRefSteps]
    rfl
  have hty : storageTypeAt? (contract v).storage er = some (.elem .address) := by
    simp [er, storageTypeAt?, contract, storageDecls, addrSt]
  have hloc : (config v).storage.layout er = fun _ => some (addrLoc ⟨2⟩) := by
    funext evm'
    rfl
  exact evalExpr_storage_scalar_value hbase her hty hloc
    (clipperStorageLocLoad_address evm ⟨2⟩)

theorem clipperVowBodyReturns (v : ClipperImmutables) (evm : EVM.State) (locals : Store)
    (h : evm.executionEnv.weiValue = ⟨0⟩) (hbase : locals.get? "vow" = none) :
    ExecTransitionBody (config v) (contract v) evm locals vowTransition.body
      (.returned { contract := contract v, locals := locals } evm
        (some [(.address (AccountAddress.ofNat
          (UInt256.land (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨2⟩)
            solcAddrMask).toNat))])) := by
  simpa [vowTransition] using
    nonpayableReturnExprBodyReturns (cfg := config v) (contract := contract v) h
      (clipperEvalVow v evm locals hbase)

set_option maxHeartbeats 1000000 in
theorem clipperReachVowBody {cA gh bl σ σ₀ A I} {g : Sat256}
    (v : ClipperImmutables)
    {code : ByteArray} (hpatch : patchRuntime clipperBytecode (patches v) = some code)
    (hcode : I.code = code) (hwv : I.weiValue = ⟨0⟩)
    (hsz : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hsel : selIs I (clipperSelBytes 26)) :
    ∃ k C, RD code I g (initState cA gh bl σ σ₀ g A I) (⟨829⟩ : UInt256)
      [clipperSelWord I] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
  obtain ⟨_, _, h32⟩ := clipperReachRoot (cA := cA) (gh := gh) (bl := bl)
    (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := g) v hpatch hcode hwv hsz hsize
  have hword := clipperVowSelectorWord hsz hsel
  have h260 := clipperSplitTaken (pc := (⟨32⟩ : UInt256)) (pivot := clipperSelNat 20)
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
    (clipperJumpDestBeforeFirstPatch v hpatch (⟨260⟩ : UInt256) (by native_decide))
    (by simp)
  have h272 := clipperSplitNotTaken (pc := (⟨261⟩ : UInt256))
    (next := (⟨272⟩ : UInt256)) (pivot := clipperSelNat 9)
    (tgt := (⟨369⟩ : UInt256))
    (h260.jumpdest
      (by
          change decode code (⟨260⟩ : UInt256) = some (.JUMPDEST, .none)
          clipper_decode)
      (by simp))
    (by
        change decode code (⟨261⟩ : UInt256) = some (.DUP1, .none)
        clipper_decode)
    (by
        change decode code (selArmPush4Pc (⟨261⟩ : UInt256)) =
          some (.Push .PUSH4, some (clipperSelNat 9, 4))
        clipper_decode)
    (by
        change decode code (selArmEqPc (⟨261⟩ : UInt256)) = some (.GT, .none)
        clipper_decode)
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
  have h283 := clipperSplitNotTaken (pc := (⟨272⟩ : UInt256))
    (next := (⟨283⟩ : UInt256)) (pivot := clipperSelNat 6)
    (tgt := (⟨331⟩ : UInt256)) h272
    (by
        change decode code (⟨272⟩ : UInt256) = some (.DUP1, .none)
        clipper_decode)
    (by
        change decode code (selArmPush4Pc (⟨272⟩ : UInt256)) =
          some (.Push .PUSH4, some (clipperSelNat 6, 4))
        clipper_decode)
    (by
        change decode code (selArmEqPc (⟨272⟩ : UInt256)) = some (.GT, .none)
        clipper_decode)
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
  have h294 := clipperArmNotTaken (pc := (⟨283⟩ : UInt256))
    (next := (⟨294⟩ : UInt256)) (sel := clipperSelNat 6)
    (tgt := (⟨752⟩ : UInt256)) h283
    (by
        change decode code (⟨283⟩ : UInt256) = some (.DUP1, .none)
        clipper_decode)
    (by
        change decode code (selArmPush4Pc (⟨283⟩ : UInt256)) =
          some (.Push .PUSH4, some (clipperSelNat 6, 4))
        clipper_decode)
    (by
        change decode code (selArmEqPc (⟨283⟩ : UInt256)) = some (.EQ, .none)
        clipper_decode)
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
  have h305 := clipperArmNotTaken (pc := (⟨294⟩ : UInt256))
    (next := (⟨305⟩ : UInt256)) (sel := clipperSelNat 11)
    (tgt := (⟨760⟩ : UInt256)) h294
    (by
        change decode code (⟨294⟩ : UInt256) = some (.DUP1, .none)
        clipper_decode)
    (by
        change decode code (selArmPush4Pc (⟨294⟩ : UInt256)) =
          some (.Push .PUSH4, some (clipperSelNat 11, 4))
        clipper_decode)
    (by
        change decode code (selArmEqPc (⟨294⟩ : UInt256)) = some (.EQ, .none)
        clipper_decode)
    (by decide)
    (by
        change decode code (selArmPushTgtPc (⟨294⟩ : UInt256)) =
          some (.Push .PUSH2, some (⟨760⟩, 2))
        clipper_decode)
    (by
        change decode code (selArmJumpiPc (⟨294⟩ : UInt256) 2) = some (.JUMPI, .none)
        clipper_decode)
    (by rw [hword]; native_decide)
    (by native_decide)
    (by simp)
  have h829 := clipperArmTaken (pc := (⟨305⟩ : UInt256)) (sel := clipperSelNat 26)
    (tgt := (⟨829⟩ : UInt256)) h305
    (by
        change decode code (⟨305⟩ : UInt256) = some (.DUP1, .none)
        clipper_decode)
    (by
        change decode code (selArmPush4Pc (⟨305⟩ : UInt256)) =
          some (.Push .PUSH4, some (clipperSelNat 26, 4))
        clipper_decode)
    (by
        change decode code (selArmEqPc (⟨305⟩ : UInt256)) = some (.EQ, .none)
        clipper_decode)
    (by decide)
    (by
        change decode code (selArmPushTgtPc (⟨305⟩ : UInt256)) =
          some (.Push .PUSH2, some (⟨829⟩, 2))
        clipper_decode)
    (by
        change decode code (selArmJumpiPc (⟨305⟩ : UInt256) 2) = some (.JUMPI, .none)
        clipper_decode)
    (by rw [hword]; native_decide)
    (clipperJumpDestBeforeFirstPatch v hpatch (⟨829⟩ : UInt256) (by native_decide))
    (by simp)
  exact ⟨_, _, h829⟩

theorem clipperVowGetterEntryWf (v : ClipperImmutables) {code : ByteArray}
    (hpatch : patchRuntime clipperBytecode (patches v) = some code) :
    solcGetterEntryWf code (⟨829⟩ : UInt256) (⟨716⟩ : UInt256) (⟨3325⟩ : UInt256) := by
  unfold solcGetterEntryWf
  repeat' first | apply And.intro
  all_goals
    rw [clipperDecodeBeforeFirstPatch v hpatch _ (by native_decide)]
    native_decide

theorem clipperVowPatchesWindowDisjoint32 (v : ClipperImmutables) (lo hi : Nat)
    (hlo : lo ∈ [3325, 3326, 3327, 3328, 3329, 3330, 3331, 3332, 3333, 3334,
      3335, 3336, 3337, 3338, 3339, 3340])
    (hhi : hi ∈ [3326, 3327, 3328, 3329, 3330, 3331, 3332, 3333, 3334,
      3335, 3336, 3337, 3338, 3339, 3340, 3341]) :
    PatchesWindowDisjoint32 lo hi (patches v) := by
  unfold PatchesWindowDisjoint32 PatchWindowDisjoint32 patches patchesFrom offsets immValues
  simp only [List.foldrM_cons, List.foldrM_nil, List.lookup_cons]
  cases hIlk : wordBytes? v.ilk
  · simp [hIlk] at hlo hhi ⊢
  · simp [hIlk] at hlo hhi ⊢
    omega

theorem clipperVowSlotGetterWf (v : ClipperImmutables) {code : ByteArray}
    (hpatch : patchRuntime clipperBytecode (patches v) = some code) :
    solcAddressSlotGetterWf code (⟨3325⟩ : UInt256) (⟨2⟩ : UInt256) := by
  unfold solcAddressSlotGetterWf
  repeat' first | apply And.intro
  all_goals
    exact patchRuntime_decode_disjoint_of_decode_res hpatch
      (by
        apply clipperVowPatchesWindowDisjoint32 v <;> native_decide)
      (by
        apply clipperVowPatchesWindowDisjoint32 v <;> native_decide)
      (by native_decide)
      (by native_decide)
      (by native_decide)

theorem clipperJumpDest3325 (v : ClipperImmutables) {code : ByteArray}
    (hpatch : patchRuntime clipperBytecode (patches v) = some code) :
    (D_J code 0).contains (⟨3325⟩ : UInt256) = true := by
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

theorem clipperVowBody (v : ClipperImmutables) {code : ByteArray}
    (hpatch : patchRuntime clipperBytecode (patches v) = some code)
    {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256}
    (hcode : I.code = code) (hsize : I.calldata.size < UInt256.size)
    (_hperm : I.perm = true) (hwv : I.weiValue = ⟨0⟩)
    (hsel : selIs I (clipperSelBytes 26))
    (hAccounts : accountMapEquiv σ_evm σ_solm) :
    runtimeEquivalenceFor (config v) (contract v) cA gh bl σ_evm σ_solm σ₀ g A I := by
  have hsz : 4 ≤ I.calldata.size :=
    calldata_size_ge_of_selIs I (clipperSelBytes 26) (by native_decide) hsel
  have hbody :
      ExecTransitionBody (config v) (contract v)
        (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I) ∅ vowTransition.body
        (.returned { contract := contract v, locals := ∅ }
          (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)
          (some [(.address (AccountAddress.ofNat
            (UInt256.land (solcSlotWord σ_solm I ⟨2⟩) solcAddrMask).toNat))])) := by
    simpa [solcSlotWord, initState, Solm.EVM.storageLoad, State.lookupAccount] using
      clipperVowBodyReturns v
        (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I) ∅
        (by simp only [initState]; exact hwv) (by simp)
  have hreach := clipperReachVowBody (cA := cA) (gh := gh) (bl := bl)
    (σ := σ_evm) (σ₀ := σ₀) (A := A) (I := I) (g := Sat256.ofUInt256 g)
    (v := v) hpatch hcode hwv hsz hsize hsel
  have hroutine : (D_J code 0).contains (⟨3325⟩ : UInt256) = true := by
    exact clipperJumpDest3325 v hpatch
  exact clipperAddressGetterBodyCore (v := v) (code := code) (cA := cA) (gh := gh)
    (bl := bl) (σ_evm := σ_evm) (σ_solm := σ_solm) (σ₀ := σ₀) (A := A) (I := I)
    (g := g) (sel := clipperSelWord I) (transition := vowTransition)
    (entry := (⟨829⟩ : UInt256)) (routine := (⟨3325⟩ : UInt256))
    (slot := (⟨2⟩ : UInt256)) (returnPc := (⟨716⟩ : UInt256))
    hcode (clipperDispatch_vow v hsel) (clipperDecode_vow v hsz) hreach hAccounts
    (clipperVowGetterEntryWf v hpatch) (clipperVowSlotGetterWf v hpatch) hroutine
    (clipperJumpDestBeforeFirstPatch v hpatch (⟨716⟩ : UInt256) (by native_decide))
    (clipperReturnAddress716Wf v hpatch) (by rfl) hbody

end Benchmarks.Dss.Clipper
