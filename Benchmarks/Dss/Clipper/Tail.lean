import Benchmarks.Dss.Clipper.Fallback

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach Reasoning.Refinement
open Benchmarks.Dss.Clipper.Immutables

namespace Benchmarks.Dss.Clipper

set_option linter.unusedTactic false

theorem clipperTailSelectorWord {I : ExecutionEnv} (hsz : 4 ≤ I.calldata.size)
    (hsel : selIs I (clipperSelBytes 21)) :
    clipperSelWord I = clipperSelNat 21 := by
  simpa [clipperSelWord, solcSelectorWord, clipperSelNat] using
    solcSelectorWord_eq_of_beq I hsz 0x13 0xd8 0xc8 0x40 (clipperSelNat 21)
      (by native_decide) (by simpa [clipperSelBytes, selIs] using hsel)

theorem clipperDispatch_tail (v : ClipperImmutables) {I : ExecutionEnv}
    (hsel : selIs I (clipperSelBytes 21)) :
    dispatchMsg (contract v) I.calldata = some tailTransition := by
  refine dispatchMsg_eq_some_of_split (contract := contract v)
    (pre :=
      [activeTransition, bufTransition, calcTransition, chipTransition, chostTransition,
        countTransition, cuspTransition, denyTransition, dogTransition, fileUintTransition,
        fileAddressTransition, getStatusTransition, ilkTransition v, kickTransition v,
        kicksTransition, listTransition, redoTransition v, relyTransition, salesTransition,
        spotterTransition, stoppedTransition])
    (post :=
      [takeTransition v, tipTransition, upchostTransition v, vatTransition v, vowTransition,
        wardsTransition, yankTransition v])
    (ti := tailTransition) (cd := I.calldata) (by rfl) ?_ ?_ ?_ (by rfl)
  · rfl
  · intro t ht
    simp only [List.mem_cons, List.mem_nil_iff] at ht
    rcases ht with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | hfalse
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
    · cases hfalse
  · rw [selectorOf, tailSelectorBytes]
    simpa [clipperSelBytes] using hsel

theorem clipperDecode_tail (v : ClipperImmutables) {I : ExecutionEnv}
    (hsz : 4 ≤ I.calldata.size) :
    decodeCalldataWithMode (config v).abiDecodeMode (tailTransition.params.map Param.name)
      (transitionSignature tailTransition).paramTypes I.calldata = some ∅ := by
  show decodeCalldataWithMode (config v).abiDecodeMode [] [] I.calldata = some ∅
  exact decodeCalldataWithMode_empty_ok hsz

theorem clipperEvalTail (v : ClipperImmutables) (evm : EVM.State) (locals : Store)
    (hbase : locals.get? "tail" = none) :
    evalExpr? (config v) { contract := contract v, locals := locals } evm
      (.storage tailRef) =
      .ok (.int (Int.ofNat (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨6⟩).toNat)) := by
  let er : EvaledStorageRef := { base := "tail", steps := [] }
  have her : evalStorageRef (config v)
      { contract := contract v, locals := locals } evm tailRef = .ok er := by
    unfold evalStorageRef tailRef
    simp only [evalStorageRefSteps]
    rfl
  have hty : storageTypeAt? (contract v).storage er = some (.elem (.int uint256Int)) := by
    simp [er, storageTypeAt?, contract, storageDecls, uint256St]
  have hloc : (config v).storage.layout er = fun _ => some (wordLoc ⟨6⟩) := by
    funext evm'
    rfl
  exact evalExpr_storage_scalar_value hbase her hty hloc
    (clipperStorageLocLoad_uint256 evm ⟨6⟩)

theorem clipperTailBodyReturns (v : ClipperImmutables) (evm : EVM.State) (locals : Store)
    (h : evm.executionEnv.weiValue = ⟨0⟩) (hbase : locals.get? "tail" = none) :
    ExecTransitionBody (config v) (contract v) evm locals tailTransition.body
      (.returned { contract := contract v, locals := locals } evm
        (some [(.int (Int.ofNat
          (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨6⟩).toNat))])) := by
  simpa [tailTransition] using
    nonpayableReturnExprBodyReturns (cfg := config v) (contract := contract v) h
      (clipperEvalTail v evm locals hbase)

set_option maxHeartbeats 1000000 in
theorem clipperReachTailBody {cA gh bl σ σ₀ A I} {g : Sat256} (v : ClipperImmutables)
    {code : ByteArray} (hpatch : patchRuntime clipperBytecode (patches v) = some code)
    (hcode : I.code = code) (hwv : I.weiValue = ⟨0⟩)
    (hsz : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hsel : selIs I (clipperSelBytes 21)) :
    ∃ k C, RD code I g (initState cA gh bl σ σ₀ g A I) (⟨592⟩ : UInt256)
      [clipperSelWord I] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
  obtain ⟨_, _, h32⟩ := clipperReachRoot (cA := cA) (gh := gh) (bl := bl)
    (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := g) v hpatch hcode hwv hsz hsize
  have hword := clipperTailSelectorWord hsz hsel
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
  have h369 := clipperSplitTaken (pc := (⟨261⟩ : UInt256)) (pivot := clipperSelNat 9)
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
    (clipperJumpDestBeforeFirstPatch v hpatch (⟨369⟩ : UInt256) (by native_decide))
    (by simp)
  have h381 := clipperSplitNotTaken (pc := (⟨370⟩ : UInt256))
    (next := (⟨381⟩ : UInt256)) (pivot := clipperSelNat 21)
    (tgt := (⟨429⟩ : UInt256))
    (h369.jumpdest
      (by
          change decode code (⟨369⟩ : UInt256) = some (.JUMPDEST, .none)
          clipper_decode)
      (by simp))
    (by
        change decode code (⟨370⟩ : UInt256) = some (.DUP1, .none)
        clipper_decode)
    (by
        change decode code (selArmPush4Pc (⟨370⟩ : UInt256)) =
          some (.Push .PUSH4, some (clipperSelNat 21, 4))
        clipper_decode)
    (by
        change decode code (selArmEqPc (⟨370⟩ : UInt256)) = some (.GT, .none)
        clipper_decode)
    (by decide)
    (by
        change decode code (selArmPushTgtPc (⟨370⟩ : UInt256)) =
          some (.Push .PUSH2, some (⟨429⟩, 2))
        clipper_decode)
    (by
        change decode code (selArmJumpiPc (⟨370⟩ : UInt256) 2) = some (.JUMPI, .none)
        clipper_decode)
    (by rw [hword]; native_decide)
    (by native_decide)
    (by simp)
  have h592 := clipperArmTaken (pc := (⟨381⟩ : UInt256)) (sel := clipperSelNat 21)
    (tgt := (⟨592⟩ : UInt256)) h381
    (by
        change decode code (⟨381⟩ : UInt256) = some (.DUP1, .none)
        clipper_decode)
    (by
        change decode code (selArmPush4Pc (⟨381⟩ : UInt256)) =
          some (.Push .PUSH4, some (clipperSelNat 21, 4))
        clipper_decode)
    (by
        change decode code (selArmEqPc (⟨381⟩ : UInt256)) = some (.EQ, .none)
        clipper_decode)
    (by decide)
    (by
        change decode code (selArmPushTgtPc (⟨381⟩ : UInt256)) =
          some (.Push .PUSH2, some (⟨592⟩, 2))
        clipper_decode)
    (by
        change decode code (selArmJumpiPc (⟨381⟩ : UInt256) 2) = some (.JUMPI, .none)
        clipper_decode)
    (by rw [hword]; native_decide)
    (clipperJumpDestBeforeFirstPatch v hpatch (⟨592⟩ : UInt256) (by native_decide))
    (by simp)
  exact ⟨_, _, h592⟩

theorem clipperTailGetterEntryWf (v : ClipperImmutables) {code : ByteArray}
    (hpatch : patchRuntime clipperBytecode (patches v) = some code) :
    solcGetterEntryWf code (⟨592⟩ : UInt256) (⟨476⟩ : UInt256) (⟨1900⟩ : UInt256) := by
  unfold solcGetterEntryWf
  repeat' first | apply And.intro
  all_goals
    rw [clipperDecodeBeforeFirstPatch v hpatch _ (by native_decide)]
    native_decide

theorem clipperTailPatchesWindowDisjoint32 (v : ClipperImmutables) (lo hi : Nat)
    (hlo : lo ∈ [1900, 1901, 1902, 1903, 1904, 1905, 1906])
    (hhi : hi ∈ [1901, 1902, 1903, 1904, 1905, 1906, 1907]) :
    PatchesWindowDisjoint32 lo hi (patches v) := by
  unfold PatchesWindowDisjoint32 PatchWindowDisjoint32 patches patchesFrom offsets immValues
  simp only [List.foldrM_cons, List.foldrM_nil, List.lookup_cons]
  cases hIlk : wordBytes? v.ilk
  · simp [hIlk] at hlo hhi ⊢
  · simp [hIlk] at hlo hhi ⊢
    omega

theorem clipperTailSlotGetterWf (v : ClipperImmutables) {code : ByteArray}
    (hpatch : patchRuntime clipperBytecode (patches v) = some code) :
    solcWordSlotGetterWf code (⟨1900⟩ : UInt256) (⟨6⟩ : UInt256) := by
  unfold solcWordSlotGetterWf
  repeat' first | apply And.intro
  all_goals
    exact patchRuntime_decode_disjoint_of_decode_res hpatch
      (by
        apply clipperTailPatchesWindowDisjoint32 v <;> native_decide)
      (by
        apply clipperTailPatchesWindowDisjoint32 v <;> native_decide)
      (by native_decide)
      (by native_decide)
      (by native_decide)

theorem clipperJumpDest1900 (v : ClipperImmutables) {code : ByteArray}
    (hpatch : patchRuntime clipperBytecode (patches v) = some code) :
    (D_J code 0).contains (⟨1900⟩ : UInt256) = true := by
  apply patchRuntime_D_J_contains_of_patchScanReaches (fuel := 2000) hpatch
  unfold patches patchesFrom offsets immValues
  simp only [List.foldrM_cons, List.foldrM_nil, List.lookup_cons]
  cases hIlk : wordBytes? v.ilk with
  | none =>
      simp [hIlk]
      native_decide
  | some bs =>
      simp [hIlk]
      native_decide

theorem clipperTailBody (v : ClipperImmutables) {code : ByteArray}
    (hpatch : patchRuntime clipperBytecode (patches v) = some code)
    {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256}
    (hcode : I.code = code) (hsize : I.calldata.size < UInt256.size)
    (_hperm : I.perm = true) (hwv : I.weiValue = ⟨0⟩)
    (hsel : selIs I (clipperSelBytes 21))
    (hAccounts : accountMapEquiv σ_evm σ_solm) :
    runtimeEquivalenceFor (config v) (contract v) cA gh bl σ_evm σ_solm σ₀ g A I := by
  have hsz : 4 ≤ I.calldata.size :=
    calldata_size_ge_of_selIs I (clipperSelBytes 21) (by native_decide) hsel
  have hbody :
      ExecTransitionBody (config v) (contract v)
        (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I) ∅ tailTransition.body
        (.returned { contract := contract v, locals := ∅ }
          (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)
          (some [(.int (Int.ofNat (solcSlotWord σ_solm I ⟨6⟩).toNat))])) := by
    simpa [solcSlotWord, initState, Solm.EVM.storageLoad, State.lookupAccount] using
      clipperTailBodyReturns v
        (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I) ∅
        (by simp only [initState]; exact hwv) (by simp)
  have hreach := clipperReachTailBody (cA := cA) (gh := gh) (bl := bl)
    (σ := σ_evm) (σ₀ := σ₀) (A := A) (I := I) (g := Sat256.ofUInt256 g)
    (v := v) hpatch hcode hwv hsz hsize hsel
  have hroutine : (D_J code 0).contains (⟨1900⟩ : UInt256) = true := by
    exact clipperJumpDest1900 v hpatch
  exact clipperUint256GetterBodyCore (v := v) (code := code) (cA := cA) (gh := gh)
    (bl := bl) (σ_evm := σ_evm) (σ_solm := σ_solm) (σ₀ := σ₀) (A := A) (I := I)
    (g := g) (sel := clipperSelWord I) (transition := tailTransition)
    (entry := (⟨592⟩ : UInt256)) (routine := (⟨1900⟩ : UInt256))
    (slot := (⟨6⟩ : UInt256)) (returnPc := (⟨476⟩ : UInt256))
    hcode (clipperDispatch_tail v hsel) (clipperDecode_tail v hsz) hreach hAccounts
    (clipperTailGetterEntryWf v hpatch) (clipperTailSlotGetterWf v hpatch) hroutine
    (clipperJumpDestBeforeFirstPatch v hpatch (⟨476⟩ : UInt256) (by native_decide))
    (clipperReturnWord476Wf v hpatch) (by rfl) hbody

end Benchmarks.Dss.Clipper
