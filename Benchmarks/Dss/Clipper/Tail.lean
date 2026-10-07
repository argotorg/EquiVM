import Benchmarks.Dss.Clipper.Fallback

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Benchmarks.Dss.Clipper.Immutables

namespace Benchmarks.Dss.Clipper

set_option linter.unusedTactic false

theorem clipperTailSelectorWord {I : ExecutionEnv} (hsz : 4 ≤ I.calldata.size)
    (hsel : selIs I (clipperSelBytes 21)) :
    clipperSelWord I = clipperSelNat 21 := by
  simpa [clipperSelWord, solcSelectorWord, clipperSelNat] using
    solcSelectorWord_eq_of_beq I hsz 0x13 0xd8 0xc8 0x40 (clipperSelNat 21)
      (by native_decide) (by simpa [clipperSelBytes, selIs] using hsel)

theorem clipperDispatch_tail {I : ExecutionEnv}
    (hsel : selIs I (clipperSelBytes 21)) :
    dispatchMsg contract I.calldata = some tailTransition := by
  refine dispatchMsg_eq_some_of_split (contract := contract)
    (pre :=
      [activeTransition, bufTransition, calcTransition, chipTransition, chostTransition,
        countTransition, cuspTransition, denyTransition, dogTransition, fileUintTransition,
        fileAddressTransition, getStatusTransition, ilkTransition, kickTransition,
        kicksTransition, listTransition, redoTransition, relyTransition, salesTransition,
        spotterTransition, stoppedTransition])
    (post :=
      [takeTransition, tipTransition, upchostTransition, vatTransition, vowTransition,
        wardsTransition, yankTransition])
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
    · rw [selectorOf, ilkSelectorBytes, ← byteArray_eq_of_beq hsel]
      native_decide
    · rw [selectorOf, kickSelectorBytes, ← byteArray_eq_of_beq hsel]
      native_decide
    · rw [selectorOf, kicksSelectorBytes, ← byteArray_eq_of_beq hsel]
      native_decide
    · rw [selectorOf, listSelectorBytes, ← byteArray_eq_of_beq hsel]
      native_decide
    · rw [selectorOf, redoSelectorBytes, ← byteArray_eq_of_beq hsel]
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

theorem clipperDecode_tail {I : ExecutionEnv}
    (hsz : 4 ≤ I.calldata.size) :
    decodeCalldataWithMode config.abiDecodeMode (tailTransition.params.map Param.name)
      (transitionSignature tailTransition).paramTypes I.calldata = some ∅ := by
  show decodeCalldataWithMode config.abiDecodeMode [] [] I.calldata = some ∅
  exact decodeCalldataWithMode_empty_ok hsz

theorem clipperEvalTail (v : ClipperImmutables) (evm : EVM.State) (locals : Store)
    (hbase : locals.get? "tail" = none) :
    evalExpr? config { contract := contract, locals := locals, immutables := immStore v } evm
      (.storage tailRef) =
      .ok (.int (Int.ofNat (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨6⟩).toNat)) := by
  let er : EvaledStorageRef := { base := "tail", steps := [] }
  have her : evalStorageRef config
      { contract := contract, locals := locals, immutables := immStore v } evm tailRef = .ok er := by
    unfold evalStorageRef tailRef
    simp only [evalStorageRefSteps]
    rfl
  have hty : storageTypeAt? contract.storage er = some (.elem (.int uint256Int)) := by
    simp [er, storageTypeAt?, contract, storageDecls, uint256St]
  have hloc : config.storageBackend.locate? er = some (.leaf (wordLoc ⟨6⟩)) := by
    rfl
  exact evalExpr_storage_scalar_value (hbackend := rfl) hbase her hty hloc
    (storageLocLoad_uint256 evm ⟨6⟩)

theorem clipperTailBodyReturns (v : ClipperImmutables) (evm : EVM.State) (locals : Store)
    (h : evm.executionEnv.weiValue = ⟨0⟩) (hbase : locals.get? "tail" = none) :
    ExecTransitionBody config contract evm locals tailTransition.body
      (.returned { contract := contract, locals := locals, immutables := immStore v } evm
        (some [(.int (Int.ofNat
          (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨6⟩).toNat))])) (immStore v) := by
  simpa [tailTransition] using
    nonpayableReturnExprBodyReturns (cfg := config) (contract := contract) h
      (clipperEvalTail v evm locals hbase)

set_option maxHeartbeats 1000000 in
theorem clipperReachTailBody {σ σ₀ A I} {g : Sat256} (v : ClipperImmutables)
    {code : ByteArray} (hpatch : patchRuntime clipperBytecode (patches v) = some code)
    (hcode : I.code = code) (hwv : I.weiValue = ⟨0⟩)
    (hsz : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hsel : selIs I (clipperSelBytes 21)) :
    ∃ k C, RD code I g (initState σ σ₀ g A I) (⟨592⟩ : UInt256)
      [clipperSelWord I] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty σ k C := by
  obtain ⟨_, _, h32⟩ := clipperReachRoot
    (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := g) v hpatch hcode hwv hsz hsize
  have hword := clipperTailSelectorWord hsz hsel
  have h260 := RD.selectorSplitTakenPush2 (pc := (⟨32⟩ : UInt256)) (pivot := clipperSelNat 20)
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
  have h369 := RD.selectorSplitTakenPush2 (pc := (⟨261⟩ : UInt256)) (pivot := clipperSelNat 9)
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
  have h381 := RD.selectorSplitNotTakenPush2 (pc := (⟨370⟩ : UInt256))
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
  have h592 := RD.selectorArmTakenPush2 (pc := (⟨381⟩ : UInt256)) (sel := clipperSelNat 21)
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
  cases hIlk : Reasoning.Theory.wordBytes? v.ilk
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
  cases hIlk : Reasoning.Theory.wordBytes? v.ilk with
  | none =>
      simp [hIlk]
      native_decide
  | some bs =>
      simp [hIlk]
      native_decide

theorem clipperTailBody (v : ClipperImmutables) {code : ByteArray}
    (hpatch : patchRuntime clipperBytecode (patches v) = some code)
    {σ σ₀ A I} {g : UInt256}
    (hcode : I.code = code) (hsize : I.calldata.size < UInt256.size)
    (hwv : I.weiValue = ⟨0⟩)
    (hsel : selIs I (clipperSelBytes 21)) :
    runtimeRefinementFor config contract σ σ₀ g A I (immStore v) := by
  have hsz : 4 ≤ I.calldata.size :=
    calldata_size_ge_of_selIs I (clipperSelBytes 21) (by native_decide) hsel
  have hbody :
      ExecTransitionBody config contract
        (initState σ σ₀ (Sat256.ofUInt256 g) A I) ∅ tailTransition.body
        (.returned { contract := contract, locals := ∅, immutables := immStore v }
          (initState σ σ₀ (Sat256.ofUInt256 g) A I)
          (some [(.int (Int.ofNat (solcSlotWord σ I ⟨6⟩).toNat))])) (immStore v) := by
    simpa [solcSlotWord, initState, Solm.EVM.storageLoad, State.lookupAccount] using
      clipperTailBodyReturns v
        (initState σ σ₀ (Sat256.ofUInt256 g) A I) ∅
        (by simp only [initState]; exact hwv) (by simp)
  have hreach := clipperReachTailBody
    (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := Sat256.ofUInt256 g)
    (v := v) hpatch hcode hwv hsz hsize hsel
  have hroutine : (D_J code 0).contains (⟨1900⟩ : UInt256) = true := by
    exact clipperJumpDest1900 v hpatch
  exact clipperUint256GetterBodyCore (v := v) (code := code)
    (σ := σ) (σ₀ := σ₀) (A := A) (I := I)
    (g := g) (sel := clipperSelWord I) (transition := tailTransition)
    (entry := (⟨592⟩ : UInt256)) (routine := (⟨1900⟩ : UInt256))
    (slot := (⟨6⟩ : UInt256)) (returnPc := (⟨476⟩ : UInt256))
    hcode (clipperDispatch_tail hsel) (clipperDecode_tail hsz) hreach
    (clipperTailGetterEntryWf v hpatch) (clipperTailSlotGetterWf v hpatch) hroutine
    (clipperJumpDestBeforeFirstPatch v hpatch (⟨476⟩ : UInt256) (by native_decide))
    (clipperReturnWord476Wf v hpatch) (by rfl) hbody

end Benchmarks.Dss.Clipper
