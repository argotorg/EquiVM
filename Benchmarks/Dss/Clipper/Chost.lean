import Benchmarks.Dss.Clipper.Fallback

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Benchmarks.Dss.Clipper.Immutables

namespace Benchmarks.Dss.Clipper

set_option linter.unusedTactic false

theorem clipperChostSelectorWord {I : ExecutionEnv} (hsz : 4 ≤ I.calldata.size)
    (hsel : selIs I (clipperSelBytes 4)) :
    clipperSelWord I = clipperSelNat 4 := by
  simpa [clipperSelWord, solcSelectorWord, clipperSelNat] using
    solcSelectorWord_eq_of_beq I hsz 0xba 0x2c 0xdc 0x75 (clipperSelNat 4)
      (by decide +native) (by simpa [clipperSelBytes, selIs] using hsel)

theorem clipperDispatch_chost (v : ClipperImmutables) {I : ExecutionEnv}
    (hsel : selIs I (clipperSelBytes 4)) :
    dispatchMsg (contract v) I.calldata = some chostTransition := by
  refine dispatchMsg_eq_some_of_split (contract := contract v)
    (pre := [activeTransition, bufTransition, calcTransition, chipTransition])
    (post :=
      [countTransition, cuspTransition, denyTransition, dogTransition, fileUintTransition,
        fileAddressTransition, getStatusTransition, ilkTransition v, kickTransition v,
        kicksTransition, listTransition, redoTransition v, relyTransition, salesTransition,
        spotterTransition, stoppedTransition, tailTransition, takeTransition v, tipTransition,
        upchostTransition v, vatTransition v, vowTransition, wardsTransition, yankTransition v])
    (ti := chostTransition) (cd := I.calldata) (by rfl) ?_ ?_ ?_ (by rfl)
  · rfl
  · intro t ht
    simp only [List.mem_cons, List.mem_nil_iff] at ht
    rcases ht with rfl | rfl | rfl | rfl | hfalse
    · rw [selectorOf, activeSelectorBytes, ← byteArray_eq_of_beq hsel]
      decide +native
    · rw [selectorOf, bufSelectorBytes, ← byteArray_eq_of_beq hsel]
      decide +native
    · rw [selectorOf, calcSelectorBytes, ← byteArray_eq_of_beq hsel]
      decide +native
    · rw [selectorOf, chipSelectorBytes, ← byteArray_eq_of_beq hsel]
      decide +native
    · cases hfalse
  · rw [selectorOf, chostSelectorBytes]
    simpa [clipperSelBytes] using hsel

theorem clipperDecode_chost (v : ClipperImmutables) {I : ExecutionEnv}
    (hsz : 4 ≤ I.calldata.size) :
    decodeCalldataWithMode (config v).abiDecodeMode (chostTransition.params.map Param.name)
      (transitionSignature chostTransition).paramTypes I.calldata = some ∅ := by
  show decodeCalldataWithMode (config v).abiDecodeMode [] [] I.calldata = some ∅
  exact decodeCalldataWithMode_empty_ok hsz

theorem clipperEvalChost (v : ClipperImmutables) (evm : EVM.State) (locals : Store)
    (hbase : locals.get? "chost" = none) :
    evalExpr? (config v) { contract := contract v, locals := locals } evm
      (.storage chostRef) =
      .ok (.int (Int.ofNat (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨9⟩).toNat)) := by
  let er : EvaledStorageRef := { base := "chost", steps := [] }
  have her : evalStorageRef (config v)
      { contract := contract v, locals := locals } evm chostRef = .ok er := by
    unfold evalStorageRef chostRef
    simp only [evalStorageRefSteps]
    rfl
  have hty : storageTypeAt? (contract v).storage er = some (.elem (.int uint256Int)) := by
    simp [er, storageTypeAt?, contract, storageDecls, uint256St]
  have hloc : (config v).storage.layout er = fun _ => some (wordLoc ⟨9⟩) := by
    funext evm'
    rfl
  exact evalExpr_storage_scalar_value hbase her hty hloc
    (clipperStorageLocLoad_uint256 evm ⟨9⟩)

theorem clipperChostBodyReturns (v : ClipperImmutables) (evm : EVM.State) (locals : Store)
    (h : evm.executionEnv.weiValue = ⟨0⟩) (hbase : locals.get? "chost" = none) :
    ExecTransitionBody (config v) (contract v) evm locals chostTransition.body
      (.returned { contract := contract v, locals := locals } evm
        (some [(.int (Int.ofNat
          (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨9⟩).toNat))])) := by
  simpa [chostTransition] using
    nonpayableReturnExprBodyReturns (cfg := config v) (contract := contract v) h
      (clipperEvalChost v evm locals hbase)

set_option maxHeartbeats 1000000 in
theorem clipperReachChostBody {cA gh bl σ σ₀ A I} {g : Sat256} (v : ClipperImmutables)
    {code : ByteArray} (hpatch : patchRuntime clipperBytecode (patches v) = some code)
    (hcode : I.code = code) (hwv : I.weiValue = ⟨0⟩)
    (hsz : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hsel : selIs I (clipperSelBytes 4)) :
    ∃ k C, RD code I g (initState cA gh bl σ σ₀ g A I) (⟨1295⟩ : UInt256)
      [clipperSelWord I] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
  obtain ⟨_, _, h32⟩ := clipperReachRoot (cA := cA) (gh := gh) (bl := bl)
    (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := g) v hpatch hcode hwv hsz hsize
  have hword := clipperChostSelectorWord hsz hsel
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
    (by rw [hword]; decide +native)
    (by decide +native)
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
    (by rw [hword]; decide +native)
    (by decide +native)
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
    (by rw [hword]; decide +native)
    (clipperJumpDestBeforeFirstPatch v hpatch (⟨113⟩ : UInt256) (by decide +native))
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
    (by rw [hword]; decide +native)
    (by decide +native)
    (by simp)
  have h1295 := clipperArmTaken (pc := (⟨125⟩ : UInt256)) (sel := clipperSelNat 4)
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
    (by rw [hword]; decide +native)
    (clipperJumpDestBeforeFirstPatch v hpatch (⟨1295⟩ : UInt256) (by decide +native))
    (by simp)
  exact ⟨_, _, h1295⟩

theorem clipperChostGetterEntryWf (v : ClipperImmutables) {code : ByteArray}
    (hpatch : patchRuntime clipperBytecode (patches v) = some code) :
    solcGetterEntryWf code (⟨1295⟩ : UInt256) (⟨476⟩ : UInt256) (⟨6759⟩ : UInt256) := by
  unfold solcGetterEntryWf
  repeat' first | apply And.intro
  all_goals
    rw [clipperDecodeBeforeFirstPatch v hpatch _ (by decide +native)]
    decide +native

theorem clipperChostPatchesWindowDisjoint32 (v : ClipperImmutables) (lo hi : Nat)
    (hlo : lo ∈ [6759, 6760, 6761, 6762, 6763, 6764, 6765])
    (hhi : hi ∈ [6760, 6761, 6762, 6763, 6764, 6765, 6766]) :
    PatchesWindowDisjoint32 lo hi (patches v) := by
  unfold PatchesWindowDisjoint32 PatchWindowDisjoint32 patches patchesFrom offsets immValues
  simp only [List.foldrM_cons, List.foldrM_nil, List.lookup_cons]
  cases hIlk : wordBytes? v.ilk
  · simp [hIlk] at hlo hhi ⊢
  · simp [hIlk] at hlo hhi ⊢
    omega

theorem clipperChostSlotGetterWf (v : ClipperImmutables) {code : ByteArray}
    (hpatch : patchRuntime clipperBytecode (patches v) = some code) :
    solcWordSlotGetterWf code (⟨6759⟩ : UInt256) (⟨9⟩ : UInt256) := by
  unfold solcWordSlotGetterWf
  repeat' first | apply And.intro
  all_goals
    exact patchRuntime_decode_disjoint_of_decode_res hpatch
      (by
        apply clipperChostPatchesWindowDisjoint32 v <;> decide +native)
      (by
        apply clipperChostPatchesWindowDisjoint32 v <;> decide +native)
      (by decide +native)
      (by decide +native)
      (by decide +native)

theorem clipperJumpDest6759 (v : ClipperImmutables) {code : ByteArray}
    (hpatch : patchRuntime clipperBytecode (patches v) = some code) :
    (D_J code 0).contains (⟨6759⟩ : UInt256) = true := by
  apply patchRuntime_D_J_contains_of_patchScanReaches (fuel := 7000) hpatch
  unfold patches patchesFrom offsets immValues
  simp only [List.foldrM_cons, List.foldrM_nil, List.lookup_cons]
  cases hIlk : wordBytes? v.ilk with
  | none =>
      simp [hIlk]
      decide +native
  | some bs =>
      simp [hIlk]
      decide +native

theorem clipperChostBody (v : ClipperImmutables) {code : ByteArray}
    (hpatch : patchRuntime clipperBytecode (patches v) = some code)
    {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256}
    (hcode : I.code = code) (hsize : I.calldata.size < UInt256.size)
    (_hperm : I.perm = true) (hwv : I.weiValue = ⟨0⟩)
    (hsel : selIs I (clipperSelBytes 4))
    (hAccounts : accountMapEquiv σ_evm σ_solm) :
    runtimeEquivalenceFor (config v) (contract v) cA gh bl σ_evm σ_solm σ₀ g A I := by
  have hsz : 4 ≤ I.calldata.size :=
    calldata_size_ge_of_selIs I (clipperSelBytes 4) (by decide +native) hsel
  have hbody :
      ExecTransitionBody (config v) (contract v)
        (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I) ∅ chostTransition.body
        (.returned { contract := contract v, locals := ∅ }
          (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)
          (some [(.int (Int.ofNat (solcSlotWord σ_solm I ⟨9⟩).toNat))])) := by
    simpa [solcSlotWord, initState, Solm.EVM.storageLoad, State.lookupAccount] using
      clipperChostBodyReturns v
        (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I) ∅
        (by simp only [initState]; exact hwv) (by simp)
  have hreach := clipperReachChostBody (cA := cA) (gh := gh) (bl := bl)
    (σ := σ_evm) (σ₀ := σ₀) (A := A) (I := I) (g := Sat256.ofUInt256 g)
    (v := v) hpatch hcode hwv hsz hsize hsel
  have hroutine : (D_J code 0).contains (⟨6759⟩ : UInt256) = true := by
    exact clipperJumpDest6759 v hpatch
  exact clipperUint256GetterBodyCore (v := v) (code := code) (cA := cA) (gh := gh)
    (bl := bl) (σ_evm := σ_evm) (σ_solm := σ_solm) (σ₀ := σ₀) (A := A) (I := I)
    (g := g) (sel := clipperSelWord I) (transition := chostTransition)
    (entry := (⟨1295⟩ : UInt256)) (routine := (⟨6759⟩ : UInt256))
    (slot := (⟨9⟩ : UInt256)) (returnPc := (⟨476⟩ : UInt256))
    hcode (clipperDispatch_chost v hsel) (clipperDecode_chost v hsz) hreach hAccounts
    (clipperChostGetterEntryWf v hpatch) (clipperChostSlotGetterWf v hpatch) hroutine
    (clipperJumpDestBeforeFirstPatch v hpatch (⟨476⟩ : UInt256) (by decide +native))
    (clipperReturnWord476Wf v hpatch) (by rfl) hbody

end Benchmarks.Dss.Clipper
