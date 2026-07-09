import Benchmarks.Dss.Clipper.Fallback

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach Reasoning.Refinement
open Benchmarks.Dss.Clipper.Immutables

namespace Benchmarks.Dss.Clipper

set_option linter.unusedTactic false

theorem clipperChipSelectorWord {I : ExecutionEnv} (hsz : 4 ≤ I.calldata.size)
    (hsel : selIs I (clipperSelBytes 3)) :
    clipperSelWord I = clipperSelNat 3 := by
  simpa [clipperSelWord, solcSelectorWord, clipperSelNat] using
    solcSelectorWord_eq_of_beq I hsz 0xb6 0x15 0x00 0xe4 (clipperSelNat 3)
      (by native_decide) (by simpa [clipperSelBytes, selIs] using hsel)

theorem clipperDispatch_chip (v : ClipperImmutables) {I : ExecutionEnv}
    (hsel : selIs I (clipperSelBytes 3)) :
    dispatchMsg (contract v) I.calldata = some chipTransition := by
  refine dispatchMsg_eq_some_of_split (contract := contract v)
    (pre := [activeTransition, bufTransition, calcTransition])
    (post :=
      [chostTransition, countTransition, cuspTransition, denyTransition, dogTransition,
        fileUintTransition, fileAddressTransition, getStatusTransition, ilkTransition v,
        kickTransition v, kicksTransition, listTransition, redoTransition v, relyTransition,
        salesTransition, spotterTransition, stoppedTransition, tailTransition, takeTransition v,
        tipTransition, upchostTransition v, vatTransition v, vowTransition, wardsTransition,
        yankTransition v])
    (ti := chipTransition) (cd := I.calldata) (by rfl) ?_ ?_ ?_ (by rfl)
  · rfl
  · intro t ht
    simp only [List.mem_cons, List.mem_nil_iff] at ht
    rcases ht with rfl | rfl | rfl | hfalse
    · rw [selectorOf, activeSelectorBytes, ← byteArray_eq_of_beq hsel]
      native_decide
    · rw [selectorOf, bufSelectorBytes, ← byteArray_eq_of_beq hsel]
      native_decide
    · rw [selectorOf, calcSelectorBytes, ← byteArray_eq_of_beq hsel]
      native_decide
    · cases hfalse
  · rw [selectorOf, chipSelectorBytes]
    simpa [clipperSelBytes] using hsel

theorem clipperDecode_chip (v : ClipperImmutables) {I : ExecutionEnv}
    (hsz : 4 ≤ I.calldata.size) :
    decodeCalldataWithMode (config v).abiDecodeMode (chipTransition.params.map Param.name)
      (transitionSignature chipTransition).paramTypes I.calldata = some ∅ := by
  show decodeCalldataWithMode (config v).abiDecodeMode [] [] I.calldata = some ∅
  exact decodeCalldataWithMode_empty_ok hsz

theorem clipperEvalChip (v : ClipperImmutables) (evm : EVM.State) (locals : Store)
    (hbase : locals.get? "chip" = none) :
    evalExpr? (config v) { contract := contract v, locals := locals } evm (.storage chipRef) =
      .ok (.int (Int.ofNat (UInt256.land
        (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨8⟩)
        (UInt256.ofNat (2 ^ 64 - 1))).toNat)) := by
  let er : EvaledStorageRef := { base := "chip", steps := [] }
  have her : evalStorageRef (config v)
      { contract := contract v, locals := locals } evm chipRef = .ok er := by
    unfold evalStorageRef chipRef
    simp only [evalStorageRefSteps]
    rfl
  have hty : storageTypeAt? (contract v).storage er = some (.elem (.int uint64Int)) := by
    simp [er, storageTypeAt?, contract, storageDecls, uint64St]
  have hloc :
      (config v).storage.layout er =
        fun _ => some (uint64Loc ⟨8⟩ ⟨0, by decide⟩ (by decide)) := by
    funext evm'
    rfl
  exact evalExpr_storage_scalar_value hbase her hty hloc
    (clipperStorageLocLoad_uint64 evm ⟨8⟩)

theorem clipperChipBodyReturns (v : ClipperImmutables) (evm : EVM.State) (locals : Store)
    (h : evm.executionEnv.weiValue = ⟨0⟩) (hbase : locals.get? "chip" = none) :
    ExecTransitionBody (config v) (contract v) evm locals chipTransition.body
      (.returned { contract := contract v, locals := locals } evm
        (some [(.int (Int.ofNat (UInt256.land
          (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨8⟩)
          (UInt256.ofNat (2 ^ 64 - 1))).toNat))])) := by
  simpa [chipTransition] using
    nonpayableReturnExprBodyReturns (cfg := config v) (contract := contract v) h
      (clipperEvalChip v evm locals hbase)

set_option maxHeartbeats 1000000 in
theorem clipperReachChipBody {cA gh bl σ σ₀ A I} {g : Sat256} (v : ClipperImmutables)
    {code : ByteArray} (hpatch : patchRuntime clipperBytecode (patches v) = some code)
    (hcode : I.code = code) (hwv : I.weiValue = ⟨0⟩)
    (hsz : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hsel : selIs I (clipperSelBytes 3)) :
    ∃ k C, RD code I g (initState cA gh bl σ σ₀ g A I) (⟨1258⟩ : UInt256)
      [clipperSelWord I] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
  obtain ⟨_, _, h32⟩ := clipperReachRoot (cA := cA) (gh := gh) (bl := bl)
    (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := g) v hpatch hcode hwv hsz hsize
  have hword := clipperChipSelectorWord hsz hsel
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
  have h1258 := clipperArmTaken (pc := (⟨114⟩ : UInt256)) (sel := clipperSelNat 3)
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
    (clipperJumpDestBeforeFirstPatch v hpatch (⟨1258⟩ : UInt256) (by native_decide))
    (by simp)
  exact ⟨_, _, h1258⟩

theorem clipperChipGetterEntryWf (v : ClipperImmutables) {code : ByteArray}
    (hpatch : patchRuntime clipperBytecode (patches v) = some code) :
    solcGetterEntryWf code (⟨1258⟩ : UInt256) (⟨1266⟩ : UInt256)
      (⟨6743⟩ : UInt256) := by
  unfold solcGetterEntryWf
  repeat' first | apply And.intro
  all_goals
    rw [clipperDecodeBeforeFirstPatch v hpatch _ (by native_decide)]
    native_decide

theorem clipperChipReturnMaskedWf (v : ClipperImmutables) {code : ByteArray}
    (hpatch : patchRuntime clipperBytecode (patches v) = some code) :
    clipperReturnMaskedFromMemWf code (⟨1266⟩ : UInt256)
      (UInt256.ofNat (2 ^ 64 - 1)) 8 .PUSH8 := by
  unfold clipperReturnMaskedFromMemWf
  repeat' first | apply And.intro
  all_goals
    first
    | native_decide
    | (rw [clipperDecodeBeforeFirstPatch v hpatch _ (by native_decide)]; native_decide)

theorem clipperChipPatchesWindowDisjoint32 (v : ClipperImmutables) (lo hi : Nat)
    (hwin : (lo, hi) ∈
      [(6743, 6744), (6744, 6744), (6744, 6745), (6745, 6746),
        (6746, 6747), (6747, 6747), (6747, 6748), (6748, 6756),
        (6756, 6757), (6757, 6757), (6757, 6758), (6758, 6758),
        (6758, 6759), (6759, 6759)]) :
    PatchesWindowDisjoint32 lo hi (patches v) := by
  unfold PatchesWindowDisjoint32 PatchWindowDisjoint32 patches patchesFrom offsets immValues
  simp only [List.foldrM_cons, List.foldrM_nil, List.lookup_cons]
  cases hIlk : wordBytes? v.ilk
  · simp [hIlk] at hwin ⊢
    try omega
  · simp [hIlk] at hwin ⊢
    try omega

theorem clipperChipSlotGetterWf (v : ClipperImmutables) {code : ByteArray}
    (hpatch : patchRuntime clipperBytecode (patches v) = some code) :
    clipperPackedUintSlotGetterWf code (⟨6743⟩ : UInt256) (⟨8⟩ : UInt256)
      (UInt256.ofNat (2 ^ 64 - 1)) 8 .PUSH8 := by
  unfold clipperPackedUintSlotGetterWf
  repeat' first | apply And.intro
  · exact patchRuntime_decode_disjoint_of_decode_res hpatch
      (by apply clipperChipPatchesWindowDisjoint32 v; native_decide)
      (by apply clipperChipPatchesWindowDisjoint32 v; native_decide)
      (by native_decide) (by native_decide) (by native_decide)
  · exact patchRuntime_decode_disjoint_of_decode_res hpatch
      (by apply clipperChipPatchesWindowDisjoint32 v; native_decide)
      (by apply clipperChipPatchesWindowDisjoint32 v; native_decide)
      (by native_decide) (by native_decide) (by native_decide)
  · exact patchRuntime_decode_disjoint_of_decode_res hpatch
      (by apply clipperChipPatchesWindowDisjoint32 v; native_decide)
      (by apply clipperChipPatchesWindowDisjoint32 v; native_decide)
      (by native_decide) (by native_decide) (by native_decide)
  · native_decide
  · exact patchRuntime_decode_disjoint_of_decode_res hpatch
      (by apply clipperChipPatchesWindowDisjoint32 v; native_decide)
      (by apply clipperChipPatchesWindowDisjoint32 v; native_decide)
      (by native_decide) (by native_decide) (by native_decide)
  · exact patchRuntime_decode_disjoint_of_decode_res hpatch
      (by apply clipperChipPatchesWindowDisjoint32 v; native_decide)
      (by apply clipperChipPatchesWindowDisjoint32 v; native_decide)
      (by native_decide) (by native_decide) (by native_decide)
  · exact patchRuntime_decode_disjoint_of_decode_res hpatch
      (by apply clipperChipPatchesWindowDisjoint32 v; native_decide)
      (by apply clipperChipPatchesWindowDisjoint32 v; native_decide)
      (by native_decide) (by native_decide) (by native_decide)
  · exact patchRuntime_decode_disjoint_of_decode_res hpatch
      (by apply clipperChipPatchesWindowDisjoint32 v; native_decide)
      (by apply clipperChipPatchesWindowDisjoint32 v; native_decide)
      (by native_decide) (by native_decide) (by native_decide)

theorem clipperJumpDest6743 (v : ClipperImmutables) {code : ByteArray}
    (hpatch : patchRuntime clipperBytecode (patches v) = some code) :
    (D_J code 0).contains (⟨6743⟩ : UInt256) = true := by
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

theorem clipperChipBody (v : ClipperImmutables) {code : ByteArray}
    (hpatch : patchRuntime clipperBytecode (patches v) = some code)
    {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256}
    (hcode : I.code = code) (hsize : I.calldata.size < UInt256.size)
    (_hperm : I.perm = true) (hwv : I.weiValue = ⟨0⟩)
    (hsel : selIs I (clipperSelBytes 3))
    (hAccounts : accountMapEquiv σ_evm σ_solm) :
    runtimeEquivalenceFor (config v) (contract v) cA gh bl σ_evm σ_solm σ₀ g A I := by
  have hsz : 4 ≤ I.calldata.size :=
    calldata_size_ge_of_selIs I (clipperSelBytes 3) (by native_decide) hsel
  have hbody :
      ExecTransitionBody (config v) (contract v)
        (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I) ∅ chipTransition.body
        (.returned { contract := contract v, locals := ∅ }
          (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)
          (some [(.int (Int.ofNat (UInt256.land (solcSlotWord σ_solm I ⟨8⟩)
            (UInt256.ofNat (2 ^ 64 - 1))).toNat))])) := by
    simpa [solcSlotWord, initState, Solm.EVM.storageLoad, State.lookupAccount] using
      clipperChipBodyReturns v
        (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I) ∅
        (by simp only [initState]; exact hwv) (by simp)
  have hword : solcSlotWord σ_evm I ⟨8⟩ = solcSlotWord σ_solm I ⟨8⟩ :=
    accountMapEquiv_storage_findD hAccounts I.codeOwner ⟨8⟩ ⟨0⟩
  have hval :
      some [Value.int (Int.ofNat
          (UInt256.land (solcSlotWord σ_solm I ⟨8⟩)
            (UInt256.ofNat (2 ^ 64 - 1))).toNat)] =
        some [Value.int (Int.ofNat
          (UInt256.land (solcSlotWord σ_evm I ⟨8⟩)
            (UInt256.ofNat (2 ^ 64 - 1))).toNat)] := by
    rw [hword]
  have henc :
      returnEquiv
        (UInt256.toByteArray
          (UInt256.land (solcSlotWord σ_evm I ⟨8⟩) (UInt256.ofNat (2 ^ 64 - 1))))
        (some [(.int (Int.ofNat
          (UInt256.land (solcSlotWord σ_evm I ⟨8⟩)
            (UInt256.ofNat (2 ^ 64 - 1))).toNat))])
        chipTransition.returnType := by
    rw [show chipTransition.returnType = [uint64] from rfl]
    exact returnEquiv_of_encode
      (by
        simpa [uint64] using
          uintReturnEncoding ⟨64, by decide⟩
            (UInt256.land (solcSlotWord σ_evm I ⟨8⟩) (UInt256.ofNat (2 ^ 64 - 1)))
            (u256LandMaskToNatLtOfToNat (solcSlotWord σ_evm I ⟨8⟩)
              (UInt256.ofNat (2 ^ 64 - 1)) (by native_decide)))
  have hreach := clipperReachChipBody (cA := cA) (gh := gh) (bl := bl)
    (σ := σ_evm) (σ₀ := σ₀) (A := A) (I := I) (g := Sat256.ofUInt256 g)
    (v := v) hpatch hcode hwv hsz hsize hsel
  have hret := clipperPackedUintGetterExternal (code := code) (cA := cA) (gh := gh)
    (bl := bl) (σ := σ_evm) (σ₀ := σ₀) (A := A) (I := I)
    (g := Sat256.ofUInt256 g) (sel := clipperSelWord I) (entry := (⟨1258⟩ : UInt256))
    (routine := (⟨6743⟩ : UInt256)) (slot := (⟨8⟩ : UInt256))
    (returnPc := (⟨1266⟩ : UInt256)) (mask := UInt256.ofNat (2 ^ 64 - 1))
    (bits := 64) (width := 8) (op := .PUSH8) hreach
    (clipperChipGetterEntryWf v hpatch) (clipperChipSlotGetterWf v hpatch)
    (by native_decide) (clipperJumpDest6743 v hpatch)
    (clipperJumpDestBeforeFirstPatch v hpatch (⟨1266⟩ : UInt256) (by native_decide))
    (clipperChipReturnMaskedWf v hpatch)
  exact hret.reEquivExecutionTransport hcode (clipperDispatch_chip v hsel)
    (clipperDecode_chip v hsz) hbody hval hAccounts henc

end Benchmarks.Dss.Clipper
