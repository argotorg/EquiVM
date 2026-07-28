import Benchmarks.Dss.Clipper.Fallback

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Benchmarks.Dss.Clipper.Immutables

namespace Benchmarks.Dss.Clipper

set_option linter.unusedTactic false

theorem clipperCalcSelectorWord {I : ExecutionEnv} (hsz : 4 ≤ I.calldata.size)
    (hsel : selIs I (clipperSelBytes 2)) :
    clipperSelWord I = clipperSelNat 2 := by
  simpa [clipperSelWord, solcSelectorWord, clipperSelNat] using
    solcSelectorWord_eq_of_beq I hsz 0x96 0xf1 0xb6 0xbe (clipperSelNat 2)
      (by native_decide) (by simpa [clipperSelBytes, selIs] using hsel)

theorem clipperDispatch_calc (v : ClipperImmutables) {I : ExecutionEnv}
    (hsel : selIs I (clipperSelBytes 2)) :
    dispatchMsg (contract v) I.calldata = some calcTransition := by
  refine dispatchMsg_eq_some_of_split (contract := contract v)
    (pre := [activeTransition, bufTransition])
    (post :=
      [chipTransition, chostTransition, countTransition, cuspTransition, denyTransition,
        dogTransition, fileUintTransition, fileAddressTransition, getStatusTransition,
        ilkTransition v, kickTransition v, kicksTransition, listTransition, redoTransition v,
        relyTransition, salesTransition, spotterTransition, stoppedTransition, tailTransition,
        takeTransition v, tipTransition, upchostTransition v, vatTransition v, vowTransition,
        wardsTransition, yankTransition v])
    (ti := calcTransition) (cd := I.calldata) (by rfl) ?_ ?_ ?_ (by rfl)
  · rfl
  · intro t ht
    simp only [List.mem_cons, List.mem_nil_iff] at ht
    rcases ht with rfl | rfl | hfalse
    · rw [selectorOf, activeSelectorBytes, ← byteArray_eq_of_beq hsel]
      native_decide
    · rw [selectorOf, bufSelectorBytes, ← byteArray_eq_of_beq hsel]
      native_decide
    · cases hfalse
  · rw [selectorOf, calcSelectorBytes]
    simpa [clipperSelBytes] using hsel

theorem clipperDecode_calc (v : ClipperImmutables) {I : ExecutionEnv}
    (hsz : 4 ≤ I.calldata.size) :
    decodeCalldataWithMode (config v).abiDecodeMode (calcTransition.params.map Param.name)
      (transitionSignature calcTransition).paramTypes I.calldata = some ∅ := by
  show decodeCalldataWithMode (config v).abiDecodeMode [] [] I.calldata = some ∅
  exact decodeCalldataWithMode_empty_ok hsz

theorem clipperEvalCalc (v : ClipperImmutables) (evm : EVM.State) (locals : Store)
    (hbase : locals.get? "calc" = none) :
    evalExpr? (config v) { contract := contract v, locals := locals } evm
      (.storage calcRef) =
      .ok (.address (AccountAddress.ofNat
        (UInt256.land (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨4⟩)
          solcAddrMask).toNat)) := by
  let er : EvaledStorageRef := { base := "calc", steps := [] }
  have her : evalStorageRef (config v)
      { contract := contract v, locals := locals } evm calcRef = .ok er := by
    unfold evalStorageRef calcRef
    simp only [evalStorageRefSteps]
    rfl
  have hty : storageTypeAt? (contract v).storage er = some (.elem .address) := by
    simp [er, storageTypeAt?, contract, storageDecls, addrSt]
  have hloc : (config v).storage.layout er = fun _ => some (addrLoc ⟨4⟩) := by
    funext evm'
    rfl
  exact evalExpr_storage_scalar_value hbase her hty hloc
    (clipperStorageLocLoad_address evm ⟨4⟩)

theorem clipperCalcBodyReturns (v : ClipperImmutables) (evm : EVM.State) (locals : Store)
    (h : evm.executionEnv.weiValue = ⟨0⟩) (hbase : locals.get? "calc" = none) :
    ExecTransitionBody (config v) (contract v) evm locals calcTransition.body
      (.returned { contract := contract v, locals := locals } evm
        (some [(.address (AccountAddress.ofNat
          (UInt256.land (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨4⟩)
            solcAddrMask).toNat))])) := by
  simpa [calcTransition] using
    nonpayableReturnExprBodyReturns (cfg := config v) (contract := contract v) h
      (clipperEvalCalc v evm locals hbase)

set_option maxHeartbeats 1000000 in
theorem clipperReachCalcBody {cA gh bl σ σ₀ A I} {g : Sat256}
    (v : ClipperImmutables)
    {code : ByteArray} (hpatch : patchRuntime clipperBytecode (patches v) = some code)
    (hcode : I.code = code) (hwv : I.weiValue = ⟨0⟩)
    (hsz : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hsel : selIs I (clipperSelBytes 2)) :
    ∃ k C, RD code I g (initState cA gh bl σ σ₀ g A I) (⟨1115⟩ : UInt256)
      [clipperSelWord I] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
  obtain ⟨_, _, h32⟩ := clipperReachRoot (cA := cA) (gh := gh) (bl := bl)
    (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := g) v hpatch hcode hwv hsz hsize
  have hword := clipperCalcSelectorWord hsz hsel
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
  have h162 := clipperSplitTaken (pc := (⟨43⟩ : UInt256))
    (pivot := clipperSelNat 3) (tgt := (⟨162⟩ : UInt256)) h43
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
  have h174 := clipperSplitNotTaken (pc := (⟨163⟩ : UInt256))
    (next := (⟨174⟩ : UInt256)) (pivot := clipperSelNat 13)
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
    (by native_decide)
    (by simp)
  have h185 := clipperArmNotTaken (pc := (⟨174⟩ : UInt256))
    (next := (⟨185⟩ : UInt256)) (sel := clipperSelNat 13)
    (tgt := (⟨1057⟩ : UInt256)) h174
    (by
        change decode code (⟨174⟩ : UInt256) = some (.DUP1, .none)
        clipper_decode)
    (by
        change decode code (selArmPush4Pc (⟨174⟩ : UInt256)) =
          some (.Push .PUSH4, some (clipperSelNat 13, 4))
        clipper_decode)
    (by
        change decode code (selArmEqPc (⟨174⟩ : UInt256)) = some (.EQ, .none)
        clipper_decode)
    (by decide)
    (by
        change decode code (selArmPushTgtPc (⟨174⟩ : UInt256)) =
          some (.Push .PUSH2, some (⟨1057⟩, 2))
        clipper_decode)
    (by
        change decode code (selArmJumpiPc (⟨174⟩ : UInt256) 2) = some (.JUMPI, .none)
        clipper_decode)
    (by rw [hword]; native_decide)
    (by native_decide)
    (by simp)
  have h1115 := clipperArmTaken (pc := (⟨185⟩ : UInt256)) (sel := clipperSelNat 2)
    (tgt := (⟨1115⟩ : UInt256)) h185
    (by
        change decode code (⟨185⟩ : UInt256) = some (.DUP1, .none)
        clipper_decode)
    (by
        change decode code (selArmPush4Pc (⟨185⟩ : UInt256)) =
          some (.Push .PUSH4, some (clipperSelNat 2, 4))
        clipper_decode)
    (by
        change decode code (selArmEqPc (⟨185⟩ : UInt256)) = some (.EQ, .none)
        clipper_decode)
    (by decide)
    (by
        change decode code (selArmPushTgtPc (⟨185⟩ : UInt256)) =
          some (.Push .PUSH2, some (⟨1115⟩, 2))
        clipper_decode)
    (by
        change decode code (selArmJumpiPc (⟨185⟩ : UInt256) 2) = some (.JUMPI, .none)
        clipper_decode)
    (by rw [hword]; native_decide)
    (clipperJumpDestBeforeFirstPatch v hpatch (⟨1115⟩ : UInt256) (by native_decide))
    (by simp)
  exact ⟨_, _, h1115⟩

theorem clipperCalcGetterEntryWf (v : ClipperImmutables) {code : ByteArray}
    (hpatch : patchRuntime clipperBytecode (patches v) = some code) :
    solcGetterEntryWf code (⟨1115⟩ : UInt256) (⟨716⟩ : UInt256) (⟨6503⟩ : UInt256) := by
  unfold solcGetterEntryWf
  repeat' first | apply And.intro
  all_goals
    rw [clipperDecodeBeforeFirstPatch v hpatch _ (by native_decide)]
    native_decide

theorem clipperCalcPatchesWindowDisjoint32 (v : ClipperImmutables) (lo hi : Nat)
    (hlo : lo ∈ [6503, 6504, 6505, 6506, 6507, 6508, 6509, 6510, 6511, 6512,
      6513, 6514, 6515, 6516, 6517, 6518])
    (hhi : hi ∈ [6504, 6505, 6506, 6507, 6508, 6509, 6510, 6511, 6512,
      6513, 6514, 6515, 6516, 6517, 6518, 6519]) :
    PatchesWindowDisjoint32 lo hi (patches v) := by
  unfold PatchesWindowDisjoint32 PatchWindowDisjoint32 patches patchesFrom offsets immValues
  simp only [List.foldrM_cons, List.foldrM_nil, List.lookup_cons]
  cases hIlk : wordBytes? v.ilk
  · simp [hIlk] at hlo hhi ⊢
  · simp [hIlk] at hlo hhi ⊢
    omega

theorem clipperCalcSlotGetterWf (v : ClipperImmutables) {code : ByteArray}
    (hpatch : patchRuntime clipperBytecode (patches v) = some code) :
    solcAddressSlotGetterWf code (⟨6503⟩ : UInt256) (⟨4⟩ : UInt256) := by
  unfold solcAddressSlotGetterWf
  repeat' first | apply And.intro
  all_goals
    exact patchRuntime_decode_disjoint_of_decode_res hpatch
      (by
        apply clipperCalcPatchesWindowDisjoint32 v <;> native_decide)
      (by
        apply clipperCalcPatchesWindowDisjoint32 v <;> native_decide)
      (by native_decide)
      (by native_decide)
      (by native_decide)

theorem clipperJumpDest6503 (v : ClipperImmutables) {code : ByteArray}
    (hpatch : patchRuntime clipperBytecode (patches v) = some code) :
    (D_J code 0).contains (⟨6503⟩ : UInt256) = true := by
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

theorem clipperCalcBody (v : ClipperImmutables) {code : ByteArray}
    (hpatch : patchRuntime clipperBytecode (patches v) = some code)
    {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256}
    (hcode : I.code = code) (hsize : I.calldata.size < UInt256.size)
    (_hperm : I.perm = true) (hwv : I.weiValue = ⟨0⟩)
    (hsel : selIs I (clipperSelBytes 2))
    (hAccounts : accountMapEquiv σ_evm σ_solm) :
    runtimeEquivalenceFor (config v) (contract v) cA gh bl σ_evm σ_solm σ₀ g A I := by
  have hsz : 4 ≤ I.calldata.size :=
    calldata_size_ge_of_selIs I (clipperSelBytes 2) (by native_decide) hsel
  have hbody :
      ExecTransitionBody (config v) (contract v)
        (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I) ∅ calcTransition.body
        (.returned { contract := contract v, locals := ∅ }
          (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)
          (some [(.address (AccountAddress.ofNat
            (UInt256.land (solcSlotWord σ_solm I ⟨4⟩) solcAddrMask).toNat))])) := by
    simpa [solcSlotWord, initState, Solm.EVM.storageLoad, State.lookupAccount] using
      clipperCalcBodyReturns v
        (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I) ∅
        (by simp only [initState]; exact hwv) (by simp)
  have hreach := clipperReachCalcBody (cA := cA) (gh := gh) (bl := bl)
    (σ := σ_evm) (σ₀ := σ₀) (A := A) (I := I) (g := Sat256.ofUInt256 g)
    (v := v) hpatch hcode hwv hsz hsize hsel
  have hroutine : (D_J code 0).contains (⟨6503⟩ : UInt256) = true := by
    exact clipperJumpDest6503 v hpatch
  exact clipperAddressGetterBodyCore (v := v) (code := code) (cA := cA) (gh := gh)
    (bl := bl) (σ_evm := σ_evm) (σ_solm := σ_solm) (σ₀ := σ₀) (A := A) (I := I)
    (g := g) (sel := clipperSelWord I) (transition := calcTransition)
    (entry := (⟨1115⟩ : UInt256)) (routine := (⟨6503⟩ : UInt256))
    (slot := (⟨4⟩ : UInt256)) (returnPc := (⟨716⟩ : UInt256))
    hcode (clipperDispatch_calc v hsel) (clipperDecode_calc v hsz) hreach hAccounts
    (clipperCalcGetterEntryWf v hpatch) (clipperCalcSlotGetterWf v hpatch) hroutine
    (clipperJumpDestBeforeFirstPatch v hpatch (⟨716⟩ : UInt256) (by native_decide))
    (clipperReturnAddress716Wf v hpatch) (by rfl) hbody

end Benchmarks.Dss.Clipper
