import Benchmarks.Dss.Clipper.Fallback

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Benchmarks.Dss.Clipper.Immutables

namespace Benchmarks.Dss.Clipper

set_option linter.unusedTactic false

theorem clipperTipSelectorWord {I : ExecutionEnv} (hsz : 4 ≤ I.calldata.size)
    (hsel : selIs I (clipperSelBytes 23)) :
    clipperSelWord I = clipperSelNat 23 := by
  simpa [clipperSelWord, solcSelectorWord, clipperSelNat] using
    solcSelectorWord_eq_of_beq I hsz 0x27 0x55 0xcd 0x2d (clipperSelNat 23)
      (by decide +native) (by simpa [clipperSelBytes, selIs] using hsel)

theorem clipperDispatch_tip (v : ClipperImmutables) {I : ExecutionEnv}
    (hsel : selIs I (clipperSelBytes 23)) :
    dispatchMsg (contract v) I.calldata = some tipTransition := by
  refine dispatchMsg_eq_some_of_split (contract := contract v)
    (pre :=
      [activeTransition, bufTransition, calcTransition, chipTransition, chostTransition,
        countTransition, cuspTransition, denyTransition, dogTransition, fileUintTransition,
        fileAddressTransition, getStatusTransition, ilkTransition v, kickTransition v,
        kicksTransition, listTransition, redoTransition v, relyTransition, salesTransition,
        spotterTransition, stoppedTransition, tailTransition, takeTransition v])
    (post :=
      [upchostTransition v, vatTransition v, vowTransition, wardsTransition,
        yankTransition v])
    (ti := tipTransition) (cd := I.calldata) (by rfl) ?_ ?_ ?_ (by rfl)
  · rfl
  · intro t ht
    simp only [List.mem_cons, List.mem_nil_iff] at ht
    rcases ht with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      | hfalse
    · rw [selectorOf, activeSelectorBytes, ← byteArray_eq_of_beq hsel]
      decide +native
    · rw [selectorOf, bufSelectorBytes, ← byteArray_eq_of_beq hsel]
      decide +native
    · rw [selectorOf, calcSelectorBytes, ← byteArray_eq_of_beq hsel]
      decide +native
    · rw [selectorOf, chipSelectorBytes, ← byteArray_eq_of_beq hsel]
      decide +native
    · rw [selectorOf, chostSelectorBytes, ← byteArray_eq_of_beq hsel]
      decide +native
    · rw [selectorOf, countSelectorBytes, ← byteArray_eq_of_beq hsel]
      decide +native
    · rw [selectorOf, cuspSelectorBytes, ← byteArray_eq_of_beq hsel]
      decide +native
    · rw [selectorOf, denySelectorBytes, ← byteArray_eq_of_beq hsel]
      decide +native
    · rw [selectorOf, dogSelectorBytes, ← byteArray_eq_of_beq hsel]
      decide +native
    · rw [selectorOf, fileUintSelectorBytes, ← byteArray_eq_of_beq hsel]
      decide +native
    · rw [selectorOf, fileAddressSelectorBytes, ← byteArray_eq_of_beq hsel]
      decide +native
    · rw [selectorOf, getStatusSelectorBytes, ← byteArray_eq_of_beq hsel]
      decide +native
    · rw [selectorOf, ilkSelectorBytes v, ← byteArray_eq_of_beq hsel]
      decide +native
    · rw [selectorOf, kickSelectorBytes v, ← byteArray_eq_of_beq hsel]
      decide +native
    · rw [selectorOf, kicksSelectorBytes, ← byteArray_eq_of_beq hsel]
      decide +native
    · rw [selectorOf, listSelectorBytes, ← byteArray_eq_of_beq hsel]
      decide +native
    · rw [selectorOf, redoSelectorBytes v, ← byteArray_eq_of_beq hsel]
      decide +native
    · rw [selectorOf, relySelectorBytes, ← byteArray_eq_of_beq hsel]
      decide +native
    · rw [selectorOf, salesSelectorBytes, ← byteArray_eq_of_beq hsel]
      decide +native
    · rw [selectorOf, spotterSelectorBytes, ← byteArray_eq_of_beq hsel]
      decide +native
    · rw [selectorOf, stoppedSelectorBytes, ← byteArray_eq_of_beq hsel]
      decide +native
    · rw [selectorOf, tailSelectorBytes, ← byteArray_eq_of_beq hsel]
      decide +native
    · rw [selectorOf, takeSelectorBytes v, ← byteArray_eq_of_beq hsel]
      decide +native
    · cases hfalse
  · rw [selectorOf, tipSelectorBytes]
    simpa [clipperSelBytes] using hsel

theorem clipperDecode_tip (v : ClipperImmutables) {I : ExecutionEnv}
    (hsz : 4 ≤ I.calldata.size) :
    decodeCalldataWithMode (config v).abiDecodeMode (tipTransition.params.map Param.name)
      (transitionSignature tipTransition).paramTypes I.calldata = some ∅ := by
  show decodeCalldataWithMode (config v).abiDecodeMode [] [] I.calldata = some ∅
  exact decodeCalldataWithMode_empty_ok hsz

theorem clipperEvalTip (v : ClipperImmutables) (evm : EVM.State) (locals : Store)
    (hbase : locals.get? "tip" = none) :
    evalExpr? (config v) { contract := contract v, locals := locals } evm (.storage tipRef) =
      .ok (.int (Int.ofNat (UInt256.land
        (UInt256.div (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨8⟩)
          (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨64⟩))
        (UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨192⟩) ⟨1⟩)).toNat)) := by
  let er : EvaledStorageRef := { base := "tip", steps := [] }
  have her : evalStorageRef (config v)
      { contract := contract v, locals := locals } evm tipRef = .ok er := by
    unfold evalStorageRef tipRef
    simp only [evalStorageRefSteps]
    rfl
  have hty : storageTypeAt? (contract v).storage er = some (.elem (.int uint192Int)) := by
    simp [er, storageTypeAt?, contract, storageDecls, uint192St]
  have hloc :
      (config v).storage.layout er =
        fun _ => some (uint192Loc ⟨8⟩ ⟨8, by decide⟩ (by decide)) := by
    funext evm'
    rfl
  exact evalExpr_storage_scalar_value hbase her hty hloc
    (clipperStorageLocLoad_uint192 evm ⟨8⟩)

theorem clipperTipBodyReturns (v : ClipperImmutables) (evm : EVM.State) (locals : Store)
    (h : evm.executionEnv.weiValue = ⟨0⟩) (hbase : locals.get? "tip" = none) :
    ExecTransitionBody (config v) (contract v) evm locals tipTransition.body
      (.returned { contract := contract v, locals := locals } evm
        (some [(.int (Int.ofNat (UInt256.land
          (UInt256.div (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨8⟩)
            (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨64⟩))
          (UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨192⟩) ⟨1⟩)).toNat))])) := by
  simpa [tipTransition] using
    nonpayableReturnExprBodyReturns (cfg := config v) (contract := contract v) h
      (clipperEvalTip v evm locals hbase)

set_option maxHeartbeats 1000000 in
theorem clipperReachTipBody {cA gh bl σ σ₀ A I} {g : Sat256} (v : ClipperImmutables)
    {code : ByteArray} (hpatch : patchRuntime clipperBytecode (patches v) = some code)
    (hcode : I.code = code) (hwv : I.weiValue = ⟨0⟩)
    (hsz : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hsel : selIs I (clipperSelBytes 23)) :
    ∃ k C, RD code I g (initState cA gh bl σ σ₀ g A I) (⟨637⟩ : UInt256)
      [clipperSelWord I] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
  obtain ⟨_, _, h32⟩ := clipperReachRoot (cA := cA) (gh := gh) (bl := bl)
    (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := g) v hpatch hcode hwv hsz hsize
  have hword := clipperTipSelectorWord hsz hsel
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
    (by rw [hword]; decide +native)
    (clipperJumpDestBeforeFirstPatch v hpatch (⟨260⟩ : UInt256) (by decide +native))
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
    (by rw [hword]; decide +native)
    (clipperJumpDestBeforeFirstPatch v hpatch (⟨369⟩ : UInt256) (by decide +native))
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
    (by rw [hword]; decide +native)
    (by decide +native)
    (by simp)
  have h392 := clipperArmNotTaken (pc := (⟨381⟩ : UInt256))
    (next := (⟨392⟩ : UInt256)) (sel := clipperSelNat 21)
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
    (by rw [hword]; decide +native)
    (by decide +native)
    (by simp)
  have h403 := clipperArmNotTaken (pc := (⟨392⟩ : UInt256))
    (next := (⟨403⟩ : UInt256)) (sel := clipperSelNat 1)
    (tgt := (⟨600⟩ : UInt256)) h392
    (by
        change decode code (⟨392⟩ : UInt256) = some (.DUP1, .none)
        clipper_decode)
    (by
        change decode code (selArmPush4Pc (⟨392⟩ : UInt256)) =
          some (.Push .PUSH4, some (clipperSelNat 1, 4))
        clipper_decode)
    (by
        change decode code (selArmEqPc (⟨392⟩ : UInt256)) = some (.EQ, .none)
        clipper_decode)
    (by decide)
    (by
        change decode code (selArmPushTgtPc (⟨392⟩ : UInt256)) =
          some (.Push .PUSH2, some (⟨600⟩, 2))
        clipper_decode)
    (by
        change decode code (selArmJumpiPc (⟨392⟩ : UInt256) 2) = some (.JUMPI, .none)
        clipper_decode)
    (by rw [hword]; decide +native)
    (by decide +native)
    (by simp)
  have h414 := clipperArmNotTaken (pc := (⟨403⟩ : UInt256))
    (next := (⟨414⟩ : UInt256)) (sel := clipperSelNat 28)
    (tgt := (⟨608⟩ : UInt256)) h403
    (by
        change decode code (⟨403⟩ : UInt256) = some (.DUP1, .none)
        clipper_decode)
    (by
        change decode code (selArmPush4Pc (⟨403⟩ : UInt256)) =
          some (.Push .PUSH4, some (clipperSelNat 28, 4))
        clipper_decode)
    (by
        change decode code (selArmEqPc (⟨403⟩ : UInt256)) = some (.EQ, .none)
        clipper_decode)
    (by decide)
    (by
        change decode code (selArmPushTgtPc (⟨403⟩ : UInt256)) =
          some (.Push .PUSH2, some (⟨608⟩, 2))
        clipper_decode)
    (by
        change decode code (selArmJumpiPc (⟨403⟩ : UInt256) 2) = some (.JUMPI, .none)
        clipper_decode)
    (by rw [hword]; decide +native)
    (by decide +native)
    (by simp)
  have h637 := clipperArmTaken (pc := (⟨414⟩ : UInt256)) (sel := clipperSelNat 23)
    (tgt := (⟨637⟩ : UInt256)) h414
    (by
        change decode code (⟨414⟩ : UInt256) = some (.DUP1, .none)
        clipper_decode)
    (by
        change decode code (selArmPush4Pc (⟨414⟩ : UInt256)) =
          some (.Push .PUSH4, some (clipperSelNat 23, 4))
        clipper_decode)
    (by
        change decode code (selArmEqPc (⟨414⟩ : UInt256)) = some (.EQ, .none)
        clipper_decode)
    (by decide)
    (by
        change decode code (selArmPushTgtPc (⟨414⟩ : UInt256)) =
          some (.Push .PUSH2, some (⟨637⟩, 2))
        clipper_decode)
    (by
        change decode code (selArmJumpiPc (⟨414⟩ : UInt256) 2) = some (.JUMPI, .none)
        clipper_decode)
    (by rw [hword]; decide +native)
    (clipperJumpDestBeforeFirstPatch v hpatch (⟨637⟩ : UInt256) (by decide +native))
    (by simp)
  exact ⟨_, _, h637⟩

theorem clipperTipGetterEntryWf (v : ClipperImmutables) {code : ByteArray}
    (hpatch : patchRuntime clipperBytecode (patches v) = some code) :
    solcGetterEntryWf code (⟨637⟩ : UInt256) (⟨645⟩ : UInt256)
      (⟨2599⟩ : UInt256) := by
  unfold solcGetterEntryWf
  repeat' first | apply And.intro
  all_goals
    rw [clipperDecodeBeforeFirstPatch v hpatch _ (by decide +native)]
    decide +native

theorem clipperTipReturnComputedWf (v : ClipperImmutables) {code : ByteArray}
    (hpatch : patchRuntime clipperBytecode (patches v) = some code) :
    clipperReturnComputedMaskFromMemWf code (⟨645⟩ : UInt256) (⟨192⟩ : UInt256) := by
  unfold clipperReturnComputedMaskFromMemWf
  repeat' first | apply And.intro
  all_goals
    rw [clipperDecodeBeforeFirstPatch v hpatch _ (by decide +native)]
    decide +native

theorem clipperTipPatchesWindowDisjoint32 (v : ClipperImmutables) (lo hi : Nat)
    (hwin : (lo, hi) ∈
      [(2599, 2600), (2600, 2600), (2600, 2601), (2601, 2602),
        (2602, 2603), (2603, 2603), (2603, 2604), (2604, 2605),
        (2605, 2606), (2606, 2607), (2607, 2608), (2608, 2608),
        (2608, 2609), (2609, 2609), (2609, 2610), (2610, 2610),
        (2610, 2611), (2611, 2612), (2612, 2613), (2613, 2614),
        (2614, 2615), (2615, 2616), (2616, 2617), (2617, 2617),
        (2617, 2618), (2618, 2618), (2618, 2619), (2619, 2619),
        (2619, 2620), (2620, 2620), (2620, 2621), (2621, 2621)]) :
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

theorem clipperTipSlotGetterWf (v : ClipperImmutables) {code : ByteArray}
    (hpatch : patchRuntime clipperBytecode (patches v) = some code) :
    clipperPackedUintOffsetSlotGetterWf code (⟨2599⟩ : UInt256) (⟨8⟩ : UInt256)
      (⟨64⟩ : UInt256) (⟨192⟩ : UInt256) := by
  unfold clipperPackedUintOffsetSlotGetterWf
  repeat' first | apply And.intro
  all_goals
    exact patchRuntime_decode_disjoint_of_decode_res hpatch
      (by apply clipperTipPatchesWindowDisjoint32 v; decide +native)
      (by apply clipperTipPatchesWindowDisjoint32 v; decide +native)
      (by decide +native)
      (by decide +native)
      (by decide +native)

theorem clipperJumpDest2599 (v : ClipperImmutables) {code : ByteArray}
    (hpatch : patchRuntime clipperBytecode (patches v) = some code) :
    (D_J code 0).contains (⟨2599⟩ : UInt256) = true := by
  apply patchRuntime_D_J_contains_of_patchScanReaches (fuel := 3000) hpatch
  unfold patches patchesFrom offsets immValues
  simp only [List.foldrM_cons, List.foldrM_nil, List.lookup_cons]
  cases hIlk : wordBytes? v.ilk with
  | none =>
      simp [hIlk]
      decide +native
  | some bs =>
      simp [hIlk]
      decide +native

theorem clipperTipBody (v : ClipperImmutables) {code : ByteArray}
    (hpatch : patchRuntime clipperBytecode (patches v) = some code)
    {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256}
    (hcode : I.code = code) (hsize : I.calldata.size < UInt256.size)
    (_hperm : I.perm = true) (hwv : I.weiValue = ⟨0⟩)
    (hsel : selIs I (clipperSelBytes 23))
    (hAccounts : accountMapEquiv σ_evm σ_solm) :
    runtimeEquivalenceFor (config v) (contract v) cA gh bl σ_evm σ_solm σ₀ g A I := by
  have hsz : 4 ≤ I.calldata.size :=
    calldata_size_ge_of_selIs I (clipperSelBytes 23) (by decide +native) hsel
  have hbody :
      ExecTransitionBody (config v) (contract v)
        (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I) ∅ tipTransition.body
        (.returned { contract := contract v, locals := ∅ }
          (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)
          (some [(.int (Int.ofNat (UInt256.land
            (UInt256.div (solcSlotWord σ_solm I ⟨8⟩)
              (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨64⟩))
            (UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨192⟩) ⟨1⟩)).toNat))])) := by
    simpa [solcSlotWord, initState, Solm.EVM.storageLoad, State.lookupAccount] using
      clipperTipBodyReturns v
        (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I) ∅
        (by simp only [initState]; exact hwv) (by simp)
  have hword : solcSlotWord σ_evm I ⟨8⟩ = solcSlotWord σ_solm I ⟨8⟩ :=
    accountMapEquiv_storage_findD hAccounts I.codeOwner ⟨8⟩ ⟨0⟩
  have hval :
      some [Value.int (Int.ofNat (UInt256.land
          (UInt256.div (solcSlotWord σ_solm I ⟨8⟩)
            (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨64⟩))
          (UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨192⟩) ⟨1⟩)).toNat)] =
        some [Value.int (Int.ofNat (UInt256.land
          (UInt256.div (solcSlotWord σ_evm I ⟨8⟩)
            (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨64⟩))
          (UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨192⟩) ⟨1⟩)).toNat)] := by
    rw [hword]
  have hmask192 :
      (UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨192⟩) ⟨1⟩).toNat =
        2 ^ 192 - 1 := by
    decide +native
  have henc :
      returnEquiv
        (UInt256.toByteArray (UInt256.land
          (UInt256.div (solcSlotWord σ_evm I ⟨8⟩)
            (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨64⟩))
          (UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨192⟩) ⟨1⟩)))
        (some [(.int (Int.ofNat (UInt256.land
          (UInt256.div (solcSlotWord σ_evm I ⟨8⟩)
            (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨64⟩))
          (UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨192⟩) ⟨1⟩)).toNat))])
        tipTransition.returnType := by
    rw [show tipTransition.returnType = [uint192] from rfl]
    exact returnEquiv_of_encode
      (by
        simpa [uint192] using
          uintReturnEncoding ⟨192, by decide⟩
            (UInt256.land
              (UInt256.div (solcSlotWord σ_evm I ⟨8⟩)
                (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨64⟩))
              (UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨192⟩) ⟨1⟩))
            (u256LandMaskToNatLtOfToNat
              (UInt256.div (solcSlotWord σ_evm I ⟨8⟩)
                (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨64⟩))
              (UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨192⟩) ⟨1⟩)
              hmask192))
  have hreach := clipperReachTipBody (cA := cA) (gh := gh) (bl := bl)
    (σ := σ_evm) (σ₀ := σ₀) (A := A) (I := I) (g := Sat256.ofUInt256 g)
    (v := v) hpatch hcode hwv hsz hsize hsel
  have hret := clipperPackedUintOffsetGetterExternal (code := code) (cA := cA)
    (gh := gh) (bl := bl) (σ := σ_evm) (σ₀ := σ₀) (A := A) (I := I)
    (g := Sat256.ofUInt256 g) (sel := clipperSelWord I) (entry := (⟨637⟩ : UInt256))
    (routine := (⟨2599⟩ : UInt256)) (slot := (⟨8⟩ : UInt256))
    (returnPc := (⟨645⟩ : UInt256)) (shiftBits := (⟨64⟩ : UInt256))
    (bits := (⟨192⟩ : UInt256)) (bitNat := 192) hreach
    (clipperTipGetterEntryWf v hpatch) (clipperTipSlotGetterWf v hpatch)
    hmask192 (clipperJumpDest2599 v hpatch)
    (clipperJumpDestBeforeFirstPatch v hpatch (⟨645⟩ : UInt256) (by decide +native))
    (clipperTipReturnComputedWf v hpatch)
  exact hret.reEquivExecutionTransport hcode (clipperDispatch_tip v hsel)
    (clipperDecode_tip v hsz) hbody hval hAccounts henc

end Benchmarks.Dss.Clipper
