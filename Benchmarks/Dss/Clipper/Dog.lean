import Benchmarks.Dss.Clipper.Fallback

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Benchmarks.Dss.Clipper.Immutables

namespace Benchmarks.Dss.Clipper

set_option linter.unusedTactic false

theorem clipperDogSelectorWord {I : ExecutionEnv} (hsz : 4 ≤ I.calldata.size)
    (hsel : selIs I (clipperSelBytes 8)) :
    clipperSelWord I = clipperSelNat 8 := by
  simpa [clipperSelWord, solcSelectorWord, clipperSelNat] using
    solcSelectorWord_eq_of_beq I hsz 0xc3 0xb3 0xad 0x7f (clipperSelNat 8)
      (by native_decide) (by simpa [clipperSelBytes, selIs] using hsel)

theorem clipperDispatch_dog {I : ExecutionEnv}
    (hsel : selIs I (clipperSelBytes 8)) :
    dispatchMsg contract I.calldata = some dogTransition := by
  refine dispatchMsg_eq_some_of_split (contract := contract)
    (pre :=
      [activeTransition, bufTransition, calcTransition, chipTransition, chostTransition,
        countTransition, cuspTransition, denyTransition])
    (post :=
      [fileUintTransition, fileAddressTransition, getStatusTransition, ilkTransition,
        kickTransition, kicksTransition, listTransition, redoTransition, relyTransition,
        salesTransition, spotterTransition, stoppedTransition, tailTransition, takeTransition,
        tipTransition, upchostTransition, vatTransition, vowTransition, wardsTransition,
        yankTransition])
    (ti := dogTransition) (cd := I.calldata) (by rfl) ?_ ?_ ?_ (by rfl)
  · rfl
  · intro t ht
    simp only [List.mem_cons, List.mem_nil_iff] at ht
    rcases ht with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | hfalse
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
    · cases hfalse
  · rw [selectorOf, dogSelectorBytes]
    simpa [clipperSelBytes] using hsel

theorem clipperDecode_dog {I : ExecutionEnv}
    (hsz : 4 ≤ I.calldata.size) :
    decodeCalldataWithMode config.abiDecodeMode (dogTransition.params.map Param.name)
      (transitionSignature dogTransition).paramTypes I.calldata = some ∅ := by
  show decodeCalldataWithMode config.abiDecodeMode [] [] I.calldata = some ∅
  exact decodeCalldataWithMode_empty_ok hsz

theorem clipperEvalDog (v : ClipperImmutables) (evm : EVM.State) (locals : Store)
    (hbase : locals.get? "dog" = none) :
    evalExpr? config { contract := contract, locals := locals, immutables := immStore v } evm
      (.storage dogRef) =
      .ok (.address (AccountAddress.ofNat
        (UInt256.land (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨1⟩)
          solcAddrMask).toNat)) := by
  let er : EvaledStorageRef := { base := "dog", steps := [] }
  have her : evalStorageRef config
      { contract := contract, locals := locals, immutables := immStore v } evm dogRef = .ok er := by
    unfold evalStorageRef dogRef
    simp only [evalStorageRefSteps]
    rfl
  have hty : storageTypeAt? contract.storage er = some (.elem .address) := by
    simp [er, storageTypeAt?, contract, storageDecls, addrSt]
  have hloc : config.storage.layout er = fun _ => some (addrLoc ⟨1⟩) := by
    funext evm'
    rfl
  exact evalExpr_storage_scalar_value hbase her hty hloc
    (clipperStorageLocLoad_address evm ⟨1⟩)

theorem clipperDogBodyReturns (v : ClipperImmutables) (evm : EVM.State) (locals : Store)
    (h : evm.executionEnv.weiValue = ⟨0⟩) (hbase : locals.get? "dog" = none) :
    ExecTransitionBody config contract evm locals dogTransition.body
      (.returned { contract := contract, locals := locals, immutables := immStore v } evm
        (some [(.address (AccountAddress.ofNat
          (UInt256.land (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨1⟩)
            solcAddrMask).toNat))])) (immStore v) := by
  simpa [dogTransition] using
    nonpayableReturnExprBodyReturns (cfg := config) (contract := contract) h
      (clipperEvalDog v evm locals hbase)

set_option maxHeartbeats 1000000 in
theorem clipperReachDogBody {σ σ₀ A I} {g : Sat256} (v : ClipperImmutables)
    {code : ByteArray} (hpatch : patchRuntime clipperBytecode (patches v) = some code)
    (hcode : I.code = code) (hwv : I.weiValue = ⟨0⟩)
    (hsz : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hsel : selIs I (clipperSelBytes 8)) :
    ∃ k C, RD code I g (initState σ σ₀ g A I) (⟨1341⟩ : UInt256)
      [clipperSelWord I] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty σ k C := by
  obtain ⟨_, _, h32⟩ := clipperReachRoot
    (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := g) v hpatch hcode hwv hsz hsize
  have hword := clipperDogSelectorWord hsz hsel
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
  have h147 := clipperArmNotTaken (pc := (⟨136⟩ : UInt256))
    (next := (⟨147⟩ : UInt256)) (sel := clipperSelNat 27)
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
    (by native_decide)
    (by simp)
  have h1341 := clipperArmTaken (pc := (⟨147⟩ : UInt256)) (sel := clipperSelNat 8)
    (tgt := (⟨1341⟩ : UInt256)) h147
    (by
        change decode code (⟨147⟩ : UInt256) = some (.DUP1, .none)
        clipper_decode)
    (by
        change decode code (selArmPush4Pc (⟨147⟩ : UInt256)) =
          some (.Push .PUSH4, some (clipperSelNat 8, 4))
        clipper_decode)
    (by
        change decode code (selArmEqPc (⟨147⟩ : UInt256)) = some (.EQ, .none)
        clipper_decode)
    (by decide)
    (by
        change decode code (selArmPushTgtPc (⟨147⟩ : UInt256)) =
          some (.Push .PUSH2, some (⟨1341⟩, 2))
        clipper_decode)
    (by
        change decode code (selArmJumpiPc (⟨147⟩ : UInt256) 2) = some (.JUMPI, .none)
        clipper_decode)
    (by rw [hword]; native_decide)
    (clipperJumpDestBeforeFirstPatch v hpatch (⟨1341⟩ : UInt256) (by native_decide))
    (by simp)
  exact ⟨_, _, h1341⟩

theorem clipperDogGetterEntryWf (v : ClipperImmutables) {code : ByteArray}
    (hpatch : patchRuntime clipperBytecode (patches v) = some code) :
    solcGetterEntryWf code (⟨1341⟩ : UInt256) (⟨716⟩ : UInt256) (⟨6783⟩ : UInt256) := by
  unfold solcGetterEntryWf
  repeat' first | apply And.intro
  all_goals
    rw [clipperDecodeBeforeFirstPatch v hpatch _ (by native_decide)]
    native_decide

theorem clipperDogPatchesWindowDisjoint32 (v : ClipperImmutables) (lo hi : Nat)
    (hlo : lo ∈ [6783, 6784, 6785, 6786, 6787, 6788, 6789, 6790, 6791, 6792,
      6793, 6794, 6795, 6796, 6797, 6798])
    (hhi : hi ∈ [6784, 6785, 6786, 6787, 6788, 6789, 6790, 6791, 6792,
      6793, 6794, 6795, 6796, 6797, 6798, 6799]) :
    PatchesWindowDisjoint32 lo hi (patches v) := by
  unfold PatchesWindowDisjoint32 PatchWindowDisjoint32 patches patchesFrom offsets immValues
  simp only [List.foldrM_cons, List.foldrM_nil, List.lookup_cons]
  cases hIlk : wordBytes? v.ilk
  · simp [hIlk] at hlo hhi ⊢
  · simp [hIlk] at hlo hhi ⊢
    omega

theorem clipperDogSlotGetterWf (v : ClipperImmutables) {code : ByteArray}
    (hpatch : patchRuntime clipperBytecode (patches v) = some code) :
    solcAddressSlotGetterWf code (⟨6783⟩ : UInt256) (⟨1⟩ : UInt256) := by
  unfold solcAddressSlotGetterWf
  repeat' first | apply And.intro
  all_goals
    exact patchRuntime_decode_disjoint_of_decode_res hpatch
      (by
        apply clipperDogPatchesWindowDisjoint32 v <;> native_decide)
      (by
        apply clipperDogPatchesWindowDisjoint32 v <;> native_decide)
      (by native_decide)
      (by native_decide)
      (by native_decide)

theorem clipperJumpDest6783 (v : ClipperImmutables) {code : ByteArray}
    (hpatch : patchRuntime clipperBytecode (patches v) = some code) :
    (D_J code 0).contains (⟨6783⟩ : UInt256) = true := by
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

theorem clipperDogBody (v : ClipperImmutables) {code : ByteArray}
    (hpatch : patchRuntime clipperBytecode (patches v) = some code)
    {σ σ₀ A I} {g : UInt256}
    (hcode : I.code = code) (hsize : I.calldata.size < UInt256.size)
    (_hperm : I.perm = true) (hwv : I.weiValue = ⟨0⟩)
    (hsel : selIs I (clipperSelBytes 8)) :
    runtimeRefinementFor config contract σ σ₀ g A I (immStore v) := by
  have hsz : 4 ≤ I.calldata.size :=
    calldata_size_ge_of_selIs I (clipperSelBytes 8) (by native_decide) hsel
  have hbody :
      ExecTransitionBody config contract
        (initState σ σ₀ (Sat256.ofUInt256 g) A I) ∅ dogTransition.body
        (.returned { contract := contract, locals := ∅, immutables := immStore v }
          (initState σ σ₀ (Sat256.ofUInt256 g) A I)
          (some [(.address (AccountAddress.ofNat
            (UInt256.land (solcSlotWord σ I ⟨1⟩) solcAddrMask).toNat))])) (immStore v) := by
    simpa [solcSlotWord, initState, Solm.EVM.storageLoad, State.lookupAccount] using
      clipperDogBodyReturns v
        (initState σ σ₀ (Sat256.ofUInt256 g) A I) ∅
        (by simp only [initState]; exact hwv) (by simp)
  have hreach := clipperReachDogBody
    (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := Sat256.ofUInt256 g)
    (v := v) hpatch hcode hwv hsz hsize hsel
  have hroutine : (D_J code 0).contains (⟨6783⟩ : UInt256) = true := by
    exact clipperJumpDest6783 v hpatch
  exact clipperAddressGetterBodyCore (v := v) (code := code)
    (σ := σ) (σ₀ := σ₀) (A := A) (I := I)
    (g := g) (sel := clipperSelWord I) (transition := dogTransition)
    (entry := (⟨1341⟩ : UInt256)) (routine := (⟨6783⟩ : UInt256))
    (slot := (⟨1⟩ : UInt256)) (returnPc := (⟨716⟩ : UInt256))
    hcode (clipperDispatch_dog hsel) (clipperDecode_dog hsz) hreach
    (clipperDogGetterEntryWf v hpatch) (clipperDogSlotGetterWf v hpatch) hroutine
    (clipperJumpDestBeforeFirstPatch v hpatch (⟨716⟩ : UInt256) (by native_decide))
    (clipperReturnAddress716Wf v hpatch) (by rfl) hbody

end Benchmarks.Dss.Clipper
