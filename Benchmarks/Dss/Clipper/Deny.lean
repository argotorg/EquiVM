import Benchmarks.Dss.Clipper.Rely

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Benchmarks.Dss.Clipper.Immutables

set_option maxRecDepth 2000000

namespace Benchmarks.Dss.Clipper

/-! ## `deny(address)` -/

def clipperDenyPostState (evm : EVM.State) (I : ExecutionEnv) : EVM.State :=
  Solm.EVM.storageStore evm evm.executionEnv.codeOwner (clipperRelyUsrStorageSlot I) ⟨0⟩

theorem clipperDecode_deny_ok (v : ClipperImmutables) {I : ExecutionEnv}
    (hsz36 : 36 ≤ I.calldata.size) :
    decodeCalldataWithMode (config v).abiDecodeMode (denyTransition.params.map Param.name)
      (transitionSignature denyTransition).paramTypes I.calldata =
        some (clipperRelyStore I) := by
  show decodeCalldataWithMode (config v).abiDecodeMode ["usr"] [addr] I.calldata = _
  simpa [config, clipperRelyStore, clipperRelyUsrValue, clipperRelyUsrWord,
    calldataWord] using
      decodeCalldata_legacyAddress_ok (cd := I.calldata) (x := "usr") hsz36

theorem clipperDecode_deny_none_short (v : ClipperImmutables) {I : ExecutionEnv}
    (hsz4 : 4 ≤ I.calldata.size) (hshort : I.calldata.size < 36) :
    decodeCalldataWithMode (config v).abiDecodeMode (denyTransition.params.map Param.name)
      (transitionSignature denyTransition).paramTypes I.calldata = none := by
  show decodeCalldataWithMode (config v).abiDecodeMode ["usr"] [addr] I.calldata = none
  simpa [config] using
    decodeCalldata_legacyAddress_none_short (cd := I.calldata) (x := "usr") hsz4 hshort

theorem clipperDenyAssign (v : ClipperImmutables) (evm : EVM.State) (I : ExecutionEnv) :
    assignStorageRef? (config v) { contract := contract v, locals := clipperRelyStore I } evm
      .storage (wardsRef (.var "usr")) (.int 0) =
        .ok ({ contract := contract v, locals := clipperRelyStore I },
          clipperDenyPostState evm I) := by
  apply assignStorageRef_storage_scalar
      (ty := uint256St)
      (loc := wordLoc (clipperRelyUsrStorageSlot I))
      (hbase := clipperRelyStore_wards I)
      (her := evalStorageRef_clipperRely_usr v evm I)
      (hty := by simp [storageTypeAt?, storageTypeStep?, contract, storageDecls, uint256St])
      (hloc := by rfl)
  simpa [clipperDenyPostState] using
    storageLocStore_uint256 evm (clipperRelyUsrStorageSlot I) ⟨0⟩

theorem clipperDenyBodyReturns (v : ClipperImmutables) (evm : EVM.State)
    (I : ExecutionEnv) (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hsrc : evm.executionEnv.source = I.source)
    (hauth :
      Solm.EVM.storageLoad evm evm.executionEnv.codeOwner
        (clipperRelyAuthStorageSlot I) = ⟨1⟩) :
    ExecTransitionBody (config v) (contract v) evm (clipperRelyStore I) denyTransition.body
      (.returned { contract := contract v, locals := clipperRelyStore I }
        (clipperDenyPostState evm I) none) := by
  refine ExecFuncBody.execBlockOK ?_
  simpa [denyTransition, nonpayable, auth] using
    nonpayableRequireAssignStorageBlock
      (cfg := config v)
      (solm := { contract := contract v, locals := clipperRelyStore I })
      (evm := evm)
      (evm' := clipperDenyPostState evm I)
      (guard := .binary .eq (.storage (wardsRef sender)) (.intLit 1))
      (rhs := .intLit 0)
      (ref := wardsRef (.var "usr"))
      (value := .int 0)
      hwv
      (evalExpr_clipperRely_auth_true v evm I hsrc hauth)
      (by simp [evalExpr?, pure])
      (clipperDenyAssign v evm I)

theorem clipperDenyBodyReverts (v : ClipperImmutables) (evm : EVM.State)
    (I : ExecutionEnv) (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hsrc : evm.executionEnv.source = I.source)
    (hauth :
      Solm.EVM.storageLoad evm evm.executionEnv.codeOwner
        (clipperRelyAuthStorageSlot I) ≠ ⟨1⟩) :
    ExecTransitionBody (config v) (contract v) evm (clipperRelyStore I)
      denyTransition.body .reverted := by
  refine ExecFuncBody.execBlockRevert ?_
  simpa [denyTransition, nonpayable, auth] using
    nonpayableSecondRequireReverts
      (cfg := config v)
      (solm := { contract := contract v, locals := clipperRelyStore I })
      (evm := evm)
      (guard := .binary .eq (.storage (wardsRef sender)) (.intLit 1))
      (rest := [.assign .storage (wardsRef (.var "usr")) (.intLit 0)])
      hwv
      (evalExpr_clipperRely_auth_false v evm I hsrc hauth)

theorem clipperDenySelectorWord {I : ExecutionEnv} (hsz : 4 ≤ I.calldata.size)
    (hsel : selIs I (clipperSelBytes 7)) :
    clipperSelWord I = clipperSelNat 7 := by
  simpa [clipperSelWord, solcSelectorWord, clipperSelNat] using
    solcSelectorWord_eq_of_beq I hsz 0x9c 0x52 0xa7 0xf1 (clipperSelNat 7)
      (by native_decide) (by simpa [clipperSelBytes, selIs] using hsel)

theorem clipperDispatch_deny (v : ClipperImmutables) {I : ExecutionEnv}
    (hsel : selIs I (clipperSelBytes 7)) :
    dispatchMsg (contract v) I.calldata = some denyTransition := by
  refine dispatchMsg_eq_some_of_split (contract := contract v)
    (pre :=
      [activeTransition, bufTransition, calcTransition, chipTransition, chostTransition,
        countTransition, cuspTransition])
    (post :=
      [dogTransition, fileUintTransition, fileAddressTransition, getStatusTransition,
        ilkTransition v, kickTransition v, kicksTransition, listTransition, redoTransition v,
        relyTransition, salesTransition, spotterTransition, stoppedTransition, tailTransition,
        takeTransition v, tipTransition, upchostTransition v, vatTransition v, vowTransition,
        wardsTransition, yankTransition v])
    (ti := denyTransition) (cd := I.calldata) (by rfl) ?_ ?_ ?_ (by rfl)
  · rfl
  · intro t ht
    simp only [List.mem_cons, List.mem_nil_iff] at ht
    rcases ht with rfl | rfl | rfl | rfl | rfl | rfl | rfl | hfalse
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
    · cases hfalse
  · rw [selectorOf, denySelectorBytes]
    simpa [clipperSelBytes] using hsel

set_option maxHeartbeats 1000000 in
theorem clipperReachDenyBody {cA gh bl σ σ₀ A I} {g : Sat256}
    (v : ClipperImmutables)
    {code : ByteArray} (hpatch : patchRuntime clipperBytecode (patches v) = some code)
    (hcode : I.code = code) (hwv : I.weiValue = ⟨0⟩)
    (hsz : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hsel : selIs I (clipperSelBytes 7)) :
    ∃ k C, RD code I g (initState cA gh bl σ σ₀ g A I) (⟨1123⟩ : UInt256)
      [clipperSelWord I] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
  obtain ⟨_, _, h32⟩ := clipperReachRoot (cA := cA) (gh := gh) (bl := bl)
    (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := g) v hpatch hcode hwv hsz hsize
  have hword := clipperDenySelectorWord hsz hsel
  have h43 := clipperSplitNotTaken (pc := (⟨32⟩ : UInt256))
    (next := (⟨43⟩ : UInt256)) (pivot := clipperSelNat 20)
    (tgt := (⟨260⟩ : UInt256)) h32
    (by change decode code (⟨32⟩ : UInt256) = some (.DUP1, .none); clipper_decode)
    (by
      change decode code (selArmPush4Pc (⟨32⟩ : UInt256)) =
        some (.Push .PUSH4, some (clipperSelNat 20, 4))
      clipper_decode)
    (by change decode code (selArmEqPc (⟨32⟩ : UInt256)) = some (.GT, .none); clipper_decode)
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
    (by change decode code (⟨43⟩ : UInt256) = some (.DUP1, .none); clipper_decode)
    (by
      change decode code (selArmPush4Pc (⟨43⟩ : UInt256)) =
        some (.Push .PUSH4, some (clipperSelNat 3, 4))
      clipper_decode)
    (by change decode code (selArmEqPc (⟨43⟩ : UInt256)) = some (.GT, .none); clipper_decode)
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
      (by change decode code (⟨162⟩ : UInt256) = some (.JUMPDEST, .none); clipper_decode)
      (by simp))
    (by change decode code (⟨163⟩ : UInt256) = some (.DUP1, .none); clipper_decode)
    (by
      change decode code (selArmPush4Pc (⟨163⟩ : UInt256)) =
        some (.Push .PUSH4, some (clipperSelNat 13, 4))
      clipper_decode)
    (by change decode code (selArmEqPc (⟨163⟩ : UInt256)) = some (.GT, .none); clipper_decode)
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
    (by change decode code (⟨174⟩ : UInt256) = some (.DUP1, .none); clipper_decode)
    (by
      change decode code (selArmPush4Pc (⟨174⟩ : UInt256)) =
        some (.Push .PUSH4, some (clipperSelNat 13, 4))
      clipper_decode)
    (by change decode code (selArmEqPc (⟨174⟩ : UInt256)) = some (.EQ, .none); clipper_decode)
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
  have h196 := clipperArmNotTaken (pc := (⟨185⟩ : UInt256))
    (next := (⟨196⟩ : UInt256)) (sel := clipperSelNat 2)
    (tgt := (⟨1115⟩ : UInt256)) h185
    (by change decode code (⟨185⟩ : UInt256) = some (.DUP1, .none); clipper_decode)
    (by
      change decode code (selArmPush4Pc (⟨185⟩ : UInt256)) =
        some (.Push .PUSH4, some (clipperSelNat 2, 4))
      clipper_decode)
    (by change decode code (selArmEqPc (⟨185⟩ : UInt256)) = some (.EQ, .none); clipper_decode)
    (by decide)
    (by
      change decode code (selArmPushTgtPc (⟨185⟩ : UInt256)) =
        some (.Push .PUSH2, some (⟨1115⟩, 2))
      clipper_decode)
    (by
      change decode code (selArmJumpiPc (⟨185⟩ : UInt256) 2) = some (.JUMPI, .none)
      clipper_decode)
    (by rw [hword]; native_decide)
    (by native_decide)
    (by simp)
  have h1123 := clipperArmTaken (pc := (⟨196⟩ : UInt256)) (sel := clipperSelNat 7)
    (tgt := (⟨1123⟩ : UInt256)) h196
    (by change decode code (⟨196⟩ : UInt256) = some (.DUP1, .none); clipper_decode)
    (by
      change decode code (selArmPush4Pc (⟨196⟩ : UInt256)) =
        some (.Push .PUSH4, some (clipperSelNat 7, 4))
      clipper_decode)
    (by change decode code (selArmEqPc (⟨196⟩ : UInt256)) = some (.EQ, .none); clipper_decode)
    (by decide)
    (by
      change decode code (selArmPushTgtPc (⟨196⟩ : UInt256)) =
        some (.Push .PUSH2, some (⟨1123⟩, 2))
      clipper_decode)
    (by
      change decode code (selArmJumpiPc (⟨196⟩ : UInt256) 2) = some (.JUMPI, .none)
      clipper_decode)
    (by rw [hword]; native_decide)
    (clipperJumpDestBeforeFirstPatch v hpatch (⟨1123⟩ : UInt256) (by native_decide))
    (by simp)
  exact ⟨_, _, h1123⟩

theorem clipperDenyPatchesWindowDisjoint (v : ClipperImmutables) (lo hi : Nat)
    (hlo : 6518 ≤ lo) (hhi : hi ≤ 6668) :
    PatchesWindowDisjoint32 lo hi (patches v) := by
  unfold PatchesWindowDisjoint32 PatchWindowDisjoint32 patches patchesFrom offsets immValues
  simp only [List.foldrM_cons, List.foldrM_nil, List.lookup_cons]
  cases hIlk : wordBytes? v.ilk with
  | none =>
      simp [hIlk]
      try omega
  | some bs =>
      simp [hIlk]
      try omega

theorem clipperDenyDecodeWindow (v : ClipperImmutables) {code : ByteArray}
    (hpatch : patchRuntime clipperBytecode (patches v) = some code)
    {pc : UInt256} {res : Operation × Option (UInt256 × Nat)}
    (hlo : 6518 ≤ pc.toNat)
    (hhi : pc.toNat + 1 + (match res.2 with | none => 0 | some p => p.2) ≤ 6668)
    (hdec : decode clipperBytecode pc = some res) :
    decode code pc = some res :=
  patchRuntime_decode_disjoint_of_decode_res hpatch
    (clipperDenyPatchesWindowDisjoint v pc.toNat (pc.toNat + 1) hlo (by omega))
    (clipperDenyPatchesWindowDisjoint v (pc.toNat + 1)
      (pc.toNat + 1 + (match res.2 with | none => 0 | some p => p.2)) (by omega) hhi)
    hdec
    (by
      have hle :
          pc.toNat + 1 ≤
            pc.toNat + 1 + (match res.2 with | none => 0 | some p => p.2) := by
        omega
      exact Nat.lt_of_le_of_lt (Nat.le_trans hle hhi) (by norm_num))
    (by exact Nat.lt_of_le_of_lt hhi (by norm_num))

macro "clipper_deny_decode" : tactic =>
  `(tactic| first
    | clipper_decode
    | exact clipperDenyDecodeWindow _ (by assumption)
        (by native_decide) (by native_decide) (by native_decide))

theorem clipperDenyOneAddressEntryWf (v : ClipperImmutables) {code : ByteArray}
    (hpatch : patchRuntime clipperBytecode (patches v) = some code) :
    solcOneAddressExternalEntryWf code (⟨1123⟩ : UInt256) (⟨502⟩ : UInt256)
      (⟨6518⟩ : UInt256) := by
  unfold solcOneAddressExternalEntryWf solcOneAddressExternalDecodedPc
  repeat' first | apply And.intro
  all_goals
    (first
      | change decode code _ = some (.JUMPDEST, .none)
      | change decode code _ = some (.POP, .none)
      | change decode code _ = some (.CALLDATASIZE, .none)
      | change decode code _ = some (.CALLDATALOAD, .none)
      | change decode code _ = some (.DUP1, .none)
      | change decode code _ = some (.DUP2, .none)
      | change decode code _ = some (.SUB, .none)
      | change decode code _ = some (.LT, .none)
      | change decode code _ = some (.ISZERO, .none)
      | change decode code _ = some (.AND, .none)
      | change decode code _ = some (.SHL, .none)
      | change decode code _ = some (.JUMPI, .none)
      | change decode code _ = some (.JUMP, .none)
      | change decode code _ = some (.REVERT, .none)
      | change decode code _ = some (.Push .PUSH1, some (_, 1))
      | change decode code _ = some (.Push .PUSH2, some (_, 2)))
    clipper_decode

theorem clipperDenyDecodedJumpDest (v : ClipperImmutables) {code : ByteArray}
    (hpatch : patchRuntime clipperBytecode (patches v) = some code) :
    (D_J code 0).contains (solcOneAddressExternalDecodedPc (⟨1123⟩ : UInt256)) = true := by
  change (D_J code 0).contains (⟨1145⟩ : UInt256) = true
  exact clipperJumpDestBeforeFirstPatch v hpatch (⟨1145⟩ : UInt256) (by native_decide)

theorem clipperDenyRoutineJumpDest (v : ClipperImmutables) {code : ByteArray}
    (hpatch : patchRuntime clipperBytecode (patches v) = some code) :
    (D_J code 0).contains (⟨6518⟩ : UInt256) = true := by
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

theorem clipperDenySuccessJumpDest (v : ClipperImmutables) {code : ByteArray}
    (hpatch : patchRuntime clipperBytecode (patches v) = some code) :
    (D_J code 0).contains (⟨6600⟩ : UInt256) = true := by
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

theorem clipperDenyReturnJumpDest (v : ClipperImmutables) {code : ByteArray}
    (hpatch : patchRuntime clipperBytecode (patches v) = some code) :
    (D_J code 0).contains (⟨502⟩ : UInt256) = true := by
  exact clipperJumpDestBeforeFirstPatch v hpatch (⟨502⟩ : UInt256) (by native_decide)

theorem clipperDenyX_decoded {cA gh bl σ σ₀ A I} {g : Sat256} {sel : UInt256}
    (v : ClipperImmutables) {code : ByteArray}
    (hpatch : patchRuntime clipperBytecode (patches v) = some code)
    (hsz36 : 36 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hreach : ∃ k C, RD code I g (initState cA gh bl σ σ₀ g A I) (⟨1123⟩ : UInt256)
      [sel] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    ∃ k C, RD code I g (initState cA gh bl σ σ₀ g A I) (⟨6518⟩ : UInt256)
      [clipperRelyUsrMaskedWord I, ⟨502⟩, sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
  obtain ⟨_, _, hdecoded⟩ := solcOneAddressExternalLenOk
    (entry := (⟨1123⟩ : UInt256)) (ret := (⟨502⟩ : UInt256))
    (routine := (⟨6518⟩ : UInt256)) hreach
    (clipperDenyOneAddressEntryWf v hpatch)
    (clipperDenyDecodedJumpDest v hpatch) hsz36 hsize
  obtain ⟨_, _, hroutine⟩ := solcOneAddressExternalMaskAndJumpMasked
    (entry := (⟨1123⟩ : UInt256)) (ret := (⟨502⟩ : UInt256))
    (routine := (⟨6518⟩ : UInt256)) (R := [sel]) hdecoded
    (clipperDenyOneAddressEntryWf v hpatch)
    (clipperDenyRoutineJumpDest v hpatch)
    (by simp)
  exact ⟨_, _, by simpa [clipperRelyUsrMaskedWord, clipperRelyUsrWord] using hroutine⟩

theorem clipperDenyX_shortarg {cA gh bl σ σ₀ A I} {g : Sat256} {sel : UInt256}
    (v : ClipperImmutables) {code : ByteArray}
    (hpatch : patchRuntime clipperBytecode (patches v) = some code)
    (hsz4 : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hshort : I.calldata.size < 36)
    (hreach : ∃ k C, RD code I g (initState cA gh bl σ σ₀ g A I) (⟨1123⟩ : UInt256)
      [sel] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    RDrev code g (initState cA gh bl σ σ₀ g A I) := by
  exact solcOneAddressExternalShort
    (entry := (⟨1123⟩ : UInt256)) (ret := (⟨502⟩ : UInt256))
    (routine := (⟨6518⟩ : UInt256)) hreach
    (clipperDenyOneAddressEntryWf v hpatch) hsz4 hsize hshort

set_option maxHeartbeats 1000000 in
theorem clipperDenyX_authorized {cA σ I} {g : Sat256} {s0 : State} {k C : ℕ}
    {sel : UInt256} (v : ClipperImmutables) {code : ByteArray}
    (hpatch : patchRuntime clipperBytecode (patches v) = some code)
    (hauth : clipperRelyAuthWord σ I = ⟨1⟩)
    (h : RD code I g s0 ⟨6518⟩
      [clipperRelyUsrMaskedWord I, ⟨502⟩, sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    ∃ k' C', RD code I g s0 ⟨6600⟩
      [clipperRelyUsrMaskedWord I, ⟨502⟩, sel]
      (clipperRelyAuthHashMem I) (UInt256.ofNat 3) ByteArray.empty (cA, σ) k' C' := by
  have hauthSlot :
      UInt256.ofNat (fromByteArrayBigEndian
          (ffi.KEC ((clipperRelyAuthHashMem I).readWithPadding 0 64))) =
        mapSlot (clipperRelySourceWord I) ⟨0⟩ := by
    simpa [clipperRelyAuthHashMem, mapSlot, solcMappingSlot] using
      twoWordHashMem_solcMappingSlot (⟨0⟩ : UInt256) (clipperRelySourceWord I)
        solcFreePtrMem_size
  have rd6524pre := evm_run h with [
    raw jumpdest (by clipper_deny_decode) (by evm_ov),
    raw caller (by clipper_deny_decode) (by evm_ov),
    raw push1 ⟨0⟩ (by clipper_deny_decode) (by evm_ov),
    raw swap1 (by clipper_deny_decode) (by evm_ov),
    raw dup2 (by clipper_deny_decode) (by evm_ov)]
  have rd6525 := rd6524pre.mstore 0
    (wordAt0Mem (clipperRelySourceWord I) solcFreePtrMem)
    (UInt256.ofNat 3) (by clipper_deny_decode) mem_cost (by rfl) (by native_decide)
    (by evm_ov)
  have rd6529pre := evm_run rd6525 with [
    raw push1 ⟨32⟩ (by clipper_deny_decode) (by evm_ov),
    raw dup2 (by clipper_deny_decode) (by evm_ov),
    raw swap1 (by clipper_deny_decode) (by evm_ov)]
  have rd6530 := rd6529pre.mstore 0 (clipperRelyAuthHashMem I)
    (UInt256.ofNat 3) (by clipper_deny_decode) mem_cost (by rfl) (by native_decide)
    (by evm_ov)
  have rd6533pre := evm_run rd6530 with [
    raw push1 ⟨64⟩ (by clipper_deny_decode) (by evm_ov),
    raw swap1 (by clipper_deny_decode) (by evm_ov)]
  have rd6534 := rd6533pre.keccak256 0 (mapSlot (clipperRelySourceWord I) ⟨0⟩)
    (UInt256.ofNat 3) (by clipper_deny_decode) mem_cost hauthSlot (by native_decide)
    (by evm_ov)
  obtain ⟨k6535, C6535, rd6535raw⟩ := rd6534.sload (by clipper_deny_decode) (by evm_ov)
  have rd6535 : RD code I g s0 ⟨6535⟩
      (clipperRelyAuthWord σ I :: clipperRelyUsrMaskedWord I :: ⟨502⟩ :: [sel])
      (clipperRelyAuthHashMem I) (UInt256.ofNat 3) ByteArray.empty (cA, σ) k6535 C6535 := by
    simpa [clipperRelyAuthWord, solcSlotWord,
      clipperRelyAuthStorageSlot_eq_mapSlot_source I] using rd6535raw
  have rd6538pre := evm_run rd6535 with [
    raw push1 ⟨1⟩ (by clipper_deny_decode) (by evm_ov),
    raw eq (by clipper_deny_decode) (by evm_ov)]
  rw [hauth, u256_eq_refl] at rd6538pre
  have rd6541 := rd6538pre.pushConst (⟨6600⟩ : UInt256)
    (width := 2) (op := .PUSH2) (by decide) (by clipper_deny_decode) (by evm_ov)
  exact ⟨_, _, rd6541.jumpiT (by clipper_deny_decode) one_ne_zero_uint
    (clipperDenySuccessJumpDest v hpatch) (by evm_ov)⟩

set_option maxHeartbeats 1000000 in
theorem clipperDenyX_unauthorized {cA σ I} {g : Sat256} {s0 : State} {k C : ℕ}
    {sel : UInt256} (v : ClipperImmutables) {code : ByteArray}
    (hpatch : patchRuntime clipperBytecode (patches v) = some code)
    (hauth : clipperRelyAuthWord σ I ≠ ⟨1⟩)
    (h : RD code I g s0 ⟨6518⟩
      [clipperRelyUsrMaskedWord I, ⟨502⟩, sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    RDrev code g s0 := by
  have hauthSlot :
      UInt256.ofNat (fromByteArrayBigEndian
          (ffi.KEC ((clipperRelyAuthHashMem I).readWithPadding 0 64))) =
        mapSlot (clipperRelySourceWord I) ⟨0⟩ := by
    simpa [clipperRelyAuthHashMem, mapSlot, solcMappingSlot] using
      twoWordHashMem_solcMappingSlot (⟨0⟩ : UInt256) (clipperRelySourceWord I)
        solcFreePtrMem_size
  have rd6524pre := evm_run h with [
    raw jumpdest (by clipper_deny_decode) (by evm_ov),
    raw caller (by clipper_deny_decode) (by evm_ov),
    raw push1 ⟨0⟩ (by clipper_deny_decode) (by evm_ov),
    raw swap1 (by clipper_deny_decode) (by evm_ov),
    raw dup2 (by clipper_deny_decode) (by evm_ov)]
  have rd6525 := rd6524pre.mstore 0
    (wordAt0Mem (clipperRelySourceWord I) solcFreePtrMem)
    (UInt256.ofNat 3) (by clipper_deny_decode) mem_cost (by rfl) (by native_decide)
    (by evm_ov)
  have rd6529pre := evm_run rd6525 with [
    raw push1 ⟨32⟩ (by clipper_deny_decode) (by evm_ov),
    raw dup2 (by clipper_deny_decode) (by evm_ov),
    raw swap1 (by clipper_deny_decode) (by evm_ov)]
  have rd6530 := rd6529pre.mstore 0 (clipperRelyAuthHashMem I)
    (UInt256.ofNat 3) (by clipper_deny_decode) mem_cost (by rfl) (by native_decide)
    (by evm_ov)
  have rd6533pre := evm_run rd6530 with [
    raw push1 ⟨64⟩ (by clipper_deny_decode) (by evm_ov),
    raw swap1 (by clipper_deny_decode) (by evm_ov)]
  have rd6534 := rd6533pre.keccak256 0 (mapSlot (clipperRelySourceWord I) ⟨0⟩)
    (UInt256.ofNat 3) (by clipper_deny_decode) mem_cost hauthSlot (by native_decide)
    (by evm_ov)
  obtain ⟨k6535, C6535, rd6535raw⟩ := rd6534.sload (by clipper_deny_decode) (by evm_ov)
  have rd6535 : RD code I g s0 ⟨6535⟩
      (clipperRelyAuthWord σ I :: clipperRelyUsrMaskedWord I :: ⟨502⟩ :: [sel])
      (clipperRelyAuthHashMem I) (UInt256.ofNat 3) ByteArray.empty (cA, σ) k6535 C6535 := by
    simpa [clipperRelyAuthWord, solcSlotWord,
      clipperRelyAuthStorageSlot_eq_mapSlot_source I] using rd6535raw
  have rd6538pre := evm_run rd6535 with [
    raw push1 ⟨1⟩ (by clipper_deny_decode) (by evm_ov),
    raw eq (by clipper_deny_decode) (by evm_ov)]
  have heq : UInt256.eq (⟨1⟩ : UInt256) (clipperRelyAuthWord σ I) = ⟨0⟩ := by
    exact u256_eq_of_ne (by intro hbad; exact hauth hbad.symm)
  rw [heq] at rd6538pre
  have rd6541 := rd6538pre.pushConst (⟨6600⟩ : UInt256)
    (width := 2) (op := .PUSH2) (by decide) (by clipper_deny_decode) (by evm_ov)
  have rd6542 := rd6541.jumpiNT (by clipper_deny_decode) rfl (by evm_ov)
  have rd6546 := evm_run rd6542 with [
    raw push1 ⟨64⟩ (by clipper_deny_decode) (by evm_ov),
    raw dup1 (by clipper_deny_decode) (by evm_ov),
    raw mload 0 ⟨128⟩ (UInt256.ofNat 3) (by clipper_deny_decode) mem_cost
      (mloadFreePtrValue (by rw [clipperRelyAuthHashMem_size]; decide)
        (by decide) (clipperRelyAuthHashMem_read64 I))
      (by native_decide) (by evm_ov)]
  have rd6550 := rd6546.pushConst (⟨4594637⟩ : UInt256)
    (width := 3) (op := .PUSH3) (by decide) (by clipper_deny_decode) (by evm_ov)
  have rd6553 := evm_run rd6550 with [
    raw push1 ⟨229⟩ (by clipper_deny_decode) (by evm_ov),
    raw shl (by clipper_deny_decode) (by evm_ov)]
  rw [clipperRelyNotAuthorizedWord] at rd6553
  have rd6555pre := evm_run rd6553 with [
    raw dup2 (by clipper_deny_decode) (by evm_ov)]
  have rd6555 := rd6555pre.mstore 6
    (solcErrorStringMem0 (clipperRelyAuthHashMem I))
    (UInt256.ofNat 5) (by clipper_deny_decode) mem_cost (by rfl) (by native_decide)
    (by evm_ov)
  have rd6567pre := evm_run rd6555 with [
    raw push1 ⟨32⟩ (by clipper_deny_decode) (by evm_ov),
    raw push1 ⟨4⟩ (by clipper_deny_decode) (by evm_ov),
    raw dup3 (by clipper_deny_decode) (by evm_ov),
    raw add (by clipper_deny_decode) (by evm_ov)]
  have rd6562 := rd6567pre.mstore 3
    (solcErrorStringMem1 (clipperRelyAuthHashMem I))
    (UInt256.ofNat 6) (by clipper_deny_decode) mem_cost (by rfl) (by native_decide)
    (by evm_ov)
  have rd6579pre := evm_run rd6562 with [
    raw push1 ⟨22⟩ (by clipper_deny_decode) (by evm_ov),
    raw push1 ⟨36⟩ (by clipper_deny_decode) (by evm_ov),
    raw dup3 (by clipper_deny_decode) (by evm_ov),
    raw add (by clipper_deny_decode) (by evm_ov),
    raw mstore 3 (clipperRelyErrorMem2 I)
      (UInt256.ofNat 7) (by clipper_deny_decode) mem_cost (by rfl)
      (by native_decide) (by evm_ov),
    raw push1 ⟨0⟩ (by clipper_deny_decode) (by evm_ov),
    raw dup1 (by clipper_deny_decode) (by evm_ov),
    raw mload 0 (clipperRelySourceWord I) (UInt256.ofNat 7)
      (by clipper_deny_decode) mem_cost (clipperRelyErrorMem2_mload0 I)
      (by native_decide) (by evm_ov),
    raw push1 ⟨32⟩ (by clipper_deny_decode) (by evm_ov)]
  have rd6578 := rd6579pre.pushConst (⟨9316⟩ : UInt256)
    (width := 2) (op := .PUSH2) (by decide) (by clipper_deny_decode) (by evm_ov)
  have rd6579pre2 := evm_run rd6578 with [
    raw dup4 (by clipper_deny_decode) (by evm_ov)]
  have rd6580 := rd6579pre2.codecopy 0 (clipperRelyErrorCopiedMem code I)
    (UInt256.ofNat 7) (by clipper_deny_decode) mem_cost
    (by
      rw [show (⟨9316⟩ : UInt256).toNat = 9316 from by decide,
        show (⟨32⟩ : UInt256).toNat = 32 from by decide]
      rfl)
    (by native_decide) (by evm_ov)
  have rd6582 := evm_run rd6580 with [
    raw dup2 (by clipper_deny_decode) (by evm_ov),
    raw mload 0 clipperRelyNotAuthorizedStringWord (UInt256.ofNat 7)
      (by clipper_deny_decode) mem_cost
      (by simpa [clipperRelyErrorCopiedMem, clipperRelyErrorMem2]
        using clipperRelyCodecopyMload0 v hpatch I)
      (by native_decide) (by evm_ov),
    raw swap2 (by clipper_deny_decode) (by evm_ov)]
  have rd6584 := rd6582.mstore 0 (clipperRelyErrorRestoredMem code I)
    (UInt256.ofNat 7) (by clipper_deny_decode) mem_cost
    (by simp [clipperRelyErrorRestoredMem, clipperRelyErrorCopiedMem])
    (by native_decide) (by evm_ov)
  have rd6588pre := evm_run rd6584 with [
    raw push1 ⟨68⟩ (by clipper_deny_decode) (by evm_ov),
    raw dup3 (by clipper_deny_decode) (by evm_ov),
    raw add (by clipper_deny_decode) (by evm_ov)]
  have rd6589 := rd6588pre.mstore 3 (clipperRelyErrorStringMem code I)
    (UInt256.ofNat 8) (by clipper_deny_decode) mem_cost
    (by
      rw [show ((⟨128⟩ : UInt256) + ⟨68⟩).toNat = 196 from by decide])
    (by native_decide) (by evm_ov)
  have rd6591 := evm_run rd6589 with [
    raw swap1 (by clipper_deny_decode) (by evm_ov),
    raw mload 0 ⟨128⟩ (UInt256.ofNat 8) (by clipper_deny_decode) mem_cost
      (clipperRelyErrorStringMem_mload64 v hpatch I)
      (by native_decide) (by evm_ov)]
  exact evm_run rd6591 with [
    raw swap1 (by clipper_deny_decode) (by evm_ov),
    raw dup2 (by clipper_deny_decode) (by evm_ov),
    raw swap1 (by clipper_deny_decode) (by evm_ov),
    raw sub (by clipper_deny_decode) (by evm_ov),
    raw push1 ⟨100⟩ (by clipper_deny_decode) (by evm_ov),
    raw add (by clipper_deny_decode) (by evm_ov),
    raw swap1 (by clipper_deny_decode) (by evm_ov),
    raw rev 0 (by clipper_deny_decode) mem_cost (by evm_ov)]

set_option maxHeartbeats 1000000 in
theorem clipperDenyX_storeAuthorized {cA σ I} {g : Sat256} {s0 : State} {k C : ℕ}
    {sel : UInt256} (v : ClipperImmutables) {code : ByteArray}
    (hpatch : patchRuntime clipperBytecode (patches v) = some code)
    (hperm : I.perm = true)
    (h : RD code I g s0 ⟨6600⟩
      [clipperRelyUsrMaskedWord I, ⟨502⟩, sel]
      (clipperRelyAuthHashMem I) (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    RDret code g s0
      (cA, sstoreAccountMap I.codeOwner σ (clipperRelyUsrStorageSlot I) ⟨0⟩)
      ByteArray.empty := by
  have hstoreSlot :
      UInt256.ofNat (fromByteArrayBigEndian
          (ffi.KEC ((clipperRelyStoreHashMem I).readWithPadding 0 64))) =
        mapSlot (clipperRelyUsrMaskedWord I) ⟨0⟩ := by
    simpa [clipperRelyStoreHashMem, mapSlot, solcMappingSlot] using
      twoWordHashMem_solcMappingSlot (⟨0⟩ : UInt256) (clipperRelyUsrMaskedWord I)
        (clipperRelyAuthHashMem_size I)
  have rd6611pre := evm_run h with [
    raw jumpdest (by clipper_deny_decode) (by evm_ov),
    raw push1 ⟨1⟩ (by clipper_deny_decode) (by evm_ov),
    raw push1 ⟨1⟩ (by clipper_deny_decode) (by evm_ov),
    raw push1 ⟨160⟩ (by clipper_deny_decode) (by evm_ov),
    raw shl (by clipper_deny_decode) (by evm_ov),
    raw sub (by clipper_deny_decode) (by evm_ov),
    raw dup2 (by clipper_deny_decode) (by evm_ov),
    raw and (by clipper_deny_decode) (by evm_ov)]
  have hmask :
      UInt256.land (clipperRelyUsrMaskedWord I)
          (UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨160⟩) ⟨1⟩) =
        clipperRelyUsrMaskedWord I := by
    rw [show UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨160⟩) ⟨1⟩ =
      solcAddrMask from by decide]
    exact solcAddrMask_clean (clipperRelyUsrMaskedWord_canonical I)
  rw [hmask] at rd6611pre
  have rd6615pre := evm_run rd6611pre with [
    raw push1 ⟨0⟩ (by clipper_deny_decode) (by evm_ov),
    raw dup2 (by clipper_deny_decode) (by evm_ov),
    raw dup2 (by clipper_deny_decode) (by evm_ov)]
  have rd6616 := rd6615pre.mstore 0
    (wordAt0Mem (clipperRelyUsrMaskedWord I) (clipperRelyAuthHashMem I))
    (UInt256.ofNat 3) (by clipper_deny_decode) mem_cost (by rfl) (by native_decide)
    (by evm_ov)
  have rd6620pre := evm_run rd6616 with [
    raw push1 ⟨32⟩ (by clipper_deny_decode) (by evm_ov),
    raw dup2 (by clipper_deny_decode) (by evm_ov),
    raw swap1 (by clipper_deny_decode) (by evm_ov)]
  have rd6621 := rd6620pre.mstore 0 (clipperRelyStoreHashMem I)
    (UInt256.ofNat 3) (by clipper_deny_decode) mem_cost (by rfl) (by native_decide)
    (by evm_ov)
  have rd6625 := evm_run rd6621 with [
    raw push1 ⟨64⟩ (by clipper_deny_decode) (by evm_ov),
    raw dup1 (by clipper_deny_decode) (by evm_ov),
    raw dup3 (by clipper_deny_decode) (by evm_ov)]
  have rd6626 := rd6625.keccak256 0 (mapSlot (clipperRelyUsrMaskedWord I) ⟨0⟩)
    (UInt256.ofNat 3) (by clipper_deny_decode) mem_cost hstoreSlot (by native_decide)
    (by evm_ov)
  have rd6628pre := evm_run rd6626 with [
    raw dup3 (by clipper_deny_decode) (by evm_ov),
    raw swap1 (by clipper_deny_decode) (by evm_ov)]
  obtain ⟨_, _, rd6629raw⟩ := rd6628pre.sstore hperm (by clipper_deny_decode)
    (by simp only [List.length_cons, List.length_nil]; omega)
  have rd6630 := evm_run rd6629raw with [
    raw mload 0 ⟨128⟩ (UInt256.ofNat 3) (by clipper_deny_decode) mem_cost
      (clipperRelyStoreHashMem_mload64 I) (by native_decide) (by evm_ov)]
  have rd6663 := rd6630.pushConst
    (⟨10976212123044202199007331841938769688047881638844999939251365927447214499099⟩ :
      UInt256)
    (op := .PUSH32) (width := 32) (by decide) (by clipper_deny_decode) (by evm_ov)
  have rd6665 := evm_run rd6663 with [
    raw swap2 (by clipper_deny_decode) (by evm_ov),
    raw swap1 (by clipper_deny_decode) (by evm_ov)]
  have rd6666 := RD.log2 0 (UInt256.ofNat 3) rd6665 (by clipper_deny_decode) hperm mem_cost
    (by native_decide) (by evm_ov)
  have rd6667 := rd6666.pop (by clipper_deny_decode) (by evm_ov)
  have rd502 := rd6667.jump (by clipper_deny_decode) (clipperDenyReturnJumpDest v hpatch)
    (by evm_ov)
  have rd503 := rd502.jumpdest (by clipper_deny_decode) (by evm_ov)
  simpa [clipperRelyUsrStorageSlot_eq_mapSlot_masked I] using
    RD.stop rd503 (by clipper_deny_decode) (by evm_ov)

theorem clipperX_deny_ok {cA gh bl σ σ₀ A I} {g : Sat256} {sel : UInt256}
    (v : ClipperImmutables) {code : ByteArray}
    (hpatch : patchRuntime clipperBytecode (patches v) = some code)
    (hsz36 : 36 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hperm : I.perm = true) (hauth : clipperRelyAuthWord σ I = ⟨1⟩)
    (hreach : ∃ k C, RD code I g
      (initState cA gh bl σ σ₀ g A I) (⟨1123⟩ : UInt256) [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    RDret code g (initState cA gh bl σ σ₀ g A I)
      (cA, sstoreAccountMap I.codeOwner σ (clipperRelyUsrStorageSlot I) ⟨0⟩)
      ByteArray.empty := by
  obtain ⟨_, _, rd6518⟩ := clipperDenyX_decoded (v := v) hpatch hsz36 hsize hreach
  obtain ⟨_, _, rd6600⟩ := clipperDenyX_authorized (v := v) hpatch hauth rd6518
  exact clipperDenyX_storeAuthorized (v := v) hpatch hperm rd6600

theorem clipperX_deny_unauthorized {cA gh bl σ σ₀ A I} {g : Sat256} {sel : UInt256}
    (v : ClipperImmutables) {code : ByteArray}
    (hpatch : patchRuntime clipperBytecode (patches v) = some code)
    (hsz36 : 36 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hauth : clipperRelyAuthWord σ I ≠ ⟨1⟩)
    (hreach : ∃ k C, RD code I g
      (initState cA gh bl σ σ₀ g A I) (⟨1123⟩ : UInt256) [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    RDrev code g (initState cA gh bl σ σ₀ g A I) := by
  obtain ⟨_, _, rd6518⟩ := clipperDenyX_decoded (v := v) hpatch hsz36 hsize hreach
  exact clipperDenyX_unauthorized (v := v) hpatch hauth rd6518

theorem clipperDenyBodyCoreOk
    {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256} {sel : UInt256}
    (v : ClipperImmutables) {code : ByteArray}
    (hpatch : patchRuntime clipperBytecode (patches v) = some code)
    (hcode : I.code = code) (hsize : I.calldata.size < UInt256.size)
    (hperm : I.perm = true) (hwv : I.weiValue = ⟨0⟩)
    (hsz36 : 36 ≤ I.calldata.size)
    (hauth : clipperRelyAuthWord σ_evm I = ⟨1⟩)
    (hdispatch : dispatchMsg (contract v) I.calldata = some denyTransition)
    (hdecode :
      decodeCalldataWithMode (config v).abiDecodeMode (denyTransition.params.map Param.name)
        (transitionSignature denyTransition).paramTypes I.calldata = some (clipperRelyStore I))
    (hreach : ∃ k C, RD code I (Sat256.ofUInt256 g)
      (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) (⟨1123⟩ : UInt256) [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ_evm) k C)
    (hAccounts : accountMapEquiv σ_evm σ_solm) :
    runtimeEquivalenceFor (config v) (contract v) cA gh bl σ_evm σ_solm σ₀ g A I := by
  let evmSolm := initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I
  have hauthWord : clipperRelyAuthWord σ_solm I = ⟨1⟩ := by
    have hword : clipperRelyAuthWord σ_evm I = clipperRelyAuthWord σ_solm I :=
      accountMapEquiv_storage_findD hAccounts I.codeOwner (clipperRelyAuthStorageSlot I) ⟨0⟩
    rw [← hword]
    exact hauth
  have hbody :
      ExecTransitionBody (config v) (contract v) evmSolm (clipperRelyStore I)
        denyTransition.body
        (.returned { contract := contract v, locals := clipperRelyStore I }
          (clipperDenyPostState evmSolm I) none) := by
    simpa [evmSolm, clipperRelyAuthWord, solcSlotWord, initState,
      Solm.EVM.storageLoad, State.lookupAccount] using
      clipperDenyBodyReturns v evmSolm I
        (by simp only [evmSolm, initState]; exact hwv)
        (by simp [evmSolm, initState])
        hauthWord
  exact (clipperX_deny_ok (v := v) (g := Sat256.ofUInt256 g) hpatch hsz36 hsize
      hperm hauth hreach)
    |>.reEquivExecutionGenAccountMapEquiv hcode hdispatch hdecode hbody
      (by simp [clipperDenyPostState, evmSolm, initState, storageStore_createdAccounts])
      (by
        simpa [clipperDenyPostState, evmSolm, initState, storageStore_accountMap] using
          accountMapEquiv_sstoreAccountMap I.codeOwner (clipperRelyUsrStorageSlot I) ⟨0⟩
            hAccounts)
      (by
        simpa [denyTransition] using
          (returnEquiv.fallthrough (o := ByteArray.empty) (r := none) (t := [])
            (dvs := []) rfl (by native_decide) (by native_decide)))

theorem clipperDenyBodyCoreUnauthorized
    {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256} {sel : UInt256}
    (v : ClipperImmutables) {code : ByteArray}
    (hpatch : patchRuntime clipperBytecode (patches v) = some code)
    (hcode : I.code = code) (hsize : I.calldata.size < UInt256.size)
    (hwv : I.weiValue = ⟨0⟩)
    (hsz36 : 36 ≤ I.calldata.size)
    (hauth : clipperRelyAuthWord σ_evm I ≠ ⟨1⟩)
    (hdispatch : dispatchMsg (contract v) I.calldata = some denyTransition)
    (hdecode :
      decodeCalldataWithMode (config v).abiDecodeMode (denyTransition.params.map Param.name)
        (transitionSignature denyTransition).paramTypes I.calldata = some (clipperRelyStore I))
    (hreach : ∃ k C, RD code I (Sat256.ofUInt256 g)
      (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) (⟨1123⟩ : UInt256) [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ_evm) k C)
    (hAccounts : accountMapEquiv σ_evm σ_solm) :
    runtimeEquivalenceFor (config v) (contract v) cA gh bl σ_evm σ_solm σ₀ g A I := by
  let evmSolm := initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I
  have hauthWord : clipperRelyAuthWord σ_solm I ≠ ⟨1⟩ := by
    have hword : clipperRelyAuthWord σ_evm I = clipperRelyAuthWord σ_solm I :=
      accountMapEquiv_storage_findD hAccounts I.codeOwner (clipperRelyAuthStorageSlot I) ⟨0⟩
    intro hbad
    exact hauth (by rw [hword, hbad])
  have hbody :
      ExecTransitionBody (config v) (contract v) evmSolm (clipperRelyStore I)
        denyTransition.body .reverted := by
    simpa [evmSolm, clipperRelyAuthWord, solcSlotWord, initState,
      Solm.EVM.storageLoad, State.lookupAccount] using
      clipperDenyBodyReverts v evmSolm I
        (by simp only [evmSolm, initState]; exact hwv)
        (by simp [evmSolm, initState])
        hauthWord
  exact (clipperX_deny_unauthorized (v := v) (g := Sat256.ofUInt256 g) hpatch hsz36
      hsize hauth hreach)
    |>.reEquivExecutionRevert hcode hdispatch hdecode hbody

theorem clipperDenyBodyCoreDecodeFailed_short
    {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256} {sel : UInt256}
    (v : ClipperImmutables) {code : ByteArray}
    (hpatch : patchRuntime clipperBytecode (patches v) = some code)
    (hcode : I.code = code) (hsize : I.calldata.size < UInt256.size)
    (hsz4 : 4 ≤ I.calldata.size) (hshort : I.calldata.size < 36)
    (hdispatch : dispatchMsg (contract v) I.calldata = some denyTransition)
    (hreach : ∃ k C, RD code I (Sat256.ofUInt256 g)
      (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) (⟨1123⟩ : UInt256) [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ_evm) k C) :
    runtimeEquivalenceFor (config v) (contract v) cA gh bl σ_evm σ_solm σ₀ g A I := by
  exact (clipperDenyX_shortarg (v := v) (g := Sat256.ofUInt256 g) hpatch hsz4
      hsize hshort hreach)
    |>.reEquivDecodingFailed hcode hdispatch (clipperDecode_deny_none_short v hsz4 hshort)

theorem clipperDenyBody (v : ClipperImmutables) {code : ByteArray}
    (hpatch : patchRuntime clipperBytecode (patches v) = some code)
    {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256}
    (hcode : I.code = code) (hsize : I.calldata.size < UInt256.size)
    (hperm : I.perm = true) (hwv : I.weiValue = ⟨0⟩)
    (hsel : selIs I (clipperSelBytes 7))
    (hAccounts : accountMapEquiv σ_evm σ_solm) :
    runtimeEquivalenceFor (config v) (contract v) cA gh bl σ_evm σ_solm σ₀ g A I := by
  have hsz4 : 4 ≤ I.calldata.size :=
    calldata_size_ge_of_selIs I (clipperSelBytes 7) (by native_decide) hsel
  have hdispatch : dispatchMsg (contract v) I.calldata = some denyTransition :=
    clipperDispatch_deny v hsel
  have hreach := clipperReachDenyBody (cA := cA) (gh := gh) (bl := bl)
    (σ := σ_evm) (σ₀ := σ₀) (A := A) (I := I) (g := Sat256.ofUInt256 g)
    (v := v) hpatch hcode hwv hsz4 hsize hsel
  by_cases hsz36 : 36 ≤ I.calldata.size
  · by_cases hauth : clipperRelyAuthWord σ_evm I = ⟨1⟩
    · exact clipperDenyBodyCoreOk (v := v) hpatch hcode hsize hperm hwv hsz36
        hauth hdispatch (clipperDecode_deny_ok v hsz36) hreach hAccounts
    · exact clipperDenyBodyCoreUnauthorized (v := v) hpatch hcode hsize hwv hsz36
        hauth hdispatch (clipperDecode_deny_ok v hsz36) hreach hAccounts
  · exact clipperDenyBodyCoreDecodeFailed_short (v := v) hpatch hcode hsize hsz4
      (by omega) hdispatch hreach

end Benchmarks.Dss.Clipper
