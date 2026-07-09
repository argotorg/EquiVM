import Benchmarks.Dss.Clipper.Fallback

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach Reasoning.Refinement
open Benchmarks.Dss.Clipper.Immutables

set_option maxRecDepth 2000000

namespace Benchmarks.Dss.Clipper

/-! ## Shared `rely`/`deny` address and authorization machinery -/

abbrev clipperRelyUsrWord (I : ExecutionEnv) : UInt256 :=
  calldataWord I.calldata 4

abbrev clipperRelyUsrMaskedWord (I : ExecutionEnv) : UInt256 :=
  UInt256.land solcAddrMask (clipperRelyUsrWord I)

abbrev clipperRelySourceWord (I : ExecutionEnv) : UInt256 :=
  UInt256.ofNat I.source.val

abbrev clipperRelyUsrValue (I : ExecutionEnv) : Value :=
  .address (AccountAddress.ofNat (clipperRelyUsrWord I).toNat)

abbrev clipperRelyUsrKey (I : ExecutionEnv) : KeyValue :=
  .address (AccountAddress.ofNat (clipperRelyUsrWord I).toNat)

abbrev clipperRelyAuthKey (I : ExecutionEnv) : KeyValue :=
  .address I.source

abbrev clipperRelyStore (I : ExecutionEnv) : Store :=
  (∅ : Store).insert "usr" (clipperRelyUsrValue I)

def clipperRelyUsrStorageSlot (I : ExecutionEnv) : UInt256 :=
  wardsSlot (clipperRelyUsrKey I)

def clipperRelyAuthStorageSlot (I : ExecutionEnv) : UInt256 :=
  wardsSlot (clipperRelyAuthKey I)

def clipperRelyAuthWord (σ : AccountMap) (I : ExecutionEnv) : UInt256 :=
  solcSlotWord σ I (clipperRelyAuthStorageSlot I)

def clipperRelyPostState (evm : EVM.State) (I : ExecutionEnv) : EVM.State :=
  Solm.EVM.storageStore evm evm.executionEnv.codeOwner (clipperRelyUsrStorageSlot I) ⟨1⟩

abbrev clipperRelyUsrEvaledRef (I : ExecutionEnv) : EvaledStorageRef :=
  { base := "wards", steps := [.mindex (clipperRelyUsrKey I)] }

abbrev clipperRelyAuthEvaledRef (I : ExecutionEnv) : EvaledStorageRef :=
  { base := "wards", steps := [.mindex (clipperRelyAuthKey I)] }

theorem clipperRelyStore_wards (I : ExecutionEnv) :
    (clipperRelyStore I).get? "wards" = none := by
  unfold clipperRelyStore
  rw [store_get_ne _ _ (by native_decide)]
  simp

theorem clipperRelySourceWord_toNat (I : ExecutionEnv) :
    (clipperRelySourceWord I).toNat = I.source.val := by
  unfold clipperRelySourceWord
  exact ulit_toNat' _ (lt_of_lt_of_le I.source.isLt
    (show AccountAddress.size ≤ UInt256.size from by decide))

theorem clipperRelyUsrStorageSlot_eq_mapSlot_masked (I : ExecutionEnv) :
    clipperRelyUsrStorageSlot I = mapSlot (clipperRelyUsrMaskedWord I) ⟨0⟩ := by
  unfold clipperRelyUsrStorageSlot wardsSlot clipperRelyUsrKey clipperRelyUsrMaskedWord
  rw [keyValueToWord_address_ofNat_mask]

theorem clipperRelyAuthStorageSlot_eq_mapSlot_source (I : ExecutionEnv) :
    clipperRelyAuthStorageSlot I = mapSlot (clipperRelySourceWord I) ⟨0⟩ := by
  unfold clipperRelyAuthStorageSlot wardsSlot clipperRelyAuthKey clipperRelySourceWord
  rw [keyValueToWord_address]

theorem clipperDecode_rely_ok (v : ClipperImmutables) {I : ExecutionEnv}
    (hsz36 : 36 ≤ I.calldata.size) :
    decodeCalldataWithMode (config v).abiDecodeMode (relyTransition.params.map Param.name)
      (transitionSignature relyTransition).paramTypes I.calldata =
        some (clipperRelyStore I) := by
  show decodeCalldataWithMode (config v).abiDecodeMode ["usr"] [addr] I.calldata = _
  simpa [config, clipperRelyStore, clipperRelyUsrValue, clipperRelyUsrWord,
    calldataWord] using
      decodeCalldata_legacyAddress_ok (cd := I.calldata) (x := "usr") hsz36

theorem clipperDecode_rely_none_short (v : ClipperImmutables) {I : ExecutionEnv}
    (hsz4 : 4 ≤ I.calldata.size) (hshort : I.calldata.size < 36) :
    decodeCalldataWithMode (config v).abiDecodeMode (relyTransition.params.map Param.name)
      (transitionSignature relyTransition).paramTypes I.calldata = none := by
  show decodeCalldataWithMode (config v).abiDecodeMode ["usr"] [addr] I.calldata = none
  simpa [config] using
    decodeCalldata_legacyAddress_none_short (cd := I.calldata) (x := "usr") hsz4 hshort

theorem evalStorageRef_clipperRely_usr (v : ClipperImmutables) (evm : EVM.State)
    (I : ExecutionEnv) :
    evalStorageRef (config v) { contract := contract v, locals := clipperRelyStore I } evm
      (wardsRef (.var "usr")) = .ok (clipperRelyUsrEvaledRef I) := by
  simp [evalStorageRef, evalStorageRefStep, wardsRef, clipperRelyStore,
    clipperRelyUsrValue, valueToKey?, EvalResult.bind, EvalResult.ofOption, bind, pure,
    evalExpr?]

theorem evalStorageRef_clipperRely_auth (v : ClipperImmutables) (evm : EVM.State)
    (I : ExecutionEnv) (hsrc : evm.executionEnv.source = I.source) :
    evalStorageRef (config v) { contract := contract v, locals := clipperRelyStore I } evm
      (wardsRef sender) = .ok (clipperRelyAuthEvaledRef I) := by
  simp [evalStorageRef, evalStorageRefStep, wardsRef, sender, envValue,
    clipperRelyAuthEvaledRef, clipperRelyAuthKey, hsrc, valueToKey?, EvalResult.bind,
    EvalResult.ofOption, bind, pure, evalExpr?]

theorem clipperUInt256_toNat_eq_one {a : UInt256} (h : a.toNat = 1) : a = ⟨1⟩ := by
  apply u256_inj
  simpa using h

theorem evalExpr_clipperRely_auth_true (v : ClipperImmutables) (evm : EVM.State)
    (I : ExecutionEnv) (hsrc : evm.executionEnv.source = I.source)
    (hload :
      Solm.EVM.storageLoad evm evm.executionEnv.codeOwner
        (clipperRelyAuthStorageSlot I) = ⟨1⟩) :
    evalExpr? (config v) { contract := contract v, locals := clipperRelyStore I } evm
      (.binary .eq (.storage (wardsRef sender)) (.intLit 1)) = .ok (.bool true) := by
  have hstorage :
      evalExpr? (config v) { contract := contract v, locals := clipperRelyStore I } evm
        (.storage (wardsRef sender)) = .ok (.int 1) := by
    rw [evalExpr_storage_scalar_value
      (cfg := config v)
      (solm := { contract := contract v, locals := clipperRelyStore I })
      (slot := wardsRef sender)
      (er := clipperRelyAuthEvaledRef I)
      (t := .int uint256Int)
      (loc := wordLoc (clipperRelyAuthStorageSlot I))
      (value := .int 1)
      (hbase := by simp [clipperRelyStore, wardsRef])
      (her := evalStorageRef_clipperRely_auth v evm I hsrc)
      (hty := by simp [storageTypeAt?, storageTypeStep?, contract, storageDecls, uint256St])
      (hloc := by rfl)
      (hload := by
        simpa [hload] using clipperStorageLocLoad_uint256 evm
          (clipperRelyAuthStorageSlot I))]
  simp only [evalExpr?, hstorage, EvalResult.bind, bind, pure]
  rfl

theorem evalExpr_clipperRely_auth_false (v : ClipperImmutables) (evm : EVM.State)
    (I : ExecutionEnv) (hsrc : evm.executionEnv.source = I.source)
    (hload :
      Solm.EVM.storageLoad evm evm.executionEnv.codeOwner
        (clipperRelyAuthStorageSlot I) ≠ ⟨1⟩) :
    evalExpr? (config v) { contract := contract v, locals := clipperRelyStore I } evm
      (.binary .eq (.storage (wardsRef sender)) (.intLit 1)) = .ok (.bool false) := by
  have hstorage :
      evalExpr? (config v) { contract := contract v, locals := clipperRelyStore I } evm
        (.storage (wardsRef sender)) =
          .ok (.int (Int.ofNat
            (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner
              (clipperRelyAuthStorageSlot I)).toNat)) := by
    exact evalExpr_storage_scalar_value
      (cfg := config v)
      (solm := { contract := contract v, locals := clipperRelyStore I })
      (slot := wardsRef sender)
      (er := clipperRelyAuthEvaledRef I)
      (t := .int uint256Int)
      (loc := wordLoc (clipperRelyAuthStorageSlot I))
      (hbase := by simp [clipperRelyStore, wardsRef])
      (her := evalStorageRef_clipperRely_auth v evm I hsrc)
      (hty := by simp [storageTypeAt?, storageTypeStep?, contract, storageDecls, uint256St])
      (hloc := by rfl)
      (hload := by
        exact clipperStorageLocLoad_uint256 evm (clipperRelyAuthStorageSlot I))
  have hne :
      Value.int (Int.ofNat
          (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner
            (clipperRelyAuthStorageSlot I)).toNat) ≠ Value.int 1 := by
    intro hbad
    rw [Value.int.injEq] at hbad
    apply hload
    exact clipperUInt256_toNat_eq_one (Int.ofNat.inj hbad)
  have hbeq :
      (Value.int (Int.ofNat
          (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner
            (clipperRelyAuthStorageSlot I)).toNat) == Value.int 1) = false := by
    exact beq_eq_false_iff_ne.mpr hne
  simp only [evalExpr?, hstorage, EvalResult.bind, bind, pure]
  change evalBinaryOp? BinaryOp.eq
      (Value.int (Int.ofNat
        (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner
          (clipperRelyAuthStorageSlot I)).toNat))
      (Value.int 1) = .ok (.bool false)
  simp only [evalBinaryOp?]
  rw [hbeq]

theorem clipperRelyAssign (v : ClipperImmutables) (evm : EVM.State) (I : ExecutionEnv) :
    assignStorageRef? (config v) { contract := contract v, locals := clipperRelyStore I } evm
      .storage (wardsRef (.var "usr")) (.int 1) =
        .ok ({ contract := contract v, locals := clipperRelyStore I },
          clipperRelyPostState evm I) := by
  apply assignStorageRef_storage_scalar
      (ty := uint256St)
      (loc := wordLoc (clipperRelyUsrStorageSlot I))
      (hbase := clipperRelyStore_wards I)
      (her := evalStorageRef_clipperRely_usr v evm I)
      (hty := by simp [storageTypeAt?, storageTypeStep?, contract, storageDecls, uint256St])
      (hloc := by rfl)
  simpa [clipperRelyPostState] using
    storageLocStore_uint256 evm (clipperRelyUsrStorageSlot I) ⟨1⟩

theorem clipperRelyBodyReturns (v : ClipperImmutables) (evm : EVM.State)
    (I : ExecutionEnv) (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hsrc : evm.executionEnv.source = I.source)
    (hauth :
      Solm.EVM.storageLoad evm evm.executionEnv.codeOwner
        (clipperRelyAuthStorageSlot I) = ⟨1⟩) :
    ExecTransitionBody (config v) (contract v) evm (clipperRelyStore I) relyTransition.body
      (.returned { contract := contract v, locals := clipperRelyStore I }
        (clipperRelyPostState evm I) none) := by
  refine ExecFuncBody.execBlockOK ?_
  simpa [relyTransition, nonpayable, auth] using
    nonpayableRequireAssignStorageBlock
      (cfg := config v)
      (solm := { contract := contract v, locals := clipperRelyStore I })
      (evm := evm)
      (evm' := clipperRelyPostState evm I)
      (guard := .binary .eq (.storage (wardsRef sender)) (.intLit 1))
      (rhs := .intLit 1)
      (ref := wardsRef (.var "usr"))
      (value := .int 1)
      hwv
      (evalExpr_clipperRely_auth_true v evm I hsrc hauth)
      (by simp [evalExpr?, pure])
      (clipperRelyAssign v evm I)

theorem clipperRelyBodyReverts (v : ClipperImmutables) (evm : EVM.State)
    (I : ExecutionEnv) (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hsrc : evm.executionEnv.source = I.source)
    (hauth :
      Solm.EVM.storageLoad evm evm.executionEnv.codeOwner
        (clipperRelyAuthStorageSlot I) ≠ ⟨1⟩) :
    ExecTransitionBody (config v) (contract v) evm (clipperRelyStore I)
      relyTransition.body .reverted := by
  refine ExecFuncBody.execBlockRevert ?_
  simpa [relyTransition, nonpayable, auth] using
    nonpayableSecondRequireReverts
      (cfg := config v)
      (solm := { contract := contract v, locals := clipperRelyStore I })
      (evm := evm)
      (guard := .binary .eq (.storage (wardsRef sender)) (.intLit 1))
      (rest := [.assign .storage (wardsRef (.var "usr")) (.intLit 1)])
      hwv
      (evalExpr_clipperRely_auth_false v evm I hsrc hauth)

/-! ## Local LOG2 step helper -/

-- LIBRARY CANDIDATE: `Reasoning.Reach` has `RD.log1`, `RD.log3`, and `RD.log4`; this
-- is the missing arity-2 variant.
def stLog2 (s : State) (a b c d : UInt256) (t : List UInt256) : State :=
  {s with
    substate.logSeries := s.substate.logSeries.push
      ⟨s.executionEnv.codeOwner, #[c, d], s.machineState.memory.readWithPadding a.toNat b.toNat⟩
    machineState.stack := t
    machineState.activeWords :=
      UInt256.ofNat (MachineState.M s.machineState.activeWords.toNat a.toNat b.toNat)
    machineState.gasAvailable :=
      (s.machineState.gasAvailable.subNat (memoryExpansionCost s .LOG2)).subNat
        (GasConstants.Glog + GasConstants.Glogdata * b.toNat
            + 2 * GasConstants.Glogtopic)
    machineState.pc := s.machineState.pc + ⟨1⟩
    machineState.execLength := s.machineState.execLength + 1 }

-- LIBRARY CANDIDATE: `Reasoning.Reach` has xstep lemmas for `LOG1/3/4`; this is the
-- same statement for `LOG2`.
theorem log2_xstep {s : State} {code : ByteArray} {pcv a b c d : UInt256} {t : List UInt256}
    (hcode : s.executionEnv.code = code) (hpc : s.machineState.pc = pcv)
    (hdec : decode code pcv = some (.LOG2, .none)) (hperm : s.executionEnv.perm = true)
    (hstk : s.machineState.stack = a :: b :: c :: d :: t) (hov : t.length ≤ 1024) :
    Xstep (D_J code 0) s
      = (if s.machineState.gasAvailable.toNat
            < memoryExpansionCost s .LOG2
              + (GasConstants.Glog + GasConstants.Glogdata * b.toNat + 2 * GasConstants.Glogtopic)
         then .error .OutOfGass else .ok (stLog2 s a b c d t, .none)) := by
  have hd : decode s.executionEnv.code s.machineState.pc = some (.LOG2, .none) := by
    rw [hcode, hpc]
    exact hdec
  rw [← hcode, step_log2 s hd, hstk]
  have hov' : ¬ ((a :: b :: c :: d :: t).length - 4 + 0 > 1024) := by
    simp only [List.length_cons]
    omega
  have hpermF : (¬ s.executionEnv.perm = true) = False := eq_false (by simp [hperm])
  simp only [collapse_two_stage, if_neg hov', hpermF, if_false, stLog2]

-- LIBRARY CANDIDATE: `Reasoning.Reach.RD` has `log1`, `log3`, and `log4`; this is the
-- missing arity-2 variant.
theorem RD.log2 {code : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {pc : UInt256} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap} {k C : ℕ}
    {a b c d : UInt256} {t : List UInt256} (mcost : ℕ) (awout : UInt256)
    (h : RD code ee g s0 pc (a :: b :: c :: d :: t) mem aw rdata acc k C)
    (hdec : decode code pc = some (.LOG2, .none)) (hperm : ee.perm = true)
    (hmc : ∀ s : State, s.machineState.activeWords = aw →
        s.machineState.stack = a :: b :: c :: d :: t →
        memoryExpansionCost s .LOG2 = mcost)
    (hawout : UInt256.ofNat (MachineState.M aw.toNat a.toNat b.toNat) = awout)
    (hov : t.length ≤ 1024) :
    RD code ee g s0 (pc + ⟨1⟩) t mem awout rdata acc (k + 1)
      (C + (mcost + (GasConstants.Glog + GasConstants.Glogdata * b.toNat
        + 2 * GasConstants.Glogtopic))) := by
  unfold RD at h ⊢
  rcases h with hoog | ⟨s, hX, hcode, hpc, hstk, hgas, hk, hC, hmem, haw, hrdata, hacc, hee, hworld⟩
  · exact Or.inl hoog
  · have hmcS : memoryExpansionCost s .LOG2 = mcost := hmc s haw hstk
    have hperms : s.executionEnv.perm = true := by
      rw [hee]
      exact hperm
    have st := log2_xstep hcode hpc hdec hperms hstk hov
    rw [hmcS] at st
    by_cases gg : g.toNat < C + (mcost
        + (GasConstants.Glog + GasConstants.Glogdata * b.toNat + 2 * GasConstants.Glogtopic))
    · exact Or.inl (hX.trans (stepOOG hgas st hk hC (by omega)))
    · refine Or.inr ⟨stLog2 s a b c d t,
        hX.trans (stepContinue hgas st hk (Nat.not_lt.mp gg)), ?_, ?_, ?_, ?_,
          (by have : 1 ≤ GasConstants.Glog := (by decide); omega), by omega,
          ?_, ?_, ?_, ?_, ?_, ?_⟩
      · simp only [stLog2]
        exact hcode
      · simp only [stLog2]
        rw [hpc]
      · simp only [stLog2]
      · simp only [stLog2, hmcS]
        rw [hgas, Sat256.subNat_sub_add_of_sub_sub, Sat256.subNat_sub_add_of_sub_sub]
      · simp only [stLog2]
        exact hmem
      · simp only [stLog2]
        rw [haw, hawout]
      · simp only [stLog2]
        exact hrdata
      · simp only [stLog2]
        exact hacc
      · simp only [stLog2]
        exact hee
      · exact hworld

theorem clipperRelyPatchesWindowDisjointMid (v : ClipperImmutables) (lo hi : Nat)
    (hlo : 3177 ≤ lo) (hhi : hi ≤ 4239) :
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

theorem clipperRelyDecodeMid (v : ClipperImmutables) {code : ByteArray}
    (hpatch : patchRuntime clipperBytecode (patches v) = some code)
    {pc : UInt256} {res : Operation × Option (UInt256 × Nat)}
    (hlo : 3177 ≤ pc.toNat)
    (hhi : pc.toNat + 1 + (match res.2 with | none => 0 | some p => p.2) ≤ 4239)
    (hdec : decode clipperBytecode pc = some res) :
    decode code pc = some res :=
  patchRuntime_decode_disjoint_of_decode_res hpatch
    (clipperRelyPatchesWindowDisjointMid v pc.toNat (pc.toNat + 1) hlo (by omega))
    (clipperRelyPatchesWindowDisjointMid v (pc.toNat + 1)
      (pc.toNat + 1 + (match res.2 with | none => 0 | some p => p.2)) (by omega) hhi)
    hdec
    (by
      have hle :
          pc.toNat + 1 ≤
            pc.toNat + 1 + (match res.2 with | none => 0 | some p => p.2) := by
        omega
      exact Nat.lt_of_le_of_lt (Nat.le_trans hle hhi) (by norm_num))
    (by exact Nat.lt_of_le_of_lt hhi (by norm_num))

macro "clipper_rely_decode" : tactic =>
  `(tactic| first
    | clipper_decode
    | exact clipperRelyDecodeMid _ (by assumption)
        (by native_decide) (by native_decide) (by native_decide))

/-! ## `rely(address)` dispatch, decode, and EVM trace -/

theorem clipperRelySelectorWord {I : ExecutionEnv} (hsz : 4 ≤ I.calldata.size)
    (hsel : selIs I (clipperSelBytes 17)) :
    clipperSelWord I = clipperSelNat 17 := by
  simpa [clipperSelWord, solcSelectorWord, clipperSelNat] using
    solcSelectorWord_eq_of_beq I hsz 0x65 0xfa 0xe3 0x5e (clipperSelNat 17)
      (by native_decide) (by simpa [clipperSelBytes, selIs] using hsel)

theorem clipperDispatch_rely (v : ClipperImmutables) {I : ExecutionEnv}
    (hsel : selIs I (clipperSelBytes 17)) :
    dispatchMsg (contract v) I.calldata = some relyTransition := by
  refine dispatchMsg_eq_some_of_split (contract := contract v)
    (pre :=
      [activeTransition, bufTransition, calcTransition, chipTransition, chostTransition,
        countTransition, cuspTransition, denyTransition, dogTransition, fileUintTransition,
        fileAddressTransition, getStatusTransition, ilkTransition v, kickTransition v,
        kicksTransition, listTransition, redoTransition v])
    (post :=
      [salesTransition, spotterTransition, stoppedTransition, tailTransition, takeTransition v,
        tipTransition, upchostTransition v, vatTransition v, vowTransition, wardsTransition,
        yankTransition v])
    (ti := relyTransition) (cd := I.calldata) (by rfl) ?_ ?_ ?_ (by rfl)
  · rfl
  · intro t ht
    simp only [List.mem_cons, List.mem_nil_iff] at ht
    rcases ht with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      | rfl | rfl | rfl | rfl | rfl | rfl | hfalse
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
    · cases hfalse
  · rw [selectorOf, relySelectorBytes]
    simpa [clipperSelBytes] using hsel

set_option maxHeartbeats 1000000 in
theorem clipperReachRelyBody {cA gh bl σ σ₀ A I} {g : Sat256} (v : ClipperImmutables)
    {code : ByteArray} (hpatch : patchRuntime clipperBytecode (patches v) = some code)
    (hcode : I.code = code) (hwv : I.weiValue = ⟨0⟩)
    (hsz : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hsel : selIs I (clipperSelBytes 17)) :
    ∃ k C, RD code I g (initState cA gh bl σ σ₀ g A I) (⟨837⟩ : UInt256)
      [clipperSelWord I] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
  obtain ⟨_, _, h32⟩ := clipperReachRoot (cA := cA) (gh := gh) (bl := bl)
    (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := g) v hpatch hcode hwv hsz hsize
  have hword := clipperRelySelectorWord hsz hsel
  have h260 := clipperSplitTaken (pc := (⟨32⟩ : UInt256)) (pivot := clipperSelNat 20)
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
    (clipperJumpDestBeforeFirstPatch v hpatch (⟨260⟩ : UInt256) (by native_decide))
    (by simp)
  have h272 := clipperSplitNotTaken (pc := (⟨261⟩ : UInt256))
    (next := (⟨272⟩ : UInt256)) (pivot := clipperSelNat 9)
    (tgt := (⟨369⟩ : UInt256))
    (h260.jumpdest
      (by change decode code (⟨260⟩ : UInt256) = some (.JUMPDEST, .none); clipper_decode)
      (by simp))
    (by change decode code (⟨261⟩ : UInt256) = some (.DUP1, .none); clipper_decode)
    (by
      change decode code (selArmPush4Pc (⟨261⟩ : UInt256)) =
        some (.Push .PUSH4, some (clipperSelNat 9, 4))
      clipper_decode)
    (by change decode code (selArmEqPc (⟨261⟩ : UInt256)) = some (.GT, .none); clipper_decode)
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
    (by change decode code (⟨272⟩ : UInt256) = some (.DUP1, .none); clipper_decode)
    (by
      change decode code (selArmPush4Pc (⟨272⟩ : UInt256)) =
        some (.Push .PUSH4, some (clipperSelNat 6, 4))
      clipper_decode)
    (by change decode code (selArmEqPc (⟨272⟩ : UInt256)) = some (.GT, .none); clipper_decode)
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
    (by change decode code (⟨283⟩ : UInt256) = some (.DUP1, .none); clipper_decode)
    (by
      change decode code (selArmPush4Pc (⟨283⟩ : UInt256)) =
        some (.Push .PUSH4, some (clipperSelNat 6, 4))
      clipper_decode)
    (by change decode code (selArmEqPc (⟨283⟩ : UInt256)) = some (.EQ, .none); clipper_decode)
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
    (by change decode code (⟨294⟩ : UInt256) = some (.DUP1, .none); clipper_decode)
    (by
      change decode code (selArmPush4Pc (⟨294⟩ : UInt256)) =
        some (.Push .PUSH4, some (clipperSelNat 11, 4))
      clipper_decode)
    (by change decode code (selArmEqPc (⟨294⟩ : UInt256)) = some (.EQ, .none); clipper_decode)
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
  have h316 := clipperArmNotTaken (pc := (⟨305⟩ : UInt256))
    (next := (⟨316⟩ : UInt256)) (sel := clipperSelNat 26)
    (tgt := (⟨829⟩ : UInt256)) h305
    (by change decode code (⟨305⟩ : UInt256) = some (.DUP1, .none); clipper_decode)
    (by
      change decode code (selArmPush4Pc (⟨305⟩ : UInt256)) =
        some (.Push .PUSH4, some (clipperSelNat 26, 4))
      clipper_decode)
    (by change decode code (selArmEqPc (⟨305⟩ : UInt256)) = some (.EQ, .none); clipper_decode)
    (by decide)
    (by
      change decode code (selArmPushTgtPc (⟨305⟩ : UInt256)) =
        some (.Push .PUSH2, some (⟨829⟩, 2))
      clipper_decode)
    (by
      change decode code (selArmJumpiPc (⟨305⟩ : UInt256) 2) = some (.JUMPI, .none)
      clipper_decode)
    (by rw [hword]; native_decide)
    (by native_decide)
    (by simp)
  have h837 := clipperArmTaken (pc := (⟨316⟩ : UInt256)) (sel := clipperSelNat 17)
    (tgt := (⟨837⟩ : UInt256)) h316
    (by change decode code (⟨316⟩ : UInt256) = some (.DUP1, .none); clipper_decode)
    (by
      change decode code (selArmPush4Pc (⟨316⟩ : UInt256)) =
        some (.Push .PUSH4, some (clipperSelNat 17, 4))
      clipper_decode)
    (by change decode code (selArmEqPc (⟨316⟩ : UInt256)) = some (.EQ, .none); clipper_decode)
    (by decide)
    (by
      change decode code (selArmPushTgtPc (⟨316⟩ : UInt256)) =
        some (.Push .PUSH2, some (⟨837⟩, 2))
      clipper_decode)
    (by
      change decode code (selArmJumpiPc (⟨316⟩ : UInt256) 2) = some (.JUMPI, .none)
      clipper_decode)
    (by rw [hword]; native_decide)
    (clipperJumpDestBeforeFirstPatch v hpatch (⟨837⟩ : UInt256) (by native_decide))
    (by simp)
  exact ⟨_, _, h837⟩

theorem clipperRelyOneAddressEntryWf (v : ClipperImmutables) {code : ByteArray}
    (hpatch : patchRuntime clipperBytecode (patches v) = some code) :
    solcOneAddressExternalEntryWf code (⟨837⟩ : UInt256) (⟨502⟩ : UInt256)
      (⟨3340⟩ : UInt256) := by
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

theorem clipperRelyDecodedJumpDest (v : ClipperImmutables) {code : ByteArray}
    (hpatch : patchRuntime clipperBytecode (patches v) = some code) :
    (D_J code 0).contains (solcOneAddressExternalDecodedPc (⟨837⟩ : UInt256)) = true := by
  change (D_J code 0).contains (⟨859⟩ : UInt256) = true
  exact clipperJumpDestBeforeFirstPatch v hpatch (⟨859⟩ : UInt256) (by native_decide)

theorem clipperJumpDest3340 (v : ClipperImmutables) {code : ByteArray}
    (hpatch : patchRuntime clipperBytecode (patches v) = some code) :
    (D_J code 0).contains (⟨3340⟩ : UInt256) = true := by
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

theorem clipperRelyRoutineJumpDest (v : ClipperImmutables) {code : ByteArray}
    (hpatch : patchRuntime clipperBytecode (patches v) = some code) :
    (D_J code 0).contains (⟨3340⟩ : UInt256) = true := by
  exact clipperJumpDest3340 v hpatch

theorem clipperRelyReturnJumpDest (v : ClipperImmutables) {code : ByteArray}
    (hpatch : patchRuntime clipperBytecode (patches v) = some code) :
    (D_J code 0).contains (⟨502⟩ : UInt256) = true := by
  exact clipperJumpDestBeforeFirstPatch v hpatch (⟨502⟩ : UInt256) (by native_decide)

theorem clipperRelyX_decoded {cA gh bl σ σ₀ A I} {g : Sat256} {sel : UInt256}
    (v : ClipperImmutables) {code : ByteArray}
    (hpatch : patchRuntime clipperBytecode (patches v) = some code)
    (hsz36 : 36 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hreach : ∃ k C, RD code I g (initState cA gh bl σ σ₀ g A I) (⟨837⟩ : UInt256)
      [sel] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    ∃ k C, RD code I g (initState cA gh bl σ σ₀ g A I) (⟨3340⟩ : UInt256)
      [clipperRelyUsrMaskedWord I, ⟨502⟩, sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
  obtain ⟨_, _, hdecoded⟩ := solcOneAddressExternalLenOk
    (entry := (⟨837⟩ : UInt256)) (ret := (⟨502⟩ : UInt256))
    (routine := (⟨3340⟩ : UInt256)) hreach
    (clipperRelyOneAddressEntryWf v hpatch)
    (clipperRelyDecodedJumpDest v hpatch) hsz36 hsize
  obtain ⟨_, _, hroutine⟩ := solcOneAddressExternalMaskAndJumpMasked
    (entry := (⟨837⟩ : UInt256)) (ret := (⟨502⟩ : UInt256))
    (routine := (⟨3340⟩ : UInt256)) (R := [sel]) hdecoded
    (clipperRelyOneAddressEntryWf v hpatch)
    (clipperRelyRoutineJumpDest v hpatch)
    (by simp)
  exact ⟨_, _, by simpa [clipperRelyUsrMaskedWord, clipperRelyUsrWord] using hroutine⟩

theorem clipperRelyX_shortarg {cA gh bl σ σ₀ A I} {g : Sat256} {sel : UInt256}
    (v : ClipperImmutables) {code : ByteArray}
    (hpatch : patchRuntime clipperBytecode (patches v) = some code)
    (hsz4 : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hshort : I.calldata.size < 36)
    (hreach : ∃ k C, RD code I g (initState cA gh bl σ σ₀ g A I) (⟨837⟩ : UInt256)
      [sel] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    RDrev code g (initState cA gh bl σ σ₀ g A I) := by
  exact solcOneAddressExternalShort
    (entry := (⟨837⟩ : UInt256)) (ret := (⟨502⟩ : UInt256))
    (routine := (⟨3340⟩ : UInt256)) hreach
    (clipperRelyOneAddressEntryWf v hpatch) hsz4 hsize hshort

noncomputable abbrev clipperRelyAuthHashMem (I : ExecutionEnv) : ByteArray :=
  twoWordHashMem (clipperRelySourceWord I) ⟨0⟩ solcFreePtrMem

noncomputable abbrev clipperRelyStoreHashMem (I : ExecutionEnv) : ByteArray :=
  twoWordHashMem (clipperRelyUsrMaskedWord I) ⟨0⟩ (clipperRelyAuthHashMem I)

theorem clipperRelyUsrMaskedWord_canonical (I : ExecutionEnv) :
    (clipperRelyUsrMaskedWord I).toNat < EVM.addressModulus := by
  unfold clipperRelyUsrMaskedWord
  rw [u256_land_comm solcAddrMask (clipperRelyUsrWord I)]
  exact solcAddrMask_result_canonical (clipperRelyUsrWord I)

theorem clipperRelyAuthHashMem_size (I : ExecutionEnv) :
    (clipperRelyAuthHashMem I).size = 96 := by
  exact twoWordHashMem_size_96 (clipperRelySourceWord I) ⟨0⟩ solcFreePtrMem_size

theorem clipperRelyAuthHashMem_read64 (I : ExecutionEnv) :
    (clipperRelyAuthHashMem I).readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩ := by
  exact twoWordHashMem_read64 (clipperRelySourceWord I) ⟨0⟩ solcFreePtrMem_size
    solcFreePtrMem_read64

theorem clipperRelyStoreHashMem_size (I : ExecutionEnv) :
    (clipperRelyStoreHashMem I).size = 96 := by
  exact twoWordHashMem_size_96 (clipperRelyUsrMaskedWord I) ⟨0⟩
    (clipperRelyAuthHashMem_size I)

theorem clipperRelyStoreHashMem_read64 (I : ExecutionEnv) :
    (clipperRelyStoreHashMem I).readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩ := by
  exact twoWordHashMem_read64 (clipperRelyUsrMaskedWord I) ⟨0⟩
    (clipperRelyAuthHashMem_size I) (clipperRelyAuthHashMem_read64 I)

theorem clipperRelyStoreHashMem_mload64 (I : ExecutionEnv) :
    (if (⟨64⟩ : UInt256).toNat ≥ (clipperRelyStoreHashMem I).size
        ∨ (⟨64⟩ : UInt256) ≥ (UInt256.ofNat 3) * ⟨32⟩ then ⟨0⟩
      else
        UInt256.ofNat (fromByteArrayBigEndian
          ((clipperRelyStoreHashMem I).readWithPadding (⟨64⟩ : UInt256).toNat 32))) =
      ⟨128⟩ := by
  exact mloadFreePtrValue
    (by rw [clipperRelyStoreHashMem_size]; decide)
    (by decide)
    (clipperRelyStoreHashMem_read64 I)

noncomputable abbrev clipperRelyErrorMem2 (I : ExecutionEnv) : ByteArray :=
  solcErrorStringMem2 (⟨22⟩ : UInt256) (clipperRelyAuthHashMem I)

noncomputable abbrev clipperRelyErrorCopiedMem (code : ByteArray) (I : ExecutionEnv) :
    ByteArray :=
  code.write 9316 (clipperRelyErrorMem2 I) 0 32

noncomputable abbrev clipperRelyErrorRestoredMem (code : ByteArray) (I : ExecutionEnv) :
    ByteArray :=
  (UInt256.toByteArray (clipperRelySourceWord I)).write 0
    (clipperRelyErrorCopiedMem code I) 0 32

abbrev clipperRelyNotAuthorizedStringWord : UInt256 :=
  ⟨0x436c69707065722f6e6f742d617574686f72697a656400000000000000000000⟩

noncomputable abbrev clipperRelyErrorStringMem (code : ByteArray) (I : ExecutionEnv) :
    ByteArray :=
  (UInt256.toByteArray clipperRelyNotAuthorizedStringWord).write 0
    (clipperRelyErrorRestoredMem code I) 196 32

theorem clipperRelyErrorMem2_size (I : ExecutionEnv) :
    (clipperRelyErrorMem2 I).size = 196 := by
  exact solcErrorStringMem2_size (⟨22⟩ : UInt256) (clipperRelyAuthHashMem_size I)

theorem clipperRelyErrorMem2_read0 (I : ExecutionEnv) :
    (clipperRelyErrorMem2 I).readWithPadding 0 32 =
      UInt256.toByteArray (clipperRelySourceWord I) := by
  unfold clipperRelyErrorMem2 solcErrorStringMem2
  rw [toByteArray_write_read_below_of_gap (⟨22⟩ : UInt256) _ 164 0
      (by rw [solcErrorStringMem1_size (clipperRelyAuthHashMem_size I)]; omega)
      (by omega)
      (by
        rw [solcErrorStringMem1_size (clipperRelyAuthHashMem_size I)]
        exact lt_usize _ (by norm_num))]
  unfold solcErrorStringMem1
  rw [toByteArray_write_read_below_of_gap (⟨32⟩ : UInt256) _ 132 0
      (by rw [solcErrorStringMem0_size (clipperRelyAuthHashMem_size I)]; omega)
      (by omega)
      (by
        rw [solcErrorStringMem0_size (clipperRelyAuthHashMem_size I)]
        exact lt_usize _ (by norm_num))]
  unfold solcErrorStringMem0
  rw [toByteArray_write_read_below_of_gap solcErrorStringSelector _ 128 0
      (by rw [clipperRelyAuthHashMem_size]; omega)
      (by omega)
      (by
        rw [clipperRelyAuthHashMem_size]
        exact lt_usize _ (by norm_num))]
  exact twoWordHashMem_read0 (clipperRelySourceWord I) ⟨0⟩ solcFreePtrMem_size

theorem clipperRelyErrorMem2_read64 (I : ExecutionEnv) :
    (clipperRelyErrorMem2 I).readWithPadding 64 32 =
      UInt256.toByteArray ⟨128⟩ := by
  unfold clipperRelyErrorMem2 solcErrorStringMem2
  rw [toByteArray_write_read_below_of_gap (⟨22⟩ : UInt256) _ 164 64
      (by rw [solcErrorStringMem1_size (clipperRelyAuthHashMem_size I)]; omega)
      (by omega)
      (by
        rw [solcErrorStringMem1_size (clipperRelyAuthHashMem_size I)]
        exact lt_usize _ (by norm_num))]
  unfold solcErrorStringMem1
  rw [toByteArray_write_read_below_of_gap (⟨32⟩ : UInt256) _ 132 64
      (by rw [solcErrorStringMem0_size (clipperRelyAuthHashMem_size I)]; omega)
      (by omega)
      (by
        rw [solcErrorStringMem0_size (clipperRelyAuthHashMem_size I)]
        exact lt_usize _ (by norm_num))]
  unfold solcErrorStringMem0
  rw [toByteArray_write_read_below_of_gap solcErrorStringSelector _ 128 64
      (by rw [clipperRelyAuthHashMem_size])
      (by omega)
      (by
        rw [clipperRelyAuthHashMem_size]
        exact lt_usize _ (by norm_num))]
  exact clipperRelyAuthHashMem_read64 I

theorem clipperRelyErrorMem2_mload0 (I : ExecutionEnv) :
    (if (⟨0⟩ : UInt256).toNat ≥ (clipperRelyErrorMem2 I).size
        ∨ (⟨0⟩ : UInt256) ≥ (UInt256.ofNat 7) * ⟨32⟩ then ⟨0⟩
      else UInt256.ofNat (fromByteArrayBigEndian
        ((clipperRelyErrorMem2 I).readWithPadding (⟨0⟩ : UInt256).toNat 32))) =
      clipperRelySourceWord I := by
  exact mloadWordValue_of_readWithPadding
    (by rw [clipperRelyErrorMem2_size]; decide)
    (by decide)
    (clipperRelyErrorMem2_read0 I)

theorem clipperRelyNotAuthorizedWord :
    UInt256.shiftLeft (⟨0x461bcd⟩ : UInt256) ⟨229⟩ =
      ⟨0x08c379a000000000000000000000000000000000000000000000000000000000⟩ := by
  native_decide

-- LIBRARY CANDIDATE: `spliceBytes?` preserves bytecode length when it succeeds.
theorem spliceBytes_size_eq {template value out : ByteArray} {off : Nat}
    (hsp : spliceBytes? template off value = some out) :
    out.size = template.size := by
  unfold spliceBytes? at hsp
  split at hsp
  · rename_i hle
    cases hsp
    rw [ByteArray.size_append, ByteArray.size_append, ByteArray.size_extract,
      ByteArray.size_extract]
    omega
  · cases hsp

-- LIBRARY CANDIDATE: 32-byte immutable patching preserves runtime bytecode length.
theorem patchRuntime_size_eq {template out : ByteArray} {ps : List (Nat × ByteArray)}
    (hpatch : patchRuntime template ps = some out) :
    out.size = template.size := by
  induction ps generalizing template with
  | nil =>
      simp [patchRuntime] at hpatch
      cases hpatch
      rfl
  | cons p ps ih =>
      unfold patchRuntime at hpatch
      simp only [List.foldlM_cons, Option.bind_eq_bind] at hpatch
      by_cases hsz : p.2.size = 32
      · rw [if_pos hsz] at hpatch
        cases hsp : spliceBytes? template p.1 p.2 with
        | none =>
            simp [hsp] at hpatch
        | some mid =>
            simp [hsp] at hpatch
            rw [ih hpatch, spliceBytes_size_eq hsp]
      · rw [if_neg hsz] at hpatch
        simp at hpatch

theorem clipperPatchedBytecode_size (v : ClipperImmutables) {code : ByteArray}
    (hpatch : patchRuntime clipperBytecode (patches v) = some code) :
    code.size = clipperBytecode.size :=
  patchRuntime_size_eq hpatch

theorem clipperPatchedBytecode_ge_9348 (v : ClipperImmutables) {code : ByteArray}
    (hpatch : patchRuntime clipperBytecode (patches v) = some code) :
    9348 ≤ code.size := by
  rw [clipperPatchedBytecode_size v hpatch]
  native_decide

theorem clipperRelyPatchesWindowDisjointAfterLast (v : ClipperImmutables) (lo hi : Nat)
    (hlo : 8779 ≤ lo) :
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

theorem clipperRelyNotAuthorizedExtract (v : ClipperImmutables) {code : ByteArray}
    (hpatch : patchRuntime clipperBytecode (patches v) = some code) :
    code.extract 9316 9348 = clipperBytecode.extract 9316 9348 :=
  patchRuntime_extract_disjoint hpatch
    (clipperRelyPatchesWindowDisjointAfterLast v 9316 9348 (by native_decide))

theorem clipperRelyNotAuthorizedExtract_toByteArray :
    clipperBytecode.extract 9316 9348 =
      UInt256.toByteArray clipperRelyNotAuthorizedStringWord := by
  native_decide

-- LIBRARY CANDIDATE: destination-zero `CODECOPY` leaves at least the copied length in memory.
theorem write0_from_size_ge_len (src base : ByteArray) (srcAddr len : ℕ)
    (hlen : len ≠ 0) (hsrc : srcAddr + len ≤ src.size) :
    len ≤ (src.write srcAddr base 0 len).size := by
  show len ≤ (src.write srcAddr base 0 len).data.size
  rw [write0_data_from src base srcAddr len hlen hsrc]
  rw [Array.size_append]
  have hleft : (src.data.extract srcAddr (srcAddr + len)).size = len := by
      rw [Array.size_extract]
      have : src.data.size = src.size := rfl
      omega
  omega

-- LIBRARY CANDIDATE: destination-zero `write` preserves destination size when the copied
-- source window fits inside the existing destination.
theorem write0_from_size_eq_of_len_le_base (src base : ByteArray) (srcAddr len : ℕ)
    (hlen : len ≠ 0) (hsrc : srcAddr + len ≤ src.size) (hbase : len ≤ base.size) :
    (src.write srcAddr base 0 len).size = base.size := by
  rw [write_eq_gen_from src base srcAddr 0 len hlen hsrc (by simpa using hbase)]
  simp [ByteArray.size_append, ByteArray.size_extract]
  omega

-- LIBRARY CANDIDATE: a destination-zero write from an arbitrary source offset preserves
-- a 32-byte read above the written window.
theorem write0_from_read32_above (src base : ByteArray) (srcAddr readAddr : ℕ)
    (hsrc : srcAddr + 32 ≤ src.size) (hbase : 32 ≤ base.size)
    (habove : 32 ≤ readAddr) (hread : readAddr + 32 ≤ base.size) :
    (src.write srcAddr base 0 32).readWithPadding readAddr 32 =
      base.readWithPadding readAddr 32 := by
  have hprefix : (base.extract 0 0).size = 0 := by
    rw [ByteArray.size_extract]
    omega
  have hsrcsz : (src.extract srcAddr (srcAddr + 32)).size = 32 := by
    rw [ByteArray.size_extract]
    omega
  have htail : (base.extract 32 base.size).size = base.size - 32 := by
    rw [ByteArray.size_extract]
    omega
  have habsz : (base.extract 0 0 ++ src.extract srcAddr (srcAddr + 32)).size = 32 := by
    rw [ByteArray.size_append, hprefix, hsrcsz]
  rw [write_eq_gen_from src base srcAddr 0 32 (by decide) hsrc (by omega),
    readWithPadding_eq_extract _ readAddr (by
      rw [ByteArray.size_append, habsz, htail]
      omega),
    readWithPadding_eq_extract _ readAddr hread,
    extract_append_right_window _ _ _ _ (by rw [habsz]; omega), habsz,
    extract_extract_BA,
    show 32 + (readAddr - 32) = readAddr from by omega,
    show min (32 + (readAddr + 32 - 32)) base.size = readAddr + 32 from by omega]

theorem clipperRelyCodecopyRead0 (v : ClipperImmutables) {code : ByteArray}
    (hpatch : patchRuntime clipperBytecode (patches v) = some code) (I : ExecutionEnv) :
    (code.write 9316 (solcErrorStringMem2 (⟨22⟩ : UInt256) (clipperRelyAuthHashMem I))
        0 32).readWithPadding 0 32 =
      UInt256.toByteArray clipperRelyNotAuthorizedStringWord := by
  rw [write0_read_back_from_gen]
  · rw [clipperRelyNotAuthorizedExtract v hpatch]
    exact clipperRelyNotAuthorizedExtract_toByteArray
  · decide
  · exact clipperPatchedBytecode_ge_9348 v hpatch
  · norm_num

theorem clipperRelyCodecopyMload0 (v : ClipperImmutables) {code : ByteArray}
    (hpatch : patchRuntime clipperBytecode (patches v) = some code) (I : ExecutionEnv) :
    (if (⟨0⟩ : UInt256).toNat ≥
          (code.write 9316 (solcErrorStringMem2 (⟨22⟩ : UInt256)
            (clipperRelyAuthHashMem I)) 0 32).size
        ∨ (⟨0⟩ : UInt256) ≥ (UInt256.ofNat 7) * ⟨32⟩ then ⟨0⟩
      else UInt256.ofNat (fromByteArrayBigEndian
        ((code.write 9316 (solcErrorStringMem2 (⟨22⟩ : UInt256)
          (clipperRelyAuthHashMem I)) 0 32).readWithPadding
            (⟨0⟩ : UInt256).toNat 32))) =
      clipperRelyNotAuthorizedStringWord := by
  exact mloadWordValue_of_readWithPadding
    (by
      have hge := write0_from_size_ge_len code
        (solcErrorStringMem2 (⟨22⟩ : UInt256) (clipperRelyAuthHashMem I)) 9316 32
        (by decide) (clipperPatchedBytecode_ge_9348 v hpatch)
      change 0 < (code.write 9316
        (solcErrorStringMem2 (⟨22⟩ : UInt256) (clipperRelyAuthHashMem I)) 0 32).size
      omega)
    (by decide)
    (clipperRelyCodecopyRead0 v hpatch I)

theorem clipperRelyErrorCopiedMem_size (v : ClipperImmutables) {code : ByteArray}
    (hpatch : patchRuntime clipperBytecode (patches v) = some code) (I : ExecutionEnv) :
    (clipperRelyErrorCopiedMem code I).size = 196 := by
  unfold clipperRelyErrorCopiedMem
  rw [write0_from_size_eq_of_len_le_base code (clipperRelyErrorMem2 I) 9316 32
      (by decide) (clipperPatchedBytecode_ge_9348 v hpatch)
      (by rw [clipperRelyErrorMem2_size]; omega)]
  exact clipperRelyErrorMem2_size I

theorem clipperRelyErrorCopiedMem_read64 (v : ClipperImmutables) {code : ByteArray}
    (hpatch : patchRuntime clipperBytecode (patches v) = some code) (I : ExecutionEnv) :
    (clipperRelyErrorCopiedMem code I).readWithPadding 64 32 =
      UInt256.toByteArray ⟨128⟩ := by
  unfold clipperRelyErrorCopiedMem
  rw [write0_from_read32_above code (clipperRelyErrorMem2 I) 9316 64
      (clipperPatchedBytecode_ge_9348 v hpatch)
      (by rw [clipperRelyErrorMem2_size]; omega)
      (by omega)
      (by rw [clipperRelyErrorMem2_size]; omega)]
  exact clipperRelyErrorMem2_read64 I

theorem clipperRelyErrorRestoredMem_size (v : ClipperImmutables) {code : ByteArray}
    (hpatch : patchRuntime clipperBytecode (patches v) = some code) (I : ExecutionEnv) :
    (clipperRelyErrorRestoredMem code I).size = 196 := by
  unfold clipperRelyErrorRestoredMem
  rw [write0_from_size_eq_of_len_le_base (UInt256.toByteArray (clipperRelySourceWord I))
      (clipperRelyErrorCopiedMem code I) 0 32 (by decide)
      (by rw [toByteArray_size])
      (by rw [clipperRelyErrorCopiedMem_size v hpatch I]; omega)]
  exact clipperRelyErrorCopiedMem_size v hpatch I

theorem clipperRelyErrorRestoredMem_read64 (v : ClipperImmutables) {code : ByteArray}
    (hpatch : patchRuntime clipperBytecode (patches v) = some code) (I : ExecutionEnv) :
    (clipperRelyErrorRestoredMem code I).readWithPadding 64 32 =
      UInt256.toByteArray ⟨128⟩ := by
  unfold clipperRelyErrorRestoredMem
  rw [write32_read_above (UInt256.toByteArray (clipperRelySourceWord I))
      (clipperRelyErrorCopiedMem code I) 0 64
      (by rw [toByteArray_size])
      (by omega)
      (by omega)
      (by rw [clipperRelyErrorCopiedMem_size v hpatch I]; omega)]
  exact clipperRelyErrorCopiedMem_read64 v hpatch I

theorem clipperRelyErrorStringMem_size (v : ClipperImmutables) {code : ByteArray}
    (hpatch : patchRuntime clipperBytecode (patches v) = some code) (I : ExecutionEnv) :
    (clipperRelyErrorStringMem code I).size = 228 := by
  unfold clipperRelyErrorStringMem
  rw [write32_eq _ _ 196 (by rw [toByteArray_size])
      (by rw [clipperRelyErrorRestoredMem_size v hpatch I])]
  simp [ByteArray.size_append, ByteArray.size_extract,
    clipperRelyErrorRestoredMem_size v hpatch I]

theorem clipperRelyErrorStringMem_read64 (v : ClipperImmutables) {code : ByteArray}
    (hpatch : patchRuntime clipperBytecode (patches v) = some code) (I : ExecutionEnv) :
    (clipperRelyErrorStringMem code I).readWithPadding 64 32 =
      UInt256.toByteArray ⟨128⟩ := by
  unfold clipperRelyErrorStringMem
  rw [toByteArray_write_read_below_of_gap clipperRelyNotAuthorizedStringWord _ 196 64
      (by rw [clipperRelyErrorRestoredMem_size v hpatch I]; omega)
      (by omega)
      (by
        rw [clipperRelyErrorRestoredMem_size v hpatch I]
        exact lt_usize _ (by norm_num))]
  exact clipperRelyErrorRestoredMem_read64 v hpatch I

theorem clipperRelyErrorStringMem_mload64 (v : ClipperImmutables) {code : ByteArray}
    (hpatch : patchRuntime clipperBytecode (patches v) = some code) (I : ExecutionEnv) :
    (if (⟨64⟩ : UInt256).toNat ≥ (clipperRelyErrorStringMem code I).size
        ∨ (⟨64⟩ : UInt256) ≥ UInt256.ofNat 8 * ⟨32⟩ then ⟨0⟩
      else UInt256.ofNat (fromByteArrayBigEndian
        ((clipperRelyErrorStringMem code I).readWithPadding
          (⟨64⟩ : UInt256).toNat 32))) =
      ⟨128⟩ :=
  mloadFreePtrValue
    (by rw [clipperRelyErrorStringMem_size v hpatch I]; decide)
    (by decide)
    (clipperRelyErrorStringMem_read64 v hpatch I)

theorem clipperJumpDest3422 (v : ClipperImmutables) {code : ByteArray}
    (hpatch : patchRuntime clipperBytecode (patches v) = some code) :
    (D_J code 0).contains (⟨3422⟩ : UInt256) = true := by
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

set_option maxHeartbeats 1000000 in
theorem clipperRelyX_authorized {cA σ I} {g : Sat256} {s0 : State} {k C : ℕ}
    {sel : UInt256} (v : ClipperImmutables) {code : ByteArray}
    (hpatch : patchRuntime clipperBytecode (patches v) = some code)
    (hauth : clipperRelyAuthWord σ I = ⟨1⟩)
    (h : RD code I g s0 ⟨3340⟩
      [clipperRelyUsrMaskedWord I, ⟨502⟩, sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    ∃ k' C', RD code I g s0 ⟨3422⟩
      [clipperRelyUsrMaskedWord I, ⟨502⟩, sel]
      (clipperRelyAuthHashMem I) (UInt256.ofNat 3) ByteArray.empty (cA, σ) k' C' := by
  have hauthSlot :
      UInt256.ofNat (fromByteArrayBigEndian
          (ffi.KEC ((clipperRelyAuthHashMem I).readWithPadding 0 64))) =
        mapSlot (clipperRelySourceWord I) ⟨0⟩ := by
    simpa [clipperRelyAuthHashMem, mapSlot, solcMappingSlot] using
      twoWordHashMem_solcMappingSlot (⟨0⟩ : UInt256) (clipperRelySourceWord I)
        solcFreePtrMem_size
  have rd3346pre := evm_run h with [
    raw jumpdest (by clipper_rely_decode) (by evm_ov),
    raw caller (by clipper_rely_decode) (by evm_ov),
    raw push1 ⟨0⟩ (by clipper_rely_decode) (by evm_ov),
    raw swap1 (by clipper_rely_decode) (by evm_ov),
    raw dup2 (by clipper_rely_decode) (by evm_ov)]
  have rd3347 := rd3346pre.mstore 0
    (wordAt0Mem (clipperRelySourceWord I) solcFreePtrMem)
    (UInt256.ofNat 3) (by clipper_rely_decode) mem_cost (by rfl) (by native_decide)
    (by evm_ov)
  have rd3351pre := evm_run rd3347 with [
    raw push1 ⟨32⟩ (by clipper_rely_decode) (by evm_ov),
    raw dup2 (by clipper_rely_decode) (by evm_ov),
    raw swap1 (by clipper_rely_decode) (by evm_ov)]
  have rd3352 := rd3351pre.mstore 0 (clipperRelyAuthHashMem I)
    (UInt256.ofNat 3) (by clipper_rely_decode) mem_cost (by rfl) (by native_decide)
    (by evm_ov)
  have rd3355pre := evm_run rd3352 with [
    raw push1 ⟨64⟩ (by clipper_rely_decode) (by evm_ov),
    raw swap1 (by clipper_rely_decode) (by evm_ov)]
  have rd3356 := rd3355pre.keccak256 0 (mapSlot (clipperRelySourceWord I) ⟨0⟩)
    (UInt256.ofNat 3) (by clipper_rely_decode) mem_cost hauthSlot (by native_decide)
    (by evm_ov)
  obtain ⟨k3357, C3357, rd3357raw⟩ := rd3356.sload (by clipper_rely_decode) (by evm_ov)
  have rd3357 : RD code I g s0 ⟨3357⟩
      (clipperRelyAuthWord σ I :: clipperRelyUsrMaskedWord I :: ⟨502⟩ :: [sel])
      (clipperRelyAuthHashMem I) (UInt256.ofNat 3) ByteArray.empty (cA, σ) k3357 C3357 := by
    simpa [clipperRelyAuthWord, solcSlotWord,
      clipperRelyAuthStorageSlot_eq_mapSlot_source I] using rd3357raw
  have rd3360pre := evm_run rd3357 with [
    raw push1 ⟨1⟩ (by clipper_rely_decode) (by evm_ov),
    raw eq (by clipper_rely_decode) (by evm_ov)]
  rw [hauth, u256_eq_refl] at rd3360pre
  have rd3363 := rd3360pre.pushConst (⟨3422⟩ : UInt256)
    (width := 2) (op := .PUSH2) (by decide) (by clipper_rely_decode) (by evm_ov)
  exact ⟨_, _, rd3363.jumpiT (by clipper_rely_decode) one_ne_zero_uint
    (clipperJumpDest3422 v hpatch) (by evm_ov)⟩

set_option maxHeartbeats 1000000 in
theorem clipperRelyX_unauthorized {cA σ I} {g : Sat256} {s0 : State} {k C : ℕ}
    {sel : UInt256} (v : ClipperImmutables) {code : ByteArray}
    (hpatch : patchRuntime clipperBytecode (patches v) = some code)
    (hauth : clipperRelyAuthWord σ I ≠ ⟨1⟩)
    (h : RD code I g s0 ⟨3340⟩
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
  have rd3346pre := evm_run h with [
    raw jumpdest (by clipper_rely_decode) (by evm_ov),
    raw caller (by clipper_rely_decode) (by evm_ov),
    raw push1 ⟨0⟩ (by clipper_rely_decode) (by evm_ov),
    raw swap1 (by clipper_rely_decode) (by evm_ov),
    raw dup2 (by clipper_rely_decode) (by evm_ov)]
  have rd3347 := rd3346pre.mstore 0
    (wordAt0Mem (clipperRelySourceWord I) solcFreePtrMem)
    (UInt256.ofNat 3) (by clipper_rely_decode) mem_cost (by rfl) (by native_decide)
    (by evm_ov)
  have rd3351pre := evm_run rd3347 with [
    raw push1 ⟨32⟩ (by clipper_rely_decode) (by evm_ov),
    raw dup2 (by clipper_rely_decode) (by evm_ov),
    raw swap1 (by clipper_rely_decode) (by evm_ov)]
  have rd3352 := rd3351pre.mstore 0 (clipperRelyAuthHashMem I)
    (UInt256.ofNat 3) (by clipper_rely_decode) mem_cost (by rfl) (by native_decide)
    (by evm_ov)
  have rd3355pre := evm_run rd3352 with [
    raw push1 ⟨64⟩ (by clipper_rely_decode) (by evm_ov),
    raw swap1 (by clipper_rely_decode) (by evm_ov)]
  have rd3356 := rd3355pre.keccak256 0 (mapSlot (clipperRelySourceWord I) ⟨0⟩)
    (UInt256.ofNat 3) (by clipper_rely_decode) mem_cost hauthSlot (by native_decide)
    (by evm_ov)
  obtain ⟨k3357, C3357, rd3357raw⟩ := rd3356.sload (by clipper_rely_decode) (by evm_ov)
  have rd3357 : RD code I g s0 ⟨3357⟩
      (clipperRelyAuthWord σ I :: clipperRelyUsrMaskedWord I :: ⟨502⟩ :: [sel])
      (clipperRelyAuthHashMem I) (UInt256.ofNat 3) ByteArray.empty (cA, σ) k3357 C3357 := by
    simpa [clipperRelyAuthWord, solcSlotWord,
      clipperRelyAuthStorageSlot_eq_mapSlot_source I] using rd3357raw
  have rd3360pre := evm_run rd3357 with [
    raw push1 ⟨1⟩ (by clipper_rely_decode) (by evm_ov),
    raw eq (by clipper_rely_decode) (by evm_ov)]
  have heq : UInt256.eq (⟨1⟩ : UInt256) (clipperRelyAuthWord σ I) = ⟨0⟩ := by
    exact u256_eq_of_ne (by intro hbad; exact hauth hbad.symm)
  rw [heq] at rd3360pre
  have rd3363 := rd3360pre.pushConst (⟨3422⟩ : UInt256)
    (width := 2) (op := .PUSH2) (by decide) (by clipper_rely_decode) (by evm_ov)
  have rd3364 := rd3363.jumpiNT (by clipper_rely_decode) rfl (by evm_ov)
  have rd3368 := evm_run rd3364 with [
    raw push1 ⟨64⟩ (by clipper_rely_decode) (by evm_ov),
    raw dup1 (by clipper_rely_decode) (by evm_ov),
    raw mload 0 ⟨128⟩ (UInt256.ofNat 3) (by clipper_rely_decode) mem_cost
      (mloadFreePtrValue (by rw [clipperRelyAuthHashMem_size]; decide)
        (by decide) (clipperRelyAuthHashMem_read64 I))
      (by native_decide) (by evm_ov)]
  have rd3372 := rd3368.pushConst (⟨4594637⟩ : UInt256)
    (width := 3) (op := .PUSH3) (by decide) (by clipper_rely_decode) (by evm_ov)
  have rd3375 := evm_run rd3372 with [
    raw push1 ⟨229⟩ (by clipper_rely_decode) (by evm_ov),
    raw shl (by clipper_rely_decode) (by evm_ov)]
  rw [clipperRelyNotAuthorizedWord] at rd3375
  have rd3377pre := evm_run rd3375 with [
    raw dup2 (by clipper_rely_decode) (by evm_ov)]
  have rd3377 := rd3377pre.mstore 6
    (solcErrorStringMem0 (clipperRelyAuthHashMem I))
    (UInt256.ofNat 5) (by clipper_rely_decode) mem_cost (by rfl) (by native_decide)
    (by evm_ov)
  have rd3389pre := evm_run rd3377 with [
    raw push1 ⟨32⟩ (by clipper_rely_decode) (by evm_ov),
    raw push1 ⟨4⟩ (by clipper_rely_decode) (by evm_ov),
    raw dup3 (by clipper_rely_decode) (by evm_ov),
    raw add (by clipper_rely_decode) (by evm_ov)]
  have rd3390 := rd3389pre.mstore 3
    (solcErrorStringMem1 (clipperRelyAuthHashMem I))
    (UInt256.ofNat 6) (by clipper_rely_decode) mem_cost (by rfl) (by native_decide)
    (by evm_ov)
  have rd3401pre := evm_run rd3390 with [
    raw push1 ⟨22⟩ (by clipper_rely_decode) (by evm_ov),
    raw push1 ⟨36⟩ (by clipper_rely_decode) (by evm_ov),
    raw dup3 (by clipper_rely_decode) (by evm_ov),
    raw add (by clipper_rely_decode) (by evm_ov),
    raw mstore 3 (clipperRelyErrorMem2 I)
      (UInt256.ofNat 7) (by clipper_rely_decode) mem_cost (by rfl)
      (by native_decide) (by evm_ov),
    raw push1 ⟨0⟩ (by clipper_rely_decode) (by evm_ov),
    raw dup1 (by clipper_rely_decode) (by evm_ov),
    raw mload 0 (clipperRelySourceWord I) (UInt256.ofNat 7)
      (by clipper_rely_decode) mem_cost (clipperRelyErrorMem2_mload0 I)
      (by native_decide) (by evm_ov),
    raw push1 ⟨32⟩ (by clipper_rely_decode) (by evm_ov)]
  have rd3400 := rd3401pre.pushConst (⟨9316⟩ : UInt256)
    (width := 2) (op := .PUSH2) (by decide) (by clipper_rely_decode) (by evm_ov)
  have rd3401pre2 := evm_run rd3400 with [
    raw dup4 (by clipper_rely_decode) (by evm_ov)]
  have rd3402 := rd3401pre2.codecopy 0 (clipperRelyErrorCopiedMem code I)
    (UInt256.ofNat 7) (by clipper_rely_decode) mem_cost
    (by
      rw [show (⟨9316⟩ : UInt256).toNat = 9316 from by decide,
        show (⟨32⟩ : UInt256).toNat = 32 from by decide]
      rfl)
    (by native_decide) (by evm_ov)
  have rd3404 := evm_run rd3402 with [
    raw dup2 (by clipper_rely_decode) (by evm_ov),
    raw mload 0 clipperRelyNotAuthorizedStringWord (UInt256.ofNat 7)
      (by clipper_rely_decode) mem_cost
      (by simpa [clipperRelyErrorCopiedMem, clipperRelyErrorMem2]
        using clipperRelyCodecopyMload0 v hpatch I)
      (by native_decide) (by evm_ov),
    raw swap2 (by clipper_rely_decode) (by evm_ov)]
  have rd3405 := rd3404.mstore 0 (clipperRelyErrorRestoredMem code I)
    (UInt256.ofNat 7) (by clipper_rely_decode) mem_cost
    (by simp [clipperRelyErrorRestoredMem, clipperRelyErrorCopiedMem])
    (by native_decide) (by evm_ov)
  have rd3409pre := evm_run rd3405 with [
    raw push1 ⟨68⟩ (by clipper_rely_decode) (by evm_ov),
    raw dup3 (by clipper_rely_decode) (by evm_ov),
    raw add (by clipper_rely_decode) (by evm_ov)]
  have rd3410 := rd3409pre.mstore 3 (clipperRelyErrorStringMem code I)
    (UInt256.ofNat 8) (by clipper_rely_decode) mem_cost
    (by
      rw [show ((⟨128⟩ : UInt256) + ⟨68⟩).toNat = 196 from by decide])
    (by native_decide) (by evm_ov)
  have rd3412 := evm_run rd3410 with [
    raw swap1 (by clipper_rely_decode) (by evm_ov),
    raw mload 0 ⟨128⟩ (UInt256.ofNat 8) (by clipper_rely_decode) mem_cost
      (clipperRelyErrorStringMem_mload64 v hpatch I)
      (by native_decide) (by evm_ov)]
  exact evm_run rd3412 with [
    raw swap1 (by clipper_rely_decode) (by evm_ov),
    raw dup2 (by clipper_rely_decode) (by evm_ov),
    raw swap1 (by clipper_rely_decode) (by evm_ov),
    raw sub (by clipper_rely_decode) (by evm_ov),
    raw push1 ⟨100⟩ (by clipper_rely_decode) (by evm_ov),
    raw add (by clipper_rely_decode) (by evm_ov),
    raw swap1 (by clipper_rely_decode) (by evm_ov),
    raw rev 0 (by clipper_rely_decode) mem_cost (by evm_ov)]

set_option maxHeartbeats 1000000 in
theorem clipperRelyX_storeAuthorized {cA σ I} {g : Sat256} {s0 : State} {k C : ℕ}
    {sel : UInt256} (v : ClipperImmutables) {code : ByteArray}
    (hpatch : patchRuntime clipperBytecode (patches v) = some code)
    (hperm : I.perm = true)
    (h : RD code I g s0 ⟨3422⟩
      [clipperRelyUsrMaskedWord I, ⟨502⟩, sel]
      (clipperRelyAuthHashMem I) (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    RDret code g s0
      (cA, sstoreAccountMap I.codeOwner σ (clipperRelyUsrStorageSlot I) ⟨1⟩)
      ByteArray.empty := by
  have hstoreSlot :
      UInt256.ofNat (fromByteArrayBigEndian
          (ffi.KEC ((clipperRelyStoreHashMem I).readWithPadding 0 64))) =
        mapSlot (clipperRelyUsrMaskedWord I) ⟨0⟩ := by
    simpa [clipperRelyStoreHashMem, mapSlot, solcMappingSlot] using
      twoWordHashMem_solcMappingSlot (⟨0⟩ : UInt256) (clipperRelyUsrMaskedWord I)
        (clipperRelyAuthHashMem_size I)
  have rd3432pre := evm_run h with [
    raw jumpdest (by clipper_rely_decode) (by evm_ov),
    raw push1 ⟨1⟩ (by clipper_rely_decode) (by evm_ov),
    raw push1 ⟨1⟩ (by clipper_rely_decode) (by evm_ov),
    raw push1 ⟨160⟩ (by clipper_rely_decode) (by evm_ov),
    raw shl (by clipper_rely_decode) (by evm_ov),
    raw sub (by clipper_rely_decode) (by evm_ov),
    raw dup2 (by clipper_rely_decode) (by evm_ov),
    raw and (by clipper_rely_decode) (by evm_ov)]
  have hmask :
      UInt256.land (clipperRelyUsrMaskedWord I)
          (UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨160⟩) ⟨1⟩) =
        clipperRelyUsrMaskedWord I := by
    rw [show UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨160⟩) ⟨1⟩ =
      solcAddrMask from by decide]
    exact solcAddrMask_clean (clipperRelyUsrMaskedWord_canonical I)
  rw [hmask] at rd3432pre
  have rd3437pre := evm_run rd3432pre with [
    raw push1 ⟨0⟩ (by clipper_rely_decode) (by evm_ov),
    raw dup2 (by clipper_rely_decode) (by evm_ov),
    raw dup2 (by clipper_rely_decode) (by evm_ov)]
  have rd3438 := rd3437pre.mstore 0
    (wordAt0Mem (clipperRelyUsrMaskedWord I) (clipperRelyAuthHashMem I))
    (UInt256.ofNat 3) (by clipper_rely_decode) mem_cost (by rfl) (by native_decide)
    (by evm_ov)
  have rd3442pre := evm_run rd3438 with [
    raw push1 ⟨32⟩ (by clipper_rely_decode) (by evm_ov),
    raw dup2 (by clipper_rely_decode) (by evm_ov),
    raw swap1 (by clipper_rely_decode) (by evm_ov)]
  have rd3443 := rd3442pre.mstore 0 (clipperRelyStoreHashMem I)
    (UInt256.ofNat 3) (by clipper_rely_decode) mem_cost (by rfl) (by native_decide)
    (by evm_ov)
  have rd3447 := evm_run rd3443 with [
    raw push1 ⟨64⟩ (by clipper_rely_decode) (by evm_ov),
    raw dup1 (by clipper_rely_decode) (by evm_ov),
    raw dup3 (by clipper_rely_decode) (by evm_ov)]
  have rd3448 := rd3447.keccak256 0 (mapSlot (clipperRelyUsrMaskedWord I) ⟨0⟩)
    (UInt256.ofNat 3) (by clipper_rely_decode) mem_cost hstoreSlot (by native_decide)
    (by evm_ov)
  have rd3451pre := evm_run rd3448 with [
    raw push1 ⟨1⟩ (by clipper_rely_decode) (by evm_ov),
    raw swap1 (by clipper_rely_decode) (by evm_ov)]
  obtain ⟨_, _, rd3452raw⟩ := rd3451pre.sstore hperm (by clipper_rely_decode)
    (by simp only [List.length_cons, List.length_nil]; omega)
  have rd3453 := evm_run rd3452raw with [
    raw mload 0 ⟨128⟩ (UInt256.ofNat 3) (by clipper_rely_decode) mem_cost
      (clipperRelyStoreHashMem_mload64 I) (by native_decide) (by evm_ov)]
  have rd3486 := rd3453.pushConst
    (⟨99986234382112180548053307940146098591310749102190014697170127658504464915040⟩ :
      UInt256)
    (op := .PUSH32) (width := 32) (by decide) (by clipper_rely_decode) (by evm_ov)
  have rd3488 := evm_run rd3486 with [
    raw swap2 (by clipper_rely_decode) (by evm_ov),
    raw swap1 (by clipper_rely_decode) (by evm_ov)]
  have rd3489 := RD.log2 0 (UInt256.ofNat 3) rd3488 (by clipper_rely_decode) hperm mem_cost
    (by native_decide) (by evm_ov)
  have rd3490 := rd3489.pop (by clipper_rely_decode) (by evm_ov)
  have rd502 := rd3490.jump (by clipper_rely_decode) (clipperRelyReturnJumpDest v hpatch)
    (by evm_ov)
  have rd503 := rd502.jumpdest (by clipper_rely_decode) (by evm_ov)
  simpa [clipperRelyUsrStorageSlot_eq_mapSlot_masked I] using
    RD.stop rd503 (by clipper_rely_decode) (by evm_ov)

theorem clipperX_rely_ok {cA gh bl σ σ₀ A I} {g : Sat256} {sel : UInt256}
    (v : ClipperImmutables) {code : ByteArray}
    (hpatch : patchRuntime clipperBytecode (patches v) = some code)
    (hsz36 : 36 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hperm : I.perm = true) (hauth : clipperRelyAuthWord σ I = ⟨1⟩)
    (hreach : ∃ k C, RD code I g
      (initState cA gh bl σ σ₀ g A I) (⟨837⟩ : UInt256) [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    RDret code g (initState cA gh bl σ σ₀ g A I)
      (cA, sstoreAccountMap I.codeOwner σ (clipperRelyUsrStorageSlot I) ⟨1⟩)
      ByteArray.empty := by
  obtain ⟨_, _, rd3340⟩ := clipperRelyX_decoded (v := v) hpatch hsz36 hsize hreach
  obtain ⟨_, _, rd3422⟩ := clipperRelyX_authorized (v := v) hpatch hauth rd3340
  exact clipperRelyX_storeAuthorized (v := v) hpatch hperm rd3422

theorem clipperX_rely_unauthorized {cA gh bl σ σ₀ A I} {g : Sat256} {sel : UInt256}
    (v : ClipperImmutables) {code : ByteArray}
    (hpatch : patchRuntime clipperBytecode (patches v) = some code)
    (hsz36 : 36 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hauth : clipperRelyAuthWord σ I ≠ ⟨1⟩)
    (hreach : ∃ k C, RD code I g
      (initState cA gh bl σ σ₀ g A I) (⟨837⟩ : UInt256) [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    RDrev code g (initState cA gh bl σ σ₀ g A I) := by
  obtain ⟨_, _, rd3340⟩ := clipperRelyX_decoded (v := v) hpatch hsz36 hsize hreach
  exact clipperRelyX_unauthorized (v := v) hpatch hauth rd3340

theorem clipperRelyBodyCoreOk
    {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256} {sel : UInt256}
    (v : ClipperImmutables) {code : ByteArray}
    (hpatch : patchRuntime clipperBytecode (patches v) = some code)
    (hcode : I.code = code) (hsize : I.calldata.size < UInt256.size)
    (hperm : I.perm = true) (hwv : I.weiValue = ⟨0⟩)
    (hsz36 : 36 ≤ I.calldata.size)
    (hauth : clipperRelyAuthWord σ_evm I = ⟨1⟩)
    (hdispatch : dispatchMsg (contract v) I.calldata = some relyTransition)
    (hdecode :
      decodeCalldataWithMode (config v).abiDecodeMode (relyTransition.params.map Param.name)
        (transitionSignature relyTransition).paramTypes I.calldata = some (clipperRelyStore I))
    (hreach : ∃ k C, RD code I (Sat256.ofUInt256 g)
      (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) (⟨837⟩ : UInt256) [sel]
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
        relyTransition.body
        (.returned { contract := contract v, locals := clipperRelyStore I }
          (clipperRelyPostState evmSolm I) none) := by
    simpa [evmSolm, clipperRelyAuthWord, solcSlotWord, initState,
      Solm.EVM.storageLoad, State.lookupAccount] using
      clipperRelyBodyReturns v evmSolm I
        (by simp only [evmSolm, initState]; exact hwv)
        (by simp [evmSolm, initState])
        hauthWord
  exact (clipperX_rely_ok (v := v) (g := Sat256.ofUInt256 g) hpatch hsz36 hsize
      hperm hauth hreach)
    |>.reEquivExecutionGenAccountMapEquiv hcode hdispatch hdecode hbody
      (by simp [clipperRelyPostState, evmSolm, initState, storageStore_createdAccounts])
      (by
        simpa [clipperRelyPostState, evmSolm, initState, storageStore_accountMap] using
          accountMapEquiv_sstoreAccountMap I.codeOwner (clipperRelyUsrStorageSlot I) ⟨1⟩
            hAccounts)
      (by
        simpa [relyTransition] using
          (returnEquiv.fallthrough (o := ByteArray.empty) (r := none) (t := [])
            (dvs := []) rfl (by native_decide) (by native_decide)))

theorem clipperRelyBodyCoreUnauthorized
    {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256} {sel : UInt256}
    (v : ClipperImmutables) {code : ByteArray}
    (hpatch : patchRuntime clipperBytecode (patches v) = some code)
    (hcode : I.code = code) (hsize : I.calldata.size < UInt256.size)
    (hwv : I.weiValue = ⟨0⟩)
    (hsz36 : 36 ≤ I.calldata.size)
    (hauth : clipperRelyAuthWord σ_evm I ≠ ⟨1⟩)
    (hdispatch : dispatchMsg (contract v) I.calldata = some relyTransition)
    (hdecode :
      decodeCalldataWithMode (config v).abiDecodeMode (relyTransition.params.map Param.name)
        (transitionSignature relyTransition).paramTypes I.calldata = some (clipperRelyStore I))
    (hreach : ∃ k C, RD code I (Sat256.ofUInt256 g)
      (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) (⟨837⟩ : UInt256) [sel]
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
        relyTransition.body .reverted := by
    simpa [evmSolm, clipperRelyAuthWord, solcSlotWord, initState,
      Solm.EVM.storageLoad, State.lookupAccount] using
      clipperRelyBodyReverts v evmSolm I
        (by simp only [evmSolm, initState]; exact hwv)
        (by simp [evmSolm, initState])
        hauthWord
  exact (clipperX_rely_unauthorized (v := v) (g := Sat256.ofUInt256 g) hpatch hsz36
      hsize hauth hreach)
    |>.reEquivExecutionRevert hcode hdispatch hdecode hbody

theorem clipperRelyBodyCoreDecodeFailed_short
    {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256} {sel : UInt256}
    (v : ClipperImmutables) {code : ByteArray}
    (hpatch : patchRuntime clipperBytecode (patches v) = some code)
    (hcode : I.code = code) (hsize : I.calldata.size < UInt256.size)
    (hsz4 : 4 ≤ I.calldata.size) (hshort : I.calldata.size < 36)
    (hdispatch : dispatchMsg (contract v) I.calldata = some relyTransition)
    (hreach : ∃ k C, RD code I (Sat256.ofUInt256 g)
      (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) (⟨837⟩ : UInt256) [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ_evm) k C) :
    runtimeEquivalenceFor (config v) (contract v) cA gh bl σ_evm σ_solm σ₀ g A I := by
  exact (clipperRelyX_shortarg (v := v) (g := Sat256.ofUInt256 g) hpatch hsz4
      hsize hshort hreach)
    |>.reEquivDecodingFailed hcode hdispatch (clipperDecode_rely_none_short v hsz4 hshort)

theorem clipperRelyBody (v : ClipperImmutables) {code : ByteArray}
    (hpatch : patchRuntime clipperBytecode (patches v) = some code)
    {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256}
    (hcode : I.code = code) (hsize : I.calldata.size < UInt256.size)
    (hperm : I.perm = true) (hwv : I.weiValue = ⟨0⟩)
    (hsel : selIs I (clipperSelBytes 17))
    (hAccounts : accountMapEquiv σ_evm σ_solm) :
    runtimeEquivalenceFor (config v) (contract v) cA gh bl σ_evm σ_solm σ₀ g A I := by
  have hsz4 : 4 ≤ I.calldata.size :=
    calldata_size_ge_of_selIs I (clipperSelBytes 17) (by native_decide) hsel
  have hdispatch : dispatchMsg (contract v) I.calldata = some relyTransition :=
    clipperDispatch_rely v hsel
  have hreach := clipperReachRelyBody (cA := cA) (gh := gh) (bl := bl)
    (σ := σ_evm) (σ₀ := σ₀) (A := A) (I := I) (g := Sat256.ofUInt256 g)
    (v := v) hpatch hcode hwv hsz4 hsize hsel
  by_cases hsz36 : 36 ≤ I.calldata.size
  · by_cases hauth : clipperRelyAuthWord σ_evm I = ⟨1⟩
    · exact clipperRelyBodyCoreOk (v := v) hpatch hcode hsize hperm hwv hsz36
        hauth hdispatch (clipperDecode_rely_ok v hsz36) hreach hAccounts
    · exact clipperRelyBodyCoreUnauthorized (v := v) hpatch hcode hsize hwv hsz36
        hauth hdispatch (clipperDecode_rely_ok v hsz36) hreach hAccounts
  · exact clipperRelyBodyCoreDecodeFailed_short (v := v) hpatch hcode hsize hsz4
      (by omega) hdispatch hreach

end Benchmarks.Dss.Clipper
