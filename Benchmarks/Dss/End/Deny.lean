import Benchmarks.Dss.End.Rely

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach Reasoning.Refinement

set_option maxRecDepth 2000000
set_option maxHeartbeats 0

namespace Benchmarks.Dss.End

/-! ## `deny(address)` -/

abbrev endDenyConcreteSelector : ByteArray := selectorBytes 0x9c 0x52 0xa7 0xf1

def endDenyPostState (evm : EVM.State) (I : ExecutionEnv) : EVM.State :=
  Solm.EVM.storageStore evm evm.executionEnv.codeOwner (endRelyUsrStorageSlot I) ⟨0⟩

theorem endDecode_deny_ok {I : ExecutionEnv} (hsz36 : 36 ≤ I.calldata.size) :
    decodeCalldataWithMode config.abiDecodeMode (denyTransition.params.map Param.name)
      (transitionSignature denyTransition).paramTypes I.calldata = some (endRelyStore I) := by
  simpa [config, denyTransition, endRelyStore, endRelyUsrValue, endRelyUsrWord,
    calldataWord] using
    decodeCalldata_legacyAddress_ok (cd := I.calldata) (x := "usr") hsz36

theorem endDecode_deny_none_short {I : ExecutionEnv}
    (hsz4 : 4 ≤ I.calldata.size) (hshort : I.calldata.size < 36) :
    decodeCalldataWithMode config.abiDecodeMode (denyTransition.params.map Param.name)
      (transitionSignature denyTransition).paramTypes I.calldata = none := by
  simpa [config, denyTransition] using
    decodeCalldata_legacyAddress_none_short (cd := I.calldata) (x := "usr") hsz4 hshort

theorem endDenyAssign (evm : EVM.State) (I : ExecutionEnv) :
    assignStorageRef? config { contract := contract, locals := endRelyStore I } evm
      .storage (wardsRef (.var "usr")) (.int 0) =
        .ok ({ contract := contract, locals := endRelyStore I }, endDenyPostState evm I) := by
  apply assignStorageRef_storage_scalar
      (ty := uint256St)
      (loc := wordLoc (endRelyUsrStorageSlot I))
      (hbase := endRelyStore_wards I)
      (her := evalStorageRef_endRely_usr evm I)
      (hty := by simp [storageTypeAt?, storageTypeStep?, contract, storageDecls, uint256St])
      (hloc := by rfl)
  simpa [endDenyPostState] using
    endStorageLocStore_uint256 evm (endRelyUsrStorageSlot I) ⟨0⟩

theorem endDenyBodyReturns (evm : EVM.State) (I : ExecutionEnv)
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hsrc : evm.executionEnv.source = I.source)
    (hauth :
      Solm.EVM.storageLoad evm evm.executionEnv.codeOwner (endRelyAuthStorageSlot I) =
        ⟨1⟩) :
    ExecTransitionBody config contract evm (endRelyStore I) denyTransition.body
      (.returned { contract := contract, locals := endRelyStore I }
        (endDenyPostState evm I) none) := by
  refine ExecFuncBody.execBlockOK ?_
  simpa [denyTransition, nonpayable, auth] using
    nonpayableRequireAssignStorageBlock
      (cfg := config)
      (solm := { contract := contract, locals := endRelyStore I })
      (evm := evm)
      (evm' := endDenyPostState evm I)
      (guard := .binary .eq (.storage (wardsRef sender)) (.intLit 1))
      (rhs := .intLit 0)
      (ref := wardsRef (.var "usr"))
      (value := .int 0)
      hwv
      (evalExpr_endRely_auth_true evm I hsrc hauth)
      (by simp [evalExpr?, pure])
      (endDenyAssign evm I)

theorem endDenyBodyReverts (evm : EVM.State) (I : ExecutionEnv)
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hsrc : evm.executionEnv.source = I.source)
    (hauth :
      Solm.EVM.storageLoad evm evm.executionEnv.codeOwner (endRelyAuthStorageSlot I) ≠
        ⟨1⟩) :
    ExecTransitionBody config contract evm (endRelyStore I) denyTransition.body .reverted := by
  refine ExecFuncBody.execBlockRevert ?_
  simpa [denyTransition, nonpayable, auth] using
    nonpayableSecondRequireReverts
      (cfg := config)
      (solm := { contract := contract, locals := endRelyStore I })
      (evm := evm)
      (guard := .binary .eq (.storage (wardsRef sender)) (.intLit 1))
      (rest := [.assign .storage (wardsRef (.var "usr")) (.intLit 0)])
      hwv
      (evalExpr_endRely_auth_false evm I hsrc hauth)

/-! ### Dispatch reachability -/

abbrev endDenyHighSplitPc : UInt256 := ⟨43⟩
abbrev endDenyHighJumpdestPc : UInt256 := ⟨162⟩
abbrev endDenyMidSplitPc : UInt256 := ⟨163⟩
abbrev endDenyGroupJumpdestPc : UInt256 := ⟨222⟩
abbrev endDenyFirstArmPc : UInt256 := ⟨223⟩
abbrev endDenyEntryPc : UInt256 := ⟨941⟩
abbrev endDenyDecodedPc : UInt256 := ⟨963⟩
abbrev endDenyAuthPc : UInt256 := ⟨7500⟩
abbrev endDenyStorePc : UInt256 := ⟨7589⟩

theorem endDenyHighSplitWellFormed :
    selectorSplitWellFormed endBytecode endDenyHighSplitPc := by
  dsimp [selectorSplitWellFormed]
  repeat' first | apply And.intro | native_decide

theorem endDenyMidSplitWellFormed :
    selectorSplitWellFormed endBytecode endDenyMidSplitPc := by
  dsimp [selectorSplitWellFormed]
  repeat' first | apply And.intro | native_decide

set_option maxHeartbeats 1000000 in
theorem endDenyArmsWellFormed :
    ∀ j, j ≤ 3 → armWellFormed endBytecode (nthArmPc endBytecode endDenyFirstArmPc j) := by
  intro j hj
  interval_cases j <;>
    (dsimp [armWellFormed]
     repeat' first | apply And.intro | native_decide)

theorem endReachDenyBody {cA gh bl σ σ₀ A I} {g : Sat256}
    (hcode : I.code = endBytecode) (hwv : I.weiValue = ⟨0⟩)
    (hsz : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hsel : selIs I endDenyConcreteSelector) :
    ∃ k C, RD endBytecode I g (initState cA gh bl σ σ₀ g A I)
        endDenyEntryPc [endSelWord I] solcFreePtrMem (UInt256.ofNat 3)
        ByteArray.empty (cA, σ) k C := by
  have hword : endSelWord I = ⟨0x9c52a7f1⟩ :=
    endSelWord_eq_of_beq I hsz 0x9c 0x52 0xa7 0xf1 ⟨0x9c52a7f1⟩
      (by native_decide) (by simpa [selIs, endDenyConcreteSelector, selectorBytes] using hsel)
  obtain ⟨k32, C32, h32⟩ :=
    endReachRootSplit (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀)
      (A := A) (I := I) (g := g) hcode hwv hsz hsize
  have h43 : RD endBytecode I g (initState cA gh bl σ σ₀ g A I)
      endDenyHighSplitPc [endSelWord I] solcFreePtrMem (UInt256.ofNat 3)
      ByteArray.empty (cA, σ) (k32 + 5) (C32 + 22) := by
    simpa [endRootSplitPc, endDenyHighSplitPc, selArmNextPc, armTgtWidth,
      selArmJumpiPc, selArmPushTgtPc, selArmEqPc, selArmPush4Pc] using
      RD.selectorSplitNotTakenAuto h32 endRootSplitWellFormed
        (by rw [hword]; native_decide) (by simp)
  have h162 : RD endBytecode I g (initState cA gh bl σ σ₀ g A I)
      endDenyHighJumpdestPc [endSelWord I] solcFreePtrMem (UInt256.ofNat 3)
      ByteArray.empty (cA, σ) (k32 + 5 + 5) (C32 + 22 + 22) := by
    simpa [endDenyHighSplitPc, endDenyHighJumpdestPc] using
      RD.selectorSplitTakenAuto h43 endDenyHighSplitWellFormed
        (by rw [hword]; native_decide) (by jump_dest) (by simp)
  have h163 : RD endBytecode I g (initState cA gh bl σ σ₀ g A I)
      endDenyMidSplitPc [endSelWord I] solcFreePtrMem (UInt256.ofNat 3)
      ByteArray.empty (cA, σ) (k32 + 5 + 5 + 1) (C32 + 22 + 22 + 1) := by
    simpa [endDenyMidSplitPc] using h162.jumpdest (by native_decide) (by simp)
  have h222 : RD endBytecode I g (initState cA gh bl σ σ₀ g A I)
      endDenyGroupJumpdestPc [endSelWord I] solcFreePtrMem (UInt256.ofNat 3)
      ByteArray.empty (cA, σ) (k32 + 5 + 5 + 1 + 5) (C32 + 22 + 22 + 1 + 22) := by
    simpa [endDenyMidSplitPc, endDenyGroupJumpdestPc] using
      RD.selectorSplitTakenAuto h163 endDenyMidSplitWellFormed
        (by rw [hword]; native_decide) (by jump_dest) (by simp)
  have h223 : RD endBytecode I g (initState cA gh bl σ σ₀ g A I)
      endDenyFirstArmPc [endSelWord I] solcFreePtrMem (UInt256.ofNat 3)
      ByteArray.empty (cA, σ) (k32 + 5 + 5 + 1 + 5 + 1)
        (C32 + 22 + 22 + 1 + 22 + 1) := by
    simpa [endDenyFirstArmPc] using h222.jumpdest (by native_decide) (by simp)
  have heq0 : ∀ j, j < 3 →
      UInt256.eq (armSelNat endBytecode (nthArmPc endBytecode endDenyFirstArmPc j))
        (endSelWord I) = ⟨0⟩ := by
    intro j hj
    interval_cases j <;> rw [hword] <;> native_decide
  have htake :
      UInt256.eq (armSelNat endBytecode (nthArmPc endBytecode endDenyFirstArmPc 3))
        (endSelWord I) ≠ ⟨0⟩ := by
    rw [hword]
    native_decide
  exact RD.dispatchTo endDenyEntryPc 3 h223
    (fun j hj => endDenyArmsWellFormed j (le_trans hj (by omega)))
    heq0 htake (by jump_dest) (by native_decide) (by simp)

/-! ### Runtime trace -/

theorem endDenyX_decoded {cA gh bl σ σ₀ A I} {g : Sat256} {sel : UInt256}
    (hsz36 : 36 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hreach : ∃ k C, RD endBytecode I g
      (initState cA gh bl σ σ₀ g A I) endDenyEntryPc [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    ∃ k C, RD endBytecode I g
        (initState cA gh bl σ σ₀ g A I) endDenyAuthPc
        [endRelyUsrMaskedWord I, endRelyReturnPc, sel]
        solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
  obtain ⟨_, _, hdecoded⟩ := RD.solcOneAddressExternalLenOk
    (code := endBytecode) (sel := sel)
    (entry := endDenyEntryPc) (ret := endRelyReturnPc) (decoded := endDenyDecodedPc) hreach
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by jump_dest) hsz36 hsize
  obtain ⟨_, _, hroutine⟩ := RD.solcOneAddressExternalMaskAndJumpMasked
    (code := endBytecode) (decoded := endDenyDecodedPc) (ret := endRelyReturnPc)
    (routine := endDenyAuthPc) (R := [sel]) hdecoded
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by jump_dest) (by simp)
  exact ⟨_, _, by simpa [endRelyUsrMaskedWord, endRelyUsrWord, calldataWord] using hroutine⟩

theorem endDenyX_shortarg {cA gh bl σ σ₀ A I} {g : Sat256} {sel : UInt256}
    (hsz4 : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hshort : I.calldata.size < 36)
    (hreach : ∃ k C, RD endBytecode I g
      (initState cA gh bl σ σ₀ g A I) endDenyEntryPc [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    RDrev endBytecode g (initState cA gh bl σ σ₀ g A I) := by
  have hlt :
      UInt256.lt (UInt256.sub (UInt256.ofNat I.calldata.size) ⟨4⟩) ⟨32⟩ = ⟨1⟩ := by
    apply ult_one
    rw [usub_ofNat_word_toNat (by simpa using hsz4) hsize]
    change I.calldata.size - 4 < 32
    omega
  exact RD.solcExternalStaticArgsShortReverts
    (code := endBytecode) (sel := sel)
    (entry := endDenyEntryPc) (ret := endRelyReturnPc) (decoded := endDenyDecodedPc)
    (need := ⟨32⟩) hreach
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) hlt

theorem endDenyX_authorized {cA σ I} {g : Sat256} {s0 : State} {k C : ℕ}
    {sel : UInt256} (hauth : endRelyAuthWord σ I = ⟨1⟩)
    (h : RD endBytecode I g s0 endDenyAuthPc
      [endRelyUsrMaskedWord I, endRelyReturnPc, sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    ∃ k' C', RD endBytecode I g s0 endDenyStorePc
      [endRelyUsrMaskedWord I, endRelyReturnPc, sel]
      (endRelyAuthHashMem I) (UInt256.ofNat 3) ByteArray.empty (cA, σ) k' C' := by
  have hauthSolc :
      solcSlotWord σ I (solcMappingSlot ⟨0⟩ (solcSourceWord I)) = ⟨1⟩ := by
    simpa [endRelyAuthWord, endSlotWord, endRelyAuthStorageSlot_eq_mapSlot_source I,
      mapSlot] using hauth
  simpa [endRelyAuthHashMem] using
    RD.endAuthCheckOk
      (code := endBytecode) (pc := endDenyAuthPc) (okPc := endDenyStorePc)
      (key := endRelyUsrMaskedWord I) (ret := endRelyReturnPc) (R := [sel])
      h
      (by
        unfold endAuthCheckWf
        repeat' first | apply And.intro | native_decide)
      hauthSolc (by jump_dest) (by simp)

theorem endDenyX_unauthorized {cA σ I} {g : Sat256} {s0 : State} {k C : ℕ}
    {sel : UInt256} (hauth : endRelyAuthWord σ I ≠ ⟨1⟩)
    (h : RD endBytecode I g s0 endDenyAuthPc
      [endRelyUsrMaskedWord I, endRelyReturnPc, sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    RDrev endBytecode g s0 := by
  have hauthSolc :
      solcSlotWord σ I (solcMappingSlot ⟨0⟩ (solcSourceWord I)) ≠ ⟨1⟩ := by
    simpa [endRelyAuthWord, endSlotWord, endRelyAuthStorageSlot_eq_mapSlot_source I,
      mapSlot] using hauth
  exact RD.endAuthCheckRevert
    (code := endBytecode) (pc := endDenyAuthPc) (okPc := endDenyStorePc)
    (key := endRelyUsrMaskedWord I) (ret := endRelyReturnPc) (R := [sel])
    h
    (by
      unfold endAuthCheckWf
      repeat' first | apply And.intro | native_decide)
    (by
      unfold solcErrorStringRevertTailWf endAuthTailPc endNotAuthorizedRawWord
      repeat' first | apply And.intro | native_decide)
    hauthSolc (by simp)

theorem endDenyX_storeAuthorized {cA σ I} {g : Sat256} {s0 : State} {k C : ℕ}
    {sel : UInt256} (hperm : I.perm = true)
    (h : RD endBytecode I g s0 endDenyStorePc
      [endRelyUsrMaskedWord I, endRelyReturnPc, sel]
      (endRelyAuthHashMem I) (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    RDret endBytecode g s0
      (cA, sstoreAccountMap I.codeOwner σ (endRelyUsrStorageSlot I) ⟨0⟩)
      ByteArray.empty := by
  have hstoreSlot :
      UInt256.ofNat (fromByteArrayBigEndian
          (ffi.KEC ((endRelyStoreHashMem I).readWithPadding 0 64))) =
        mapSlot (endRelyUsrMaskedWord I) ⟨0⟩ := by
    simpa [endRelyStoreHashMem, mapSlot, solcMappingSlot] using
      twoWordHashMem_solcMappingSlot (⟨0⟩ : UInt256) (endRelyUsrMaskedWord I)
        (endRelyAuthHashMem_size I)
  have rdMasked := evm_run h with [
    raw jumpdest (by native_decide) (by evm_ov),
    raw push1 ⟨1⟩ (by native_decide) (by evm_ov),
    raw push1 ⟨1⟩ (by native_decide) (by evm_ov),
    raw push1 ⟨160⟩ (by native_decide) (by evm_ov),
    raw shl (by native_decide) (by evm_ov),
    raw sub (by native_decide) (by evm_ov),
    raw dup2 (by native_decide) (by evm_ov),
    raw and (by native_decide) (by evm_ov)]
  have hmask :
      UInt256.land
          (UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨160⟩) ⟨1⟩)
          (endRelyUsrMaskedWord I)
        = endRelyUsrMaskedWord I := by
    rw [u256_land_comm]
    rw [show UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨160⟩) ⟨1⟩ =
      solcAddrMask from by decide]
    exact solcAddrMask_clean (endRelyUsrMaskedWord_canonical I)
  have hmask' :
      UInt256.land (endRelyUsrMaskedWord I)
          (UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨160⟩) ⟨1⟩)
        = endRelyUsrMaskedWord I := by
    rw [u256_land_comm]
    exact hmask
  rw [hmask'] at rdMasked
  have rdMstoreKeyPrefix := evm_run rdMasked with [
    raw push1 ⟨0⟩ (by native_decide) (by evm_ov),
    raw dup2 (by native_decide) (by evm_ov),
    raw dup2 (by native_decide) (by evm_ov)]
  have rdKeyMem := rdMstoreKeyPrefix.mstore 0
    (wordAt0Mem (endRelyUsrMaskedWord I) (endRelyAuthHashMem I))
    (UInt256.ofNat 3) (by native_decide) mem_cost (by rfl) (by native_decide)
    (by evm_ov)
  have rdMstoreSlotPrefix := evm_run rdKeyMem with [
    raw push1 ⟨32⟩ (by native_decide) (by evm_ov),
    raw dup2 (by native_decide) (by evm_ov),
    raw swap1 (by native_decide) (by evm_ov)]
  have rdHashMem := rdMstoreSlotPrefix.mstore 0 (endRelyStoreHashMem I)
    (UInt256.ofNat 3) (by native_decide) mem_cost (by rfl) (by native_decide)
    (by evm_ov)
  have rdKeccakPrefix := evm_run rdHashMem with [
    raw push1 ⟨64⟩ (by native_decide) (by evm_ov),
    raw dup1 (by native_decide) (by evm_ov),
    raw dup3 (by native_decide) (by evm_ov)]
  have rdSlot := rdKeccakPrefix.keccak256 0 (mapSlot (endRelyUsrMaskedWord I) ⟨0⟩)
    (UInt256.ofNat 3) (by native_decide) mem_cost hstoreSlot (by native_decide)
    (by evm_ov)
  have rdSstorePrefix := evm_run rdSlot with [
    raw dup3 (by native_decide) (by evm_ov),
    raw swap1 (by native_decide) (by evm_ov)]
  obtain ⟨_, _, rdStoredRaw⟩ := rdSstorePrefix.sstore hperm (by native_decide)
    (by simp only [List.length_cons, List.length_nil]; omega)
  have rdStored := by
    simpa [endRelyUsrStorageSlot_eq_mapSlot_masked I] using rdStoredRaw
  have rdMload := rdStored.mload 0 ⟨128⟩ (UInt256.ofNat 3) (by native_decide) mem_cost
    (mloadFreePtrValue (by rw [endRelyStoreHashMem_size I]; decide) (by decide)
      (endRelyStoreHashMem_read64 I))
    (by native_decide) (by evm_ov)
  have rdTopic := rdMload.pushConst
    (⟨0x184450df2e323acec0ed3b5c7531b81f9b4cdef7914dfd4c0a4317416bb5251b⟩ :
      UInt256)
    (width := 32) (op := .PUSH32) (by decide) (by native_decide) (by evm_ov)
  have rdLogPrefix := evm_run rdTopic with [
    raw swap2 (by native_decide) (by evm_ov),
    raw swap1 (by native_decide) (by evm_ov)]
  have rdLog := RD.log2
    (a := ⟨128⟩) (b := ⟨0⟩)
    (c := ⟨0x184450df2e323acec0ed3b5c7531b81f9b4cdef7914dfd4c0a4317416bb5251b⟩)
    (d := endRelyUsrMaskedWord I)
    (t := [endRelyUsrMaskedWord I, endRelyReturnPc, sel])
    0
    (UInt256.ofNat
      (MachineState.M (UInt256.ofNat 3).toNat (⟨128⟩ : UInt256).toNat
        (⟨0⟩ : UInt256).toNat))
    rdLogPrefix (by native_decide) hperm mem_cost (by native_decide)
    (by simp only [List.length_cons, List.length_nil]; omega)
  have rdPop := RD.pop (a := endRelyUsrMaskedWord I) (t := [endRelyReturnPc, sel]) rdLog
    (by native_decide) (by evm_ov)
  have rdRet := RD.jump (a := endRelyReturnPc) (t := [sel]) rdPop
    (by native_decide) (by jump_dest) (by evm_ov)
  have rdStopPc := RD.jumpdest (pc := endRelyReturnPc) (stk := [sel]) rdRet
    (by native_decide) (by evm_ov)
  have hstop := RD.stop rdStopPc (by native_decide) (by evm_ov)
  simpa [endRelyUsrStorageSlot_eq_mapSlot_masked I] using hstop

theorem endX_deny_ok {cA gh bl σ σ₀ A I} {g : Sat256} {sel : UInt256}
    (hsz36 : 36 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hperm : I.perm = true) (hauth : endRelyAuthWord σ I = ⟨1⟩)
    (hreach : ∃ k C, RD endBytecode I g
      (initState cA gh bl σ σ₀ g A I) endDenyEntryPc [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    RDret endBytecode g (initState cA gh bl σ σ₀ g A I)
      (cA, sstoreAccountMap I.codeOwner σ (endRelyUsrStorageSlot I) ⟨0⟩)
      ByteArray.empty := by
  obtain ⟨_, _, hdecoded⟩ := endDenyX_decoded (g := g) hsz36 hsize hreach
  obtain ⟨_, _, hokPc⟩ := endDenyX_authorized (I := I) hauth hdecoded
  exact endDenyX_storeAuthorized hperm hokPc

theorem endX_deny_unauthorized {cA gh bl σ σ₀ A I} {g : Sat256} {sel : UInt256}
    (hsz36 : 36 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hauth : endRelyAuthWord σ I ≠ ⟨1⟩)
    (hreach : ∃ k C, RD endBytecode I g
      (initState cA gh bl σ σ₀ g A I) endDenyEntryPc [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    RDrev endBytecode g (initState cA gh bl σ σ₀ g A I) := by
  obtain ⟨_, _, hdecoded⟩ := endDenyX_decoded (g := g) hsz36 hsize hreach
  exact endDenyX_unauthorized (I := I) hauth hdecoded

/-! ### Equivalence wrapper -/

theorem endDenyBodyCoreOk
    {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256} {sel : UInt256}
    (hcode : I.code = endBytecode)
    (hsize : I.calldata.size < UInt256.size)
    (hperm : I.perm = true) (hwv : I.weiValue = ⟨0⟩)
    (hsz36 : 36 ≤ I.calldata.size)
    (hauth : endRelyAuthWord σ_evm I = ⟨1⟩)
    (hdispatch : dispatchMsg contract I.calldata = some denyTransition)
    (hdecode :
      decodeCalldataWithMode config.abiDecodeMode (denyTransition.params.map Param.name)
        (transitionSignature denyTransition).paramTypes I.calldata = some (endRelyStore I))
    (hreach : ∃ k C, RD endBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) endDenyEntryPc [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ_evm) k C)
    (hAccounts : accountMapEquiv σ_evm σ_solm) :
    runtimeEquivalenceFor config contract cA gh bl σ_evm σ_solm σ₀ g A I := by
  let evmSolm := initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I
  have hauthWord : endRelyAuthWord σ_solm I = ⟨1⟩ := by
    have hword : endRelyAuthWord σ_evm I = endRelyAuthWord σ_solm I :=
      accountMapEquiv_storage_findD hAccounts I.codeOwner (endRelyAuthStorageSlot I) ⟨0⟩
    rw [← hword]
    exact hauth
  have hbody :
      ExecTransitionBody config contract evmSolm (endRelyStore I)
        denyTransition.body
        (.returned { contract := contract, locals := endRelyStore I }
          (endDenyPostState evmSolm I) none) := by
    simpa [evmSolm, endRelyAuthWord, endSlotWord, initState, Solm.EVM.storageLoad,
      State.lookupAccount] using
      endDenyBodyReturns evmSolm I
        (by simp only [evmSolm, initState]; exact hwv)
        (by simp [evmSolm, initState])
        hauthWord
  exact (endX_deny_ok (g := Sat256.ofUInt256 g) hsz36 hsize hperm hauth hreach)
    |>.reEquivExecutionGenAccountMapEquiv hcode hdispatch hdecode hbody
      (by simp [endDenyPostState, evmSolm, initState, storageStore_createdAccounts])
      (by
        simpa [endDenyPostState, evmSolm, initState, storageStore_accountMap] using
          accountMapEquiv_sstoreAccountMap I.codeOwner (endRelyUsrStorageSlot I) ⟨0⟩
            hAccounts)
      (by
        simpa [denyTransition] using
          (returnEquiv.fallthrough (o := ByteArray.empty) (r := none) (t := [])
            (dvs := []) rfl (by native_decide) (by native_decide)))

theorem endDenyBodyCoreUnauthorized
    {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256} {sel : UInt256}
    (hcode : I.code = endBytecode)
    (hsize : I.calldata.size < UInt256.size)
    (hwv : I.weiValue = ⟨0⟩)
    (hsz36 : 36 ≤ I.calldata.size)
    (hauth : endRelyAuthWord σ_evm I ≠ ⟨1⟩)
    (hdispatch : dispatchMsg contract I.calldata = some denyTransition)
    (hdecode :
      decodeCalldataWithMode config.abiDecodeMode (denyTransition.params.map Param.name)
        (transitionSignature denyTransition).paramTypes I.calldata = some (endRelyStore I))
    (hreach : ∃ k C, RD endBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) endDenyEntryPc [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ_evm) k C)
    (hAccounts : accountMapEquiv σ_evm σ_solm) :
    runtimeEquivalenceFor config contract cA gh bl σ_evm σ_solm σ₀ g A I := by
  let evmSolm := initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I
  have hauthWord : endRelyAuthWord σ_solm I ≠ ⟨1⟩ := by
    have hword : endRelyAuthWord σ_evm I = endRelyAuthWord σ_solm I :=
      accountMapEquiv_storage_findD hAccounts I.codeOwner (endRelyAuthStorageSlot I) ⟨0⟩
    intro hbad
    exact hauth (by rw [hword, hbad])
  have hbody :
      ExecTransitionBody config contract evmSolm (endRelyStore I)
        denyTransition.body .reverted := by
    simpa [evmSolm, endRelyAuthWord, endSlotWord, initState, Solm.EVM.storageLoad,
      State.lookupAccount] using
      endDenyBodyReverts evmSolm I
        (by simp only [evmSolm, initState]; exact hwv)
        (by simp [evmSolm, initState])
        hauthWord
  exact (endX_deny_unauthorized (g := Sat256.ofUInt256 g) hsz36 hsize hauth hreach)
    |>.reEquivExecutionRevert hcode hdispatch hdecode hbody

theorem endDenyBodyCoreDecodeFailed_short
    {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256} {sel : UInt256}
    (hcode : I.code = endBytecode)
    (hsize : I.calldata.size < UInt256.size)
    (hsz4 : 4 ≤ I.calldata.size) (hshort : I.calldata.size < 36)
    (hdispatch : dispatchMsg contract I.calldata = some denyTransition)
    (hreach : ∃ k C, RD endBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) endDenyEntryPc [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ_evm) k C) :
    runtimeEquivalenceFor config contract cA gh bl σ_evm σ_solm σ₀ g A I := by
  exact (endDenyX_shortarg (g := Sat256.ofUInt256 g) hsz4 hsize hshort hreach)
    |>.reEquivDecodingFailed hcode hdispatch (endDecode_deny_none_short hsz4 hshort)

theorem endDenyBody {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256}
    (hcode : I.code = endBytecode) (hsize : I.calldata.size < UInt256.size)
    (hperm : I.perm = true) (hwv : I.weiValue = ⟨0⟩)
    (hsel : selIs I (selectorOf denyTransition))
    (hAccounts : accountMapEquiv σ_evm σ_solm) :
    runtimeEquivalenceFor config contract cA gh bl σ_evm σ_solm σ₀ g A I := by
  have hsel' : selIs I endDenyConcreteSelector := by
    simpa [endDenySelectorBytes, endDenyConcreteSelector] using hsel
  have hsz4 : 4 ≤ I.calldata.size :=
    calldata_size_ge_of_selIs I endDenyConcreteSelector (by rfl) hsel'
  have hdispatch : dispatchMsg contract I.calldata = some denyTransition :=
    endDispatchDeny hsel
  have hreach := endReachDenyBody (cA := cA) (gh := gh) (bl := bl)
    (σ := σ_evm) (σ₀ := σ₀) (A := A) (I := I) (g := Sat256.ofUInt256 g)
    hcode hwv hsz4 hsize hsel'
  by_cases hsz36 : 36 ≤ I.calldata.size
  · by_cases hauth : endRelyAuthWord σ_evm I = ⟨1⟩
    · exact endDenyBodyCoreOk hcode hsize hperm hwv hsz36 hauth hdispatch
        (endDecode_deny_ok hsz36) hreach hAccounts
    · exact endDenyBodyCoreUnauthorized hcode hsize hwv hsz36 hauth hdispatch
        (endDecode_deny_ok hsz36) hreach hAccounts
  · exact endDenyBodyCoreDecodeFailed_short hcode hsize hsz4 (by omega)
      hdispatch hreach

end Benchmarks.Dss.End
