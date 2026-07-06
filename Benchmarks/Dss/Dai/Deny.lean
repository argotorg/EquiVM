import Benchmarks.Dss.Dai.Dispatch
import Benchmarks.Dss.Dai.Storage

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach Reasoning.Refinement

set_option maxRecDepth 2000000

namespace Benchmarks.Dss.Dai

/-! ## ABI decode and source-level body for `deny(address)` -/

abbrev denyGuyWord (I : ExecutionEnv) : UInt256 :=
  calldataWord I.calldata 4

abbrev denyGuyMaskedWord (I : ExecutionEnv) : UInt256 :=
  UInt256.land solcAddrMask (denyGuyWord I)

abbrev denySourceWord (I : ExecutionEnv) : UInt256 :=
  UInt256.ofNat I.source.val

abbrev denyGuyValue (I : ExecutionEnv) : Value :=
  .address (AccountAddress.ofNat (denyGuyWord I).toNat)

abbrev denyGuyKey (I : ExecutionEnv) : KeyValue :=
  .address (AccountAddress.ofNat (denyGuyWord I).toNat)

abbrev denyAuthKey (I : ExecutionEnv) : KeyValue :=
  .address I.source

abbrev denyStore (I : ExecutionEnv) : Store :=
  (∅ : Store).insert "guy" (denyGuyValue I)

def denyGuyStorageSlot (I : ExecutionEnv) : UInt256 :=
  wardsSlot (denyGuyKey I)

def denyAuthStorageSlot (I : ExecutionEnv) : UInt256 :=
  wardsSlot (denyAuthKey I)

def denyAuthWord (σ : AccountMap) (I : ExecutionEnv) : UInt256 :=
  σ.find? I.codeOwner |>.option ⟨0⟩
    (fun acc => acc.storage.findD (denyAuthStorageSlot I) ⟨0⟩)

def denyPostState (evm : EVM.State) (I : ExecutionEnv) : EVM.State :=
  Solm.EVM.storageStore evm evm.executionEnv.codeOwner (denyGuyStorageSlot I) ⟨0⟩

abbrev denyGuyEvaledRef (I : ExecutionEnv) : EvaledStorageRef :=
  { base := "wards", steps := [.mindex (denyGuyKey I)] }

abbrev denyAuthEvaledRef (I : ExecutionEnv) : EvaledStorageRef :=
  { base := "wards", steps := [.mindex (denyAuthKey I)] }

theorem denyStore_get_guy (I : ExecutionEnv) :
    (denyStore I).get? "guy" = some (denyGuyValue I) := by
  unfold denyStore
  simp

theorem denyStore_wards (I : ExecutionEnv) :
    (denyStore I).get? "wards" = none := by
  unfold denyStore
  rw [store_get_ne _ _ (by native_decide)]
  simp

theorem denyStore_index_guy (I : ExecutionEnv) :
    (denyStore I)["guy"] = denyGuyValue I := by
  unfold denyStore
  rw [Std.HashMap.getElem_insert]
  simp

theorem denyGuyStorageSlot_eq_mapSlot_masked (I : ExecutionEnv) :
    denyGuyStorageSlot I = mapSlot (denyGuyMaskedWord I) ⟨0⟩ := by
  unfold denyGuyStorageSlot wardsSlot denyGuyKey denyGuyMaskedWord
  rw [keyValueToWord_address_ofNat_mask]

theorem denyAuthStorageSlot_eq_mapSlot_source (I : ExecutionEnv) :
    denyAuthStorageSlot I = mapSlot (denySourceWord I) ⟨0⟩ := by
  unfold denyAuthStorageSlot wardsSlot denyAuthKey denySourceWord
  rw [keyValueToWord_address]

theorem daiDecode_deny_ok {I : ExecutionEnv} (hsz36 : 36 ≤ I.calldata.size) :
    decodeCalldataWithMode config.abiDecodeMode (denyTransition.params.map Param.name)
      (transitionSignature denyTransition).paramTypes I.calldata = some (denyStore I) := by
  show decodeCalldataWithMode config.abiDecodeMode ["guy"] [addr] I.calldata = _
  simpa [denyStore, denyGuyValue, denyGuyWord, calldataWord]
    using decodeCalldata_legacyAddress_ok (cd := I.calldata) (x := "guy") hsz36

theorem daiDecode_deny_none_short {I : ExecutionEnv}
    (hsz4 : 4 ≤ I.calldata.size) (hshort : I.calldata.size < 36) :
    decodeCalldataWithMode config.abiDecodeMode (denyTransition.params.map Param.name)
      (transitionSignature denyTransition).paramTypes I.calldata = none := by
  show decodeCalldataWithMode config.abiDecodeMode ["guy"] [addr] I.calldata = none
  simpa using decodeCalldata_legacyAddress_none_short (cd := I.calldata) (x := "guy")
    hsz4 hshort

theorem evalStorageRef_deny_guy (evm : EVM.State) (I : ExecutionEnv) :
    evalStorageRef config { contract := contract, locals := denyStore I } evm
      (wardsRef (.var "guy")) = .ok (denyGuyEvaledRef I) := by
  simp [evalStorageRef, evalStorageRefStep, wardsRef, denyStore, denyGuyValue,
    valueToKey?, EvalResult.bind, EvalResult.ofOption, bind, pure, evalExpr?]

theorem evalStorageRef_deny_auth (evm : EVM.State) (I : ExecutionEnv)
    (hsrc : evm.executionEnv.source = I.source) :
    evalStorageRef config { contract := contract, locals := denyStore I } evm
      (wardsRef sender) = .ok (denyAuthEvaledRef I) := by
  simp [evalStorageRef, evalStorageRefStep, wardsRef, sender, envValue, denyAuthEvaledRef,
    denyAuthKey, hsrc, valueToKey?, EvalResult.bind, EvalResult.ofOption, bind, pure,
    evalExpr?]

theorem denyUInt256_toNat_eq_one {a : UInt256} (h : a.toNat = 1) : a = ⟨1⟩ := by
  apply u256_inj
  simpa using h

theorem evalExpr_deny_auth_true (evm : EVM.State) (I : ExecutionEnv)
    (hsrc : evm.executionEnv.source = I.source)
    (hload :
      Solm.EVM.storageLoad evm evm.executionEnv.codeOwner (denyAuthStorageSlot I) = ⟨1⟩) :
    evalExpr? config { contract := contract, locals := denyStore I } evm
      (.binary .eq (.storage (wardsRef sender)) (.intLit 1)) = .ok (.bool true) := by
  have hstorage :
      evalExpr? config { contract := contract, locals := denyStore I } evm
        (.storage (wardsRef sender)) = .ok (.int 1) := by
    rw [evalExpr_storage_scalar_value
      (cfg := config)
      (solm := { contract := contract, locals := denyStore I })
      (slot := wardsRef sender)
      (er := denyAuthEvaledRef I)
      (t := .int uint256Int)
      (loc := wordLoc (denyAuthStorageSlot I) (.int uint256Int))
      (value := .int 1)
      (hbase := by
        simp [denyStore, wardsRef])
      (her := evalStorageRef_deny_auth evm I hsrc)
      (hty := by
        simp [storageTypeAt?, storageTypeStep?, contract, storageDecls, denyAuthKey, uint256St])
      (hloc := by rfl)
      (hload := by
        simpa [wordLoc, uint256Loc, uint256Int, hload] using
          storageLocLoad_uint256 evm (denyAuthStorageSlot I))]
  simp only [evalExpr?, hstorage, EvalResult.bind, bind, pure]
  rfl

theorem evalExpr_deny_auth_false (evm : EVM.State) (I : ExecutionEnv)
    (hsrc : evm.executionEnv.source = I.source)
    (hload :
      Solm.EVM.storageLoad evm evm.executionEnv.codeOwner (denyAuthStorageSlot I) ≠ ⟨1⟩) :
    evalExpr? config { contract := contract, locals := denyStore I } evm
      (.binary .eq (.storage (wardsRef sender)) (.intLit 1)) = .ok (.bool false) := by
  have hstorage :
      evalExpr? config { contract := contract, locals := denyStore I } evm
        (.storage (wardsRef sender)) =
          .ok (.int (Int.ofNat
            (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner
              (denyAuthStorageSlot I)).toNat)) := by
    exact evalExpr_storage_scalar_value
      (cfg := config)
      (solm := { contract := contract, locals := denyStore I })
      (slot := wardsRef sender)
      (er := denyAuthEvaledRef I)
      (t := .int uint256Int)
      (loc := wordLoc (denyAuthStorageSlot I) (.int uint256Int))
      (hbase := by
        simp [denyStore, wardsRef])
      (her := evalStorageRef_deny_auth evm I hsrc)
      (hty := by
        simp [storageTypeAt?, storageTypeStep?, contract, storageDecls, denyAuthKey, uint256St])
      (hloc := by rfl)
      (hload := by
        simpa [wordLoc, uint256Loc, uint256Int] using
          storageLocLoad_uint256 evm (denyAuthStorageSlot I))
  have hne :
      Value.int (Int.ofNat
          (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner
            (denyAuthStorageSlot I)).toNat) ≠ Value.int 1 := by
    intro hbad
    rw [Value.int.injEq] at hbad
    apply hload
    exact denyUInt256_toNat_eq_one (Int.ofNat.inj hbad)
  have hbeq :
      (Value.int (Int.ofNat
          (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner
            (denyAuthStorageSlot I)).toNat) == Value.int 1) = false := by
    exact beq_eq_false_iff_ne.mpr hne
  simp only [evalExpr?, hstorage, EvalResult.bind, bind, pure]
  change evalBinaryOp? BinaryOp.eq
      (Value.int (Int.ofNat
        (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner (denyAuthStorageSlot I)).toNat))
      (Value.int 1) = .ok (.bool false)
  simp only [evalBinaryOp?]
  rw [hbeq]

theorem evalExpr_deny_zero (evm : EVM.State) (I : ExecutionEnv) :
    evalExpr? config { contract := contract, locals := denyStore I } evm
      (.intLit 0) = .ok (.int 0) := by
  simp [evalExpr?, pure]

theorem denyAssign (evm : EVM.State) (I : ExecutionEnv) :
    assignStorageRef? config { contract := contract, locals := denyStore I } evm
      .storage (wardsRef (.var "guy")) (.int 0) =
        .ok ({ contract := contract, locals := denyStore I }, denyPostState evm I) := by
  apply assignStorageRef_storage_scalar
      (ty := uint256St)
      (loc := wordLoc (denyGuyStorageSlot I) (.int uint256Int))
      (hbase := denyStore_wards I)
      (her := evalStorageRef_deny_guy evm I)
      (hty := by
        simp [storageTypeAt?, storageTypeStep?, contract, storageDecls, denyGuyKey, uint256St])
      (hloc := by rfl)
  simpa [denyPostState, wordLoc, uint256Loc, uint256Int] using
    storageLocStore_uint256 evm (denyGuyStorageSlot I) ⟨0⟩

/-- The Solm `deny(address)` body stores `wards[guy] = 0` when `msg.sender` is authorized. -/
theorem daiDenyBodyReturns (evm : EVM.State) (I : ExecutionEnv)
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hsrc : evm.executionEnv.source = I.source)
    (hauth :
      Solm.EVM.storageLoad evm evm.executionEnv.codeOwner (denyAuthStorageSlot I) = ⟨1⟩) :
    ExecTransitionBody config contract evm (denyStore I) denyTransition.body
      (.returned { contract := contract, locals := denyStore I }
        (denyPostState evm I) none) := by
  refine ExecFuncBody.execBlockOK ?_
  simpa [denyTransition, nonpayable, auth] using
    nonpayableRequireAssignStorageBlock
      (cfg := config)
      (solm := { contract := contract, locals := denyStore I })
      (evm := evm)
      (evm' := denyPostState evm I)
      (guard := .binary .eq (.storage (wardsRef sender)) (.intLit 1))
      (rhs := .intLit 0)
      (ref := wardsRef (.var "guy"))
      (value := .int 0)
      hwv
      (evalExpr_deny_auth_true evm I hsrc hauth)
      (evalExpr_deny_zero evm I)
      (denyAssign evm I)

/-- The Solm `deny(address)` body reverts when `msg.sender` is not authorized. -/
theorem daiDenyBodyReverts (evm : EVM.State) (I : ExecutionEnv)
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hsrc : evm.executionEnv.source = I.source)
    (hauth :
      Solm.EVM.storageLoad evm evm.executionEnv.codeOwner (denyAuthStorageSlot I) ≠ ⟨1⟩) :
    ExecTransitionBody config contract evm (denyStore I) denyTransition.body .reverted := by
  refine ExecFuncBody.execBlockRevert ?_
  simpa [denyTransition, nonpayable, auth] using
    nonpayableSecondRequireReverts
      (cfg := config)
      (solm := { contract := contract, locals := denyStore I })
      (evm := evm)
      (guard := .binary .eq (.storage (wardsRef sender)) (.intLit 1))
      (rest := [.assign .storage (wardsRef (.var "guy")) (.intLit 0)])
      hwv
      (evalExpr_deny_auth_false evm I hsrc hauth)

/-! ## EVM trace -/

noncomputable abbrev denyAuthHashMem (I : ExecutionEnv) : ByteArray :=
  twoWordHashMem (denySourceWord I) ⟨0⟩ solcFreePtrMem

noncomputable abbrev denyStoreHashMem (I : ExecutionEnv) : ByteArray :=
  twoWordHashMem (denyGuyMaskedWord I) ⟨0⟩ (denyAuthHashMem I)

theorem denyGuyMaskedWord_canonical (I : ExecutionEnv) :
    (denyGuyMaskedWord I).toNat < EVM.addressModulus := by
  unfold denyGuyMaskedWord
  rw [u256_land_comm solcAddrMask (denyGuyWord I)]
  exact solcAddrMask_result_canonical (denyGuyWord I)

theorem denyAuthHashMem_size (I : ExecutionEnv) :
    (denyAuthHashMem I).size = 96 := by
  exact twoWordHashMem_size_96 (denySourceWord I) ⟨0⟩ solcFreePtrMem_size

theorem denyAuthHashMem_read64 (I : ExecutionEnv) :
    (denyAuthHashMem I).readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩ := by
  exact twoWordHashMem_read64 (denySourceWord I) ⟨0⟩ solcFreePtrMem_size
    solcFreePtrMem_read64

theorem denyStoreHashMem_size (I : ExecutionEnv) :
    (denyStoreHashMem I).size = 96 := by
  exact twoWordHashMem_size_96 (denyGuyMaskedWord I) ⟨0⟩ (denyAuthHashMem_size I)

theorem denyNotAuthorizedWord :
    UInt256.shiftLeft (⟨0x11185a4bdb9bdd0b585d5d1a1bdc9a5e9959⟩ : UInt256) ⟨114⟩ =
      ⟨0x4461692f6e6f742d617574686f72697a65640000000000000000000000000000⟩ := by
  native_decide

theorem daiDenyX_decoded {cA gh bl σ σ₀ A I} {g : Sat256} {sel : UInt256}
    (hsz36 : 36 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hreach : ∃ k C, RD daiBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨908⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    ∃ k C, RD daiBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨3221⟩
        [denyGuyMaskedWord I, ⟨686⟩, sel]
        solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
  obtain ⟨_, _, rd930⟩ := RD.daiOneAddressExternalLenOk
    (entry := ⟨908⟩) (ret := ⟨686⟩) (routine := ⟨3221⟩) hreach
    dai_one_address_external_entry_wf (by jump_dest) hsz36 hsize
  obtain ⟨_, _, rd3221⟩ := RD.daiOneAddressExternalMaskAndJumpMasked
    (entry := ⟨908⟩) (ret := ⟨686⟩) (routine := ⟨3221⟩) (R := [sel])
    rd930 dai_one_address_external_entry_wf (by jump_dest)
    (by simp only [List.length_singleton]; omega)
  exact ⟨_, _, by simpa [denyGuyMaskedWord, denyGuyWord, calldataWord] using rd3221⟩

theorem daiDenyX_shortarg {cA gh bl σ σ₀ A I} {g : Sat256} {sel : UInt256}
    (hsz4 : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hshort : I.calldata.size < 36)
    (hreach : ∃ k C, RD daiBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨908⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    RDrev daiBytecode g (initState cA gh bl σ σ₀ g A I) := by
  exact RD.daiOneAddressExternalShort
    (entry := ⟨908⟩) (ret := ⟨686⟩) (routine := ⟨3221⟩)
    hreach dai_one_address_external_entry_wf hsz4 hsize hshort

set_option maxHeartbeats 1000000 in
theorem daiDenyX_authorized {cA σ I} {g : Sat256} {s0 : State} {k C : ℕ}
    {sel : UInt256} (hauth : denyAuthWord σ I = ⟨1⟩)
    (h : RD daiBytecode I g s0 ⟨3221⟩
      [denyGuyMaskedWord I, ⟨686⟩, sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    ∃ k' C', RD daiBytecode I g s0 ⟨3310⟩
      [denyGuyMaskedWord I, ⟨686⟩, sel]
      (denyAuthHashMem I) (UInt256.ofNat 3) ByteArray.empty (cA, σ) k' C' := by
  have hauthSlot :
      UInt256.ofNat (fromByteArrayBigEndian
          (ffi.KEC ((denyAuthHashMem I).readWithPadding 0 64))) =
        mapSlot (denySourceWord I) ⟨0⟩ := by
    simpa [denyAuthHashMem, mapSlot, solcMappingSlot] using
      twoWordHashMem_solcMappingSlot (⟨0⟩ : UInt256) (denySourceWord I)
        solcFreePtrMem_size
  have rd3227pre := evm_run h with [
    raw jumpdest (by native_decide) (by evm_ov),
    raw caller (by native_decide) (by evm_ov),
    raw push1 ⟨0⟩ (by native_decide) (by evm_ov),
    raw swap1 (by native_decide) (by evm_ov),
    raw dup2 (by native_decide) (by evm_ov)]
  have rd3228 := rd3227pre.mstore 0 (wordAt0Mem (denySourceWord I) solcFreePtrMem)
    (UInt256.ofNat 3) (by native_decide) mem_cost (by rfl) (by native_decide) (by evm_ov)
  have rd3232pre := evm_run rd3228 with [
    raw push1 ⟨32⟩ (by native_decide) (by evm_ov),
    raw dup2 (by native_decide) (by evm_ov),
    raw swap1 (by native_decide) (by evm_ov)]
  have rd3233 := rd3232pre.mstore 0 (denyAuthHashMem I)
    (UInt256.ofNat 3) (by native_decide) mem_cost (by rfl) (by native_decide) (by evm_ov)
  have rd3237pre := evm_run rd3233 with [
    raw push1 ⟨64⟩ (by native_decide) (by evm_ov),
    raw swap1 (by native_decide) (by evm_ov)]
  have rd3237 := rd3237pre.keccak256 0 (mapSlot (denySourceWord I) ⟨0⟩)
    (UInt256.ofNat 3) (by native_decide) mem_cost hauthSlot (by native_decide)
    (by evm_ov)
  obtain ⟨k3238, C3238, rd3238raw⟩ := rd3237.sload (by native_decide) (by evm_ov)
  have rd3238 : RD daiBytecode I g s0 ⟨3238⟩
      (denyAuthWord σ I :: denyGuyMaskedWord I :: ⟨686⟩ :: [sel])
      (denyAuthHashMem I) (UInt256.ofNat 3) ByteArray.empty (cA, σ) k3238 C3238 := by
    simpa [denyAuthWord, denyAuthStorageSlot_eq_mapSlot_source I] using rd3238raw
  have rd3241pre := evm_run rd3238 with [
    raw push1 ⟨1⟩ (by native_decide) (by evm_ov),
    raw eq (by native_decide) (by evm_ov)]
  rw [hauth, u256_eq_refl] at rd3241pre
  have rd3244 := rd3241pre.pushConst (⟨3310⟩ : UInt256)
    (width := 2) (op := .PUSH2) (by decide) (by native_decide) (by evm_ov)
  exact ⟨_, _, rd3244.jumpiT (by native_decide) one_ne_zero_uint
    (by jump_dest) (by evm_ov)⟩

set_option maxHeartbeats 1000000 in
theorem daiDenyX_unauthorized {cA σ I} {g : Sat256} {s0 : State} {k C : ℕ}
    {sel : UInt256} (hauth : denyAuthWord σ I ≠ ⟨1⟩)
    (h : RD daiBytecode I g s0 ⟨3221⟩
      [denyGuyMaskedWord I, ⟨686⟩, sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    RDrev daiBytecode g s0 := by
  have hauthSlot :
      UInt256.ofNat (fromByteArrayBigEndian
          (ffi.KEC ((denyAuthHashMem I).readWithPadding 0 64))) =
        mapSlot (denySourceWord I) ⟨0⟩ := by
    simpa [denyAuthHashMem, mapSlot, solcMappingSlot] using
      twoWordHashMem_solcMappingSlot (⟨0⟩ : UInt256) (denySourceWord I)
        solcFreePtrMem_size
  have rd3227pre := evm_run h with [
    raw jumpdest (by native_decide) (by evm_ov),
    raw caller (by native_decide) (by evm_ov),
    raw push1 ⟨0⟩ (by native_decide) (by evm_ov),
    raw swap1 (by native_decide) (by evm_ov),
    raw dup2 (by native_decide) (by evm_ov)]
  have rd3228 := rd3227pre.mstore 0 (wordAt0Mem (denySourceWord I) solcFreePtrMem)
    (UInt256.ofNat 3) (by native_decide) mem_cost (by rfl) (by native_decide) (by evm_ov)
  have rd3232pre := evm_run rd3228 with [
    raw push1 ⟨32⟩ (by native_decide) (by evm_ov),
    raw dup2 (by native_decide) (by evm_ov),
    raw swap1 (by native_decide) (by evm_ov)]
  have rd3233 := rd3232pre.mstore 0 (denyAuthHashMem I)
    (UInt256.ofNat 3) (by native_decide) mem_cost (by rfl) (by native_decide) (by evm_ov)
  have rd3237pre := evm_run rd3233 with [
    raw push1 ⟨64⟩ (by native_decide) (by evm_ov),
    raw swap1 (by native_decide) (by evm_ov)]
  have rd3237 := rd3237pre.keccak256 0 (mapSlot (denySourceWord I) ⟨0⟩)
    (UInt256.ofNat 3) (by native_decide) mem_cost hauthSlot (by native_decide)
    (by evm_ov)
  obtain ⟨k3238, C3238, rd3238raw⟩ := rd3237.sload (by native_decide) (by evm_ov)
  have rd3238 : RD daiBytecode I g s0 ⟨3238⟩
      (denyAuthWord σ I :: denyGuyMaskedWord I :: ⟨686⟩ :: [sel])
      (denyAuthHashMem I) (UInt256.ofNat 3) ByteArray.empty (cA, σ) k3238 C3238 := by
    simpa [denyAuthWord, denyAuthStorageSlot_eq_mapSlot_source I] using rd3238raw
  have rd3241pre := evm_run rd3238 with [
    raw push1 ⟨1⟩ (by native_decide) (by evm_ov),
    raw eq (by native_decide) (by evm_ov)]
  have heq : UInt256.eq (⟨1⟩ : UInt256) (denyAuthWord σ I) = ⟨0⟩ := by
    exact u256_eq_of_ne (by intro hbad; exact hauth hbad.symm)
  rw [heq] at rd3241pre
  have rd3244 := rd3241pre.pushConst (⟨3310⟩ : UInt256)
    (width := 2) (op := .PUSH2) (by decide) (by native_decide) (by evm_ov)
  have rd3245 := rd3244.jumpiNT (by native_decide) rfl (by evm_ov)
  exact RD.solcErrorStringRevertTail
    (pc := ⟨3245⟩)
    (len := ⟨18⟩)
    (rawWord := ⟨0x11185a4bdb9bdd0b585d5d1a1bdc9a5e9959⟩)
    (shift := ⟨114⟩)
    (word := ⟨0x4461692f6e6f742d617574686f72697a65640000000000000000000000000000⟩)
    (op := .PUSH18)
    (width := 18)
    rd3245
    (by
      unfold solcErrorStringRevertTailWf
      repeat' first | apply And.intro | native_decide)
    (by decide)
    denyNotAuthorizedWord
    (denyAuthHashMem_size I)
    (denyAuthHashMem_read64 I)
    (by simp only [List.length_cons, List.length_nil]; omega)

set_option maxHeartbeats 1000000 in
theorem daiDenyX_storeAuthorized {cA σ I} {g : Sat256} {s0 : State} {k C : ℕ}
    {sel : UInt256} (hperm : I.perm = true)
    (h : RD daiBytecode I g s0 ⟨3310⟩
      [denyGuyMaskedWord I, ⟨686⟩, sel]
      (denyAuthHashMem I) (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    RDret daiBytecode g s0
      (cA, sstoreAccountMap I.codeOwner σ (denyGuyStorageSlot I) ⟨0⟩)
      ByteArray.empty := by
  have hstoreSlot :
      UInt256.ofNat (fromByteArrayBigEndian
          (ffi.KEC ((denyStoreHashMem I).readWithPadding 0 64))) =
        mapSlot (denyGuyMaskedWord I) ⟨0⟩ := by
    simpa [denyStoreHashMem, mapSlot, solcMappingSlot] using
      twoWordHashMem_solcMappingSlot (⟨0⟩ : UInt256) (denyGuyMaskedWord I)
        (denyAuthHashMem_size I)
  have rd3319pre := evm_run h with [
    raw jumpdest (by native_decide) (by evm_ov),
    raw push1 ⟨1⟩ (by native_decide) (by evm_ov),
    raw push1 ⟨1⟩ (by native_decide) (by evm_ov),
    raw push1 ⟨160⟩ (by native_decide) (by evm_ov),
    raw shl (by native_decide) (by evm_ov),
    raw sub (by native_decide) (by evm_ov),
    raw and (by native_decide) (by evm_ov)]
  have hmask :
      UInt256.land
          (UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨160⟩) ⟨1⟩)
          (denyGuyMaskedWord I)
        = denyGuyMaskedWord I := by
    rw [u256_land_comm]
    rw [show UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨160⟩) ⟨1⟩ =
      solcAddrMask from by decide]
    exact solcAddrMask_clean (denyGuyMaskedWord_canonical I)
  rw [hmask] at rd3319pre
  have rd3324pre := evm_run rd3319pre with [
    raw push1 ⟨0⟩ (by native_decide) (by evm_ov),
    raw swap1 (by native_decide) (by evm_ov),
    raw dup2 (by native_decide) (by evm_ov)]
  have rd3325 := rd3324pre.mstore 0
    (wordAt0Mem (denyGuyMaskedWord I) (denyAuthHashMem I))
    (UInt256.ofNat 3) (by native_decide) mem_cost (by rfl) (by native_decide)
    (by evm_ov)
  have rd3329pre := evm_run rd3325 with [
    raw push1 ⟨32⟩ (by native_decide) (by evm_ov),
    raw dup2 (by native_decide) (by evm_ov),
    raw swap1 (by native_decide) (by evm_ov)]
  have rd3330 := rd3329pre.mstore 0 (denyStoreHashMem I)
    (UInt256.ofNat 3) (by native_decide) mem_cost (by rfl) (by native_decide)
    (by evm_ov)
  have rd3333pre := evm_run rd3330 with [
    raw push1 ⟨64⟩ (by native_decide) (by evm_ov),
    raw dup2 (by native_decide) (by evm_ov)]
  have rd3334 := rd3333pre.keccak256 0 (mapSlot (denyGuyMaskedWord I) ⟨0⟩)
    (UInt256.ofNat 3) (by native_decide) mem_cost hstoreSlot (by native_decide)
    (by evm_ov)
  obtain ⟨_, _, rd3335raw⟩ := rd3334.sstore hperm (by native_decide)
    (by simp only [List.length_cons, List.length_nil]; omega)
  have rd686 := rd3335raw.jump (by native_decide) (by jump_dest) (by evm_ov)
  have rd687 := rd686.jumpdest (by native_decide) (by evm_ov)
  simpa [denyGuyStorageSlot_eq_mapSlot_masked I] using
    RD.stop rd687 (by native_decide) (by evm_ov)

theorem daiX_deny_ok {cA gh bl σ σ₀ A I} {g : Sat256} {sel : UInt256}
    (hsz36 : 36 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hperm : I.perm = true) (hauth : denyAuthWord σ I = ⟨1⟩)
    (hreach : ∃ k C, RD daiBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨908⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    RDret daiBytecode g (initState cA gh bl σ σ₀ g A I)
      (cA, sstoreAccountMap I.codeOwner σ (denyGuyStorageSlot I) ⟨0⟩)
      ByteArray.empty := by
  obtain ⟨_, _, rd3221⟩ := daiDenyX_decoded (g := g) hsz36 hsize hreach
  obtain ⟨_, _, rd3310⟩ := daiDenyX_authorized (I := I) hauth rd3221
  exact daiDenyX_storeAuthorized hperm rd3310

theorem daiX_deny_unauthorized {cA gh bl σ σ₀ A I} {g : Sat256} {sel : UInt256}
    (hsz36 : 36 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hauth : denyAuthWord σ I ≠ ⟨1⟩)
    (hreach : ∃ k C, RD daiBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨908⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    RDrev daiBytecode g (initState cA gh bl σ σ₀ g A I) := by
  obtain ⟨_, _, rd3221⟩ := daiDenyX_decoded (g := g) hsz36 hsize hreach
  exact daiDenyX_unauthorized (I := I) hauth rd3221

theorem daiDenyBodyCoreOk
    {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256} {sel : UInt256}
    (hcode : I.code = daiBytecode) (hsize : I.calldata.size < UInt256.size)
    (hperm : I.perm = true) (hwv : I.weiValue = ⟨0⟩)
    (hsz36 : 36 ≤ I.calldata.size)
    (hauth : denyAuthWord σ_evm I = ⟨1⟩)
    (hdispatch : dispatchMsg contract I.calldata = some denyTransition)
    (hdecode :
      decodeCalldataWithMode config.abiDecodeMode (denyTransition.params.map Param.name)
        (transitionSignature denyTransition).paramTypes I.calldata = some (denyStore I))
    (hreach : ∃ k C, RD daiBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) ⟨908⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ_evm) k C)
    (hAccounts : accountMapEquiv σ_evm σ_solm) :
    runtimeEquivalenceFor config contract cA gh bl σ_evm σ_solm σ₀ g A I := by
  let evmSolm := initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I
  have hauthWord : denyAuthWord σ_solm I = ⟨1⟩ := by
    have hword : denyAuthWord σ_evm I = denyAuthWord σ_solm I :=
      accountMapEquiv_storage_findD hAccounts I.codeOwner (denyAuthStorageSlot I) ⟨0⟩
    rw [← hword]
    exact hauth
  have hbody :
      ExecTransitionBody config contract evmSolm (denyStore I)
        denyTransition.body
        (.returned { contract := contract, locals := denyStore I }
          (denyPostState evmSolm I) none) := by
    simpa [evmSolm, denyAuthWord, initState, Solm.EVM.storageLoad,
      State.lookupAccount] using
      daiDenyBodyReturns evmSolm I
        (by simp only [evmSolm, initState]; exact hwv)
        (by simp [evmSolm, initState])
        hauthWord
  exact (daiX_deny_ok (g := Sat256.ofUInt256 g) hsz36 hsize hperm hauth hreach)
    |>.reEquivExecutionGenAccountMapEquiv hcode hdispatch hdecode hbody
      (by
        simp [denyPostState, evmSolm, initState, storageStore_createdAccounts])
      (by
        simpa [denyPostState, evmSolm, initState, storageStore_accountMap] using
          accountMapEquiv_sstoreAccountMap I.codeOwner (denyGuyStorageSlot I) ⟨0⟩
            hAccounts)
      (by
        simpa [denyTransition] using
          (returnEquiv.fallthrough (o := ByteArray.empty) (r := none) (t := [])
            (dvs := []) rfl (by native_decide) (by native_decide)))

theorem daiDenyBodyCoreUnauthorized
    {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256} {sel : UInt256}
    (hcode : I.code = daiBytecode) (hsize : I.calldata.size < UInt256.size)
    (hwv : I.weiValue = ⟨0⟩)
    (hsz36 : 36 ≤ I.calldata.size)
    (hauth : denyAuthWord σ_evm I ≠ ⟨1⟩)
    (hdispatch : dispatchMsg contract I.calldata = some denyTransition)
    (hdecode :
      decodeCalldataWithMode config.abiDecodeMode (denyTransition.params.map Param.name)
        (transitionSignature denyTransition).paramTypes I.calldata = some (denyStore I))
    (hreach : ∃ k C, RD daiBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) ⟨908⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ_evm) k C)
    (hAccounts : accountMapEquiv σ_evm σ_solm) :
    runtimeEquivalenceFor config contract cA gh bl σ_evm σ_solm σ₀ g A I := by
  let evmSolm := initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I
  have hauthWord : denyAuthWord σ_solm I ≠ ⟨1⟩ := by
    have hword : denyAuthWord σ_evm I = denyAuthWord σ_solm I :=
      accountMapEquiv_storage_findD hAccounts I.codeOwner (denyAuthStorageSlot I) ⟨0⟩
    intro hbad
    exact hauth (by rw [hword, hbad])
  have hbody :
      ExecTransitionBody config contract evmSolm (denyStore I)
        denyTransition.body .reverted := by
    simpa [evmSolm, denyAuthWord, initState, Solm.EVM.storageLoad,
      State.lookupAccount] using
      daiDenyBodyReverts evmSolm I
        (by simp only [evmSolm, initState]; exact hwv)
        (by simp [evmSolm, initState])
        hauthWord
  exact (daiX_deny_unauthorized (g := Sat256.ofUInt256 g) hsz36 hsize hauth hreach)
    |>.reEquivExecutionRevert hcode hdispatch hdecode hbody

theorem daiDenyBodyCoreDecodeFailed_short
    {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256} {sel : UInt256}
    (hcode : I.code = daiBytecode) (hsize : I.calldata.size < UInt256.size)
    (hsz4 : 4 ≤ I.calldata.size) (hshort : I.calldata.size < 36)
    (hdispatch : dispatchMsg contract I.calldata = some denyTransition)
    (hreach : ∃ k C, RD daiBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) ⟨908⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ_evm) k C) :
    runtimeEquivalenceFor config contract cA gh bl σ_evm σ_solm σ₀ g A I := by
  have hdec := daiDecode_deny_none_short (I := I) hsz4 hshort
  exact (daiDenyX_shortarg (g := Sat256.ofUInt256 g) hsz4 hsize hshort hreach)
    |>.reEquivDecodingFailed hcode hdispatch hdec

/-- `deny(address)` body refines its Solm transition. -/
theorem daiDenyBodyCore {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256}
    (hcode : I.code = daiBytecode) (hsize : I.calldata.size < UInt256.size)
    (hperm : I.perm = true) (hwv : I.weiValue = ⟨0⟩)
    (hsel : selIs I (daiSelBytes 5))
    (hAccounts : accountMapEquiv σ_evm σ_solm) :
    runtimeEquivalenceFor config contract cA gh bl σ_evm σ_solm σ₀ g A I := by
  have hsz4 : 4 ≤ I.calldata.size :=
    calldata_size_ge_of_selIs I (daiSelBytes 5) (by native_decide) hsel
  have hdispatch : dispatchMsg contract I.calldata = some denyTransition :=
    daiDispatchDeny hsel
  have hreach := daiReachDenyBody (cA := cA) (gh := gh) (bl := bl)
    (σ := σ_evm) (σ₀ := σ₀) (A := A) (I := I) (g := Sat256.ofUInt256 g)
    hcode hwv hsz4 hsize hsel
  by_cases hsz36 : 36 ≤ I.calldata.size
  · by_cases hauth : denyAuthWord σ_evm I = ⟨1⟩
    · exact daiDenyBodyCoreOk hcode hsize hperm hwv hsz36 hauth hdispatch
        (daiDecode_deny_ok hsz36) hreach hAccounts
    · exact daiDenyBodyCoreUnauthorized hcode hsize hwv hsz36 hauth hdispatch
        (daiDecode_deny_ok hsz36) hreach hAccounts
  · exact daiDenyBodyCoreDecodeFailed_short hcode hsize hsz4 (by omega)
      hdispatch hreach

end Benchmarks.Dss.Dai
