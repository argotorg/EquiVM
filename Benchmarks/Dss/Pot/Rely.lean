import Benchmarks.Dss.Pot.Dispatch

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach Reasoning.Refinement

set_option maxRecDepth 2000000

namespace Benchmarks.Dss.Pot

/-! ## `rely(address)` — auth writer, `wards[guy] = 1` (mapping slot 0). Group @114 arm 0. -/

abbrev relyGuyWord (I : ExecutionEnv) : UInt256 :=
  calldataWord I.calldata 4

abbrev relyGuyMaskedWord (I : ExecutionEnv) : UInt256 :=
  UInt256.land solcAddrMask (relyGuyWord I)

abbrev relySourceWord (I : ExecutionEnv) : UInt256 :=
  UInt256.ofNat I.source.val

abbrev relyGuyValue (I : ExecutionEnv) : Value :=
  .address (AccountAddress.ofNat (relyGuyWord I).toNat)

abbrev relyGuyKey (I : ExecutionEnv) : KeyValue :=
  .address (AccountAddress.ofNat (relyGuyWord I).toNat)

abbrev relyAuthKey (I : ExecutionEnv) : KeyValue :=
  .address I.source

abbrev relyStore (I : ExecutionEnv) : Store :=
  (∅ : Store).insert "guy" (relyGuyValue I)

def relyGuyStorageSlot (I : ExecutionEnv) : UInt256 :=
  wardsSlot (relyGuyKey I)

def relyAuthStorageSlot (I : ExecutionEnv) : UInt256 :=
  wardsSlot (relyAuthKey I)

def relyAuthWord (σ : AccountMap) (I : ExecutionEnv) : UInt256 :=
  potSlotWord (relyAuthStorageSlot I) σ I

def relyPostState (evm : EVM.State) (I : ExecutionEnv) : EVM.State :=
  Solm.EVM.storageStore evm evm.executionEnv.codeOwner (relyGuyStorageSlot I) ⟨1⟩

abbrev relyGuyEvaledRef (I : ExecutionEnv) : EvaledStorageRef :=
  { base := "wards", steps := [.mindex (relyGuyKey I)] }

abbrev relyAuthEvaledRef (I : ExecutionEnv) : EvaledStorageRef :=
  { base := "wards", steps := [.mindex (relyAuthKey I)] }

theorem relyStore_wards (I : ExecutionEnv) :
    (relyStore I).get? "wards" = none := by
  unfold relyStore
  rw [store_get_ne _ _ (by native_decide)]
  simp

theorem relySourceWord_toNat (I : ExecutionEnv) :
    (relySourceWord I).toNat = I.source.val := by
  unfold relySourceWord
  exact ulit_toNat' _ (lt_of_lt_of_le I.source.isLt
    (show AccountAddress.size ≤ UInt256.size from by decide))

theorem relyGuyStorageSlot_eq_mapSlot_masked (I : ExecutionEnv) :
    relyGuyStorageSlot I = mapSlot (relyGuyMaskedWord I) ⟨0⟩ := by
  unfold relyGuyStorageSlot wardsSlot relyGuyKey relyGuyMaskedWord
  rw [keyValueToWord_address_ofNat_mask]

theorem relyAuthStorageSlot_eq_mapSlot_source (I : ExecutionEnv) :
    relyAuthStorageSlot I = mapSlot (relySourceWord I) ⟨0⟩ := by
  unfold relyAuthStorageSlot wardsSlot relyAuthKey relySourceWord
  rw [keyValueToWord_address]

theorem potDecode_rely_ok {I : ExecutionEnv} (hsz36 : 36 ≤ I.calldata.size) :
    decodeCalldataWithMode config.abiDecodeMode (relyTransition.params.map Param.name)
      (transitionSignature relyTransition).paramTypes I.calldata = some (relyStore I) := by
  simpa [config, relyTransition, relyStore, relyGuyValue, relyGuyWord, calldataWord] using
    decodeCalldata_legacyAddress_ok (cd := I.calldata) (x := "guy") hsz36

theorem potDecode_rely_none_short {I : ExecutionEnv}
    (hsz4 : 4 ≤ I.calldata.size) (hshort : I.calldata.size < 36) :
    decodeCalldataWithMode config.abiDecodeMode (relyTransition.params.map Param.name)
      (transitionSignature relyTransition).paramTypes I.calldata = none := by
  simpa [config, relyTransition] using
    decodeCalldata_legacyAddress_none_short (cd := I.calldata) (x := "guy") hsz4 hshort

theorem evalStorageRef_rely_guy (evm : EVM.State) (I : ExecutionEnv) :
    evalStorageRef config { contract := contract, locals := relyStore I } evm
      (wardsRef (.var "guy")) = .ok (relyGuyEvaledRef I) := by
  simp [evalStorageRef, evalStorageRefStep, wardsRef, relyStore, relyGuyValue,
    valueToKey?, EvalResult.bind, EvalResult.ofOption, bind, pure, evalExpr?]

theorem evalStorageRef_rely_auth (evm : EVM.State) (I : ExecutionEnv)
    (hsrc : evm.executionEnv.source = I.source) :
    evalStorageRef config { contract := contract, locals := relyStore I } evm
      (wardsRef sender) = .ok (relyAuthEvaledRef I) := by
  simp [evalStorageRef, evalStorageRefStep, wardsRef, sender, envValue, relyAuthEvaledRef,
    relyAuthKey, hsrc, valueToKey?, EvalResult.bind, EvalResult.ofOption, bind, pure,
    evalExpr?]

theorem uint256_toNat_eq_one {a : UInt256} (h : a.toNat = 1) : a = ⟨1⟩ := by
  apply u256_inj
  simpa using h

theorem evalExpr_rely_auth_true (evm : EVM.State) (I : ExecutionEnv)
    (hsrc : evm.executionEnv.source = I.source)
    (hload :
      Solm.EVM.storageLoad evm evm.executionEnv.codeOwner (relyAuthStorageSlot I) = ⟨1⟩) :
    evalExpr? config { contract := contract, locals := relyStore I } evm
      (.binary .eq (.storage (wardsRef sender)) (.intLit 1)) = .ok (.bool true) := by
  have hstorage :
      evalExpr? config { contract := contract, locals := relyStore I } evm
        (.storage (wardsRef sender)) = .ok (.int 1) := by
    rw [evalExpr_storage_scalar_value
      (cfg := config)
      (solm := { contract := contract, locals := relyStore I })
      (slot := wardsRef sender)
      (er := relyAuthEvaledRef I)
      (t := .int uint256Int)
      (loc := wordLoc (relyAuthStorageSlot I))
      (value := .int 1)
      (hbase := by simp [relyStore, wardsRef])
      (her := evalStorageRef_rely_auth evm I hsrc)
      (hty := by simp [storageTypeAt?, storageTypeStep?, contract, storageDecls, uint256St])
      (hloc := by rfl)
      (hload := by
        simpa [hload] using potStorageLocLoad_uint256 evm (relyAuthStorageSlot I))]
  simp only [evalExpr?, hstorage, EvalResult.bind, bind, pure]
  rfl

theorem evalExpr_rely_auth_false (evm : EVM.State) (I : ExecutionEnv)
    (hsrc : evm.executionEnv.source = I.source)
    (hload :
      Solm.EVM.storageLoad evm evm.executionEnv.codeOwner (relyAuthStorageSlot I) ≠ ⟨1⟩) :
    evalExpr? config { contract := contract, locals := relyStore I } evm
      (.binary .eq (.storage (wardsRef sender)) (.intLit 1)) = .ok (.bool false) := by
  have hstorage :
      evalExpr? config { contract := contract, locals := relyStore I } evm
        (.storage (wardsRef sender)) =
          .ok (.int (Int.ofNat
            (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner
              (relyAuthStorageSlot I)).toNat)) := by
    exact evalExpr_storage_scalar_value
      (cfg := config)
      (solm := { contract := contract, locals := relyStore I })
      (slot := wardsRef sender)
      (er := relyAuthEvaledRef I)
      (t := .int uint256Int)
      (loc := wordLoc (relyAuthStorageSlot I))
      (hbase := by simp [relyStore, wardsRef])
      (her := evalStorageRef_rely_auth evm I hsrc)
      (hty := by simp [storageTypeAt?, storageTypeStep?, contract, storageDecls, uint256St])
      (hloc := by rfl)
      (hload := by
        exact potStorageLocLoad_uint256 evm (relyAuthStorageSlot I))
  have hne :
      Value.int (Int.ofNat
          (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner
            (relyAuthStorageSlot I)).toNat) ≠ Value.int 1 := by
    intro hbad
    rw [Value.int.injEq] at hbad
    apply hload
    exact uint256_toNat_eq_one (Int.ofNat.inj hbad)
  have hbeq :
      (Value.int (Int.ofNat
          (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner
            (relyAuthStorageSlot I)).toNat) == Value.int 1) = false := by
    exact beq_eq_false_iff_ne.mpr hne
  simp only [evalExpr?, hstorage, EvalResult.bind, bind, pure]
  change evalBinaryOp? BinaryOp.eq
      (Value.int (Int.ofNat
        (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner (relyAuthStorageSlot I)).toNat))
      (Value.int 1) = .ok (.bool false)
  simp only [evalBinaryOp?]
  rw [hbeq]

theorem relyAssign (evm : EVM.State) (I : ExecutionEnv) :
    assignStorageRef? config { contract := contract, locals := relyStore I } evm
      .storage (wardsRef (.var "guy")) (.int 1) =
        .ok ({ contract := contract, locals := relyStore I }, relyPostState evm I) := by
  apply assignStorageRef_storage_scalar
      (ty := uint256St)
      (loc := wordLoc (relyGuyStorageSlot I))
      (hbase := relyStore_wards I)
      (her := evalStorageRef_rely_guy evm I)
      (hty := by simp [storageTypeAt?, storageTypeStep?, contract, storageDecls, uint256St])
      (hloc := by rfl)
  simpa [relyPostState] using
    potStorageLocStore_uint256 evm (relyGuyStorageSlot I) ⟨1⟩

theorem potRelyBodyReturns (evm : EVM.State) (I : ExecutionEnv)
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hsrc : evm.executionEnv.source = I.source)
    (hauth :
      Solm.EVM.storageLoad evm evm.executionEnv.codeOwner (relyAuthStorageSlot I) = ⟨1⟩) :
    ExecTransitionBody config contract evm (relyStore I) relyTransition.body
      (.returned { contract := contract, locals := relyStore I } (relyPostState evm I) none) := by
  refine ExecFuncBody.execBlockOK ?_
  simpa [relyTransition, nonpayable, auth] using
    nonpayableRequireAssignStorageBlock
      (cfg := config)
      (solm := { contract := contract, locals := relyStore I })
      (evm := evm)
      (evm' := relyPostState evm I)
      (guard := .binary .eq (.storage (wardsRef sender)) (.intLit 1))
      (rhs := .intLit 1)
      (ref := wardsRef (.var "guy"))
      (value := .int 1)
      hwv
      (evalExpr_rely_auth_true evm I hsrc hauth)
      (by simp [evalExpr?, pure])
      (relyAssign evm I)

theorem potRelyBodyReverts (evm : EVM.State) (I : ExecutionEnv)
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hsrc : evm.executionEnv.source = I.source)
    (hauth :
      Solm.EVM.storageLoad evm evm.executionEnv.codeOwner (relyAuthStorageSlot I) ≠ ⟨1⟩) :
    ExecTransitionBody config contract evm (relyStore I) relyTransition.body .reverted := by
  refine ExecFuncBody.execBlockRevert ?_
  simpa [relyTransition, nonpayable, auth] using
    nonpayableSecondRequireReverts
      (cfg := config)
      (solm := { contract := contract, locals := relyStore I })
      (evm := evm)
      (guard := .binary .eq (.storage (wardsRef sender)) (.intLit 1))
      (rest := [.assign .storage (wardsRef (.var "guy")) (.intLit 1)])
      hwv
      (evalExpr_rely_auth_false evm I hsrc hauth)

noncomputable abbrev relyAuthHashMem (I : ExecutionEnv) : ByteArray :=
  twoWordHashMem (relySourceWord I) ⟨0⟩ solcFreePtrMem

noncomputable abbrev relyStoreHashMem (I : ExecutionEnv) : ByteArray :=
  twoWordHashMem (relyGuyMaskedWord I) ⟨0⟩ (relyAuthHashMem I)

theorem relyGuyMaskedWord_canonical (I : ExecutionEnv) :
    (relyGuyMaskedWord I).toNat < EVM.addressModulus := by
  unfold relyGuyMaskedWord
  rw [u256_land_comm solcAddrMask (relyGuyWord I)]
  exact solcAddrMask_result_canonical (relyGuyWord I)

theorem relyAuthHashMem_size (I : ExecutionEnv) :
    (relyAuthHashMem I).size = 96 := by
  exact twoWordHashMem_size_96 (relySourceWord I) ⟨0⟩ solcFreePtrMem_size

theorem relyAuthHashMem_read64 (I : ExecutionEnv) :
    (relyAuthHashMem I).readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩ := by
  exact twoWordHashMem_read64 (relySourceWord I) ⟨0⟩ solcFreePtrMem_size
    solcFreePtrMem_read64

theorem relyStoreHashMem_size (I : ExecutionEnv) :
    (relyStoreHashMem I).size = 96 := by
  exact twoWordHashMem_size_96 (relyGuyMaskedWord I) ⟨0⟩ (relyAuthHashMem_size I)

theorem relyNotAuthorizedWord :
    UInt256.shiftLeft (⟨0x141bdd0bdb9bdd0b585d5d1a1bdc9a5e9959⟩ : UInt256) ⟨114⟩ =
      ⟨0x506f742f6e6f742d617574686f72697a65640000000000000000000000000000⟩ := by
  native_decide

theorem potReachRelyBody {cA gh bl σ σ₀ A I} {g : Sat256}
    (hcode : I.code = potBytecode) (hwv : I.weiValue = ⟨0⟩)
    (hsz : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hsel : selIs I (potSelBytes 12)) :
    ∃ k C, RD potBytecode I g (initState cA gh bl σ σ₀ g A I)
        ⟨462⟩ [potSelWord I] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty
        (cA, σ) k C := by
  have hword : potSelWord I = ⟨0x65fae35e⟩ :=
    potSelWord_eq_of_beq I hsz 0x65 0xfa 0xe3 0x5e ⟨0x65fae35e⟩
      (by native_decide) (by simpa [potSelBytes] using hsel)
  have hroot : UInt256.gt (armSelNat potBytecode potRootSplitPc) (potSelWord I) = ⟨0⟩ := by
    rw [hword]; native_decide
  have h43 : UInt256.gt (armSelNat potBytecode potSplit43Pc) (potSelWord I) ≠ ⟨0⟩ := by
    rw [hword]; native_decide
  have heq0 : ∀ j, j < 0 →
      UInt256.eq (armSelNat potBytecode (nthArmPc potBytecode potG114FirstArmPc j))
        (potSelWord I) = ⟨0⟩ := by intro j hj; omega
  have htake :
      UInt256.eq (armSelNat potBytecode (nthArmPc potBytecode potG114FirstArmPc 0))
        (potSelWord I) ≠ ⟨0⟩ := by rw [hword]; native_decide
  exact potReachG114Body 0 (by omega) ⟨462⟩ hcode hwv hsz hsize hroot h43 heq0 htake
    (by jump_dest) (by native_decide)

theorem potRelyX_decoded {cA gh bl σ σ₀ A I} {g : Sat256} {sel : UInt256}
    (hsz36 : 36 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hreach : ∃ k C, RD potBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨462⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    ∃ k C, RD potBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨1372⟩
        [relyGuyMaskedWord I, ⟨301⟩, sel]
        solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
  obtain ⟨_, _, hdecoded⟩ := RD.solcOneAddressExternalLenOk
    (code := potBytecode) (sel := sel) (entry := ⟨462⟩) (ret := ⟨301⟩)
    (decoded := ⟨484⟩) hreach
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by jump_dest) hsz36 hsize
  obtain ⟨_, _, hroutine⟩ := RD.solcOneAddressExternalMaskAndJumpMasked
    (code := potBytecode) (decoded := ⟨484⟩) (ret := ⟨301⟩) (routine := ⟨1372⟩)
    (R := [sel]) hdecoded
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by jump_dest) (by simp)
  exact ⟨_, _, by simpa [relyGuyMaskedWord, relyGuyWord, calldataWord] using hroutine⟩

theorem potRelyX_shortarg {cA gh bl σ σ₀ A I} {g : Sat256} {sel : UInt256}
    (hsz4 : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hshort : I.calldata.size < 36)
    (hreach : ∃ k C, RD potBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨462⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    RDrev potBytecode g (initState cA gh bl σ σ₀ g A I) := by
  have hlt :
      UInt256.lt (UInt256.sub (UInt256.ofNat I.calldata.size) ⟨4⟩) ⟨32⟩ = ⟨1⟩ := by
    apply ult_one
    rw [usub_ofNat_word_toNat (by simpa using hsz4) hsize]
    change I.calldata.size - 4 < 32
    omega
  exact RD.solcExternalStaticArgsShortReverts
    (code := potBytecode) (sel := sel) (entry := ⟨462⟩) (ret := ⟨301⟩)
    (decoded := ⟨484⟩) (need := ⟨32⟩) hreach
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) hlt

set_option maxHeartbeats 1000000 in
theorem potRelyX_authorized {cA σ I} {g : Sat256} {s0 : State} {k C : ℕ}
    {sel : UInt256} (hauth : relyAuthWord σ I = ⟨1⟩)
    (h : RD potBytecode I g s0 ⟨1372⟩
      [relyGuyMaskedWord I, ⟨301⟩, sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    ∃ k' C', RD potBytecode I g s0 ⟨1461⟩
      [relyGuyMaskedWord I, ⟨301⟩, sel]
      (relyAuthHashMem I) (UInt256.ofNat 3) ByteArray.empty (cA, σ) k' C' := by
  have hauthSlot :
      UInt256.ofNat (fromByteArrayBigEndian
          (ffi.KEC ((relyAuthHashMem I).readWithPadding 0 64))) =
        mapSlot (relySourceWord I) ⟨0⟩ := by
    simpa [relyAuthHashMem, mapSlot, solcMappingSlot] using
      twoWordHashMem_solcMappingSlot (⟨0⟩ : UInt256) (relySourceWord I)
        solcFreePtrMem_size
  have rd1378pre := evm_run h with [
    raw jumpdest (by native_decide) (by evm_ov),
    raw caller (by native_decide) (by evm_ov),
    raw push1 ⟨0⟩ (by native_decide) (by evm_ov),
    raw swap1 (by native_decide) (by evm_ov),
    raw dup2 (by native_decide) (by evm_ov)]
  have rd1379 := rd1378pre.mstore 0 (wordAt0Mem (relySourceWord I) solcFreePtrMem)
    (UInt256.ofNat 3) (by native_decide) mem_cost (by rfl) (by native_decide) (by evm_ov)
  have rd1383pre := evm_run rd1379 with [
    raw push1 ⟨32⟩ (by native_decide) (by evm_ov),
    raw dup2 (by native_decide) (by evm_ov),
    raw swap1 (by native_decide) (by evm_ov)]
  have rd1384 := rd1383pre.mstore 0 (relyAuthHashMem I)
    (UInt256.ofNat 3) (by native_decide) mem_cost (by rfl) (by native_decide) (by evm_ov)
  have rd1387pre := evm_run rd1384 with [
    raw push1 ⟨64⟩ (by native_decide) (by evm_ov),
    raw swap1 (by native_decide) (by evm_ov)]
  have rd1388 := rd1387pre.keccak256 0 (mapSlot (relySourceWord I) ⟨0⟩)
    (UInt256.ofNat 3) (by native_decide) mem_cost hauthSlot (by native_decide)
    (by evm_ov)
  obtain ⟨k1389, C1389, rd1389raw⟩ := rd1388.sload (by native_decide) (by evm_ov)
  have rd1389 : RD potBytecode I g s0 ⟨1389⟩
      (relyAuthWord σ I :: relyGuyMaskedWord I :: ⟨301⟩ :: [sel])
      (relyAuthHashMem I) (UInt256.ofNat 3) ByteArray.empty (cA, σ) k1389 C1389 := by
    simpa [relyAuthWord, potSlotWord, relyAuthStorageSlot_eq_mapSlot_source I] using rd1389raw
  have rd1392pre := evm_run rd1389 with [
    raw push1 ⟨1⟩ (by native_decide) (by evm_ov),
    raw eq (by native_decide) (by evm_ov)]
  rw [hauth, u256_eq_refl] at rd1392pre
  have rd1395 := rd1392pre.pushConst (⟨1461⟩ : UInt256)
    (width := 2) (op := .PUSH2) (by decide) (by native_decide) (by evm_ov)
  exact ⟨_, _, rd1395.jumpiT (by native_decide) one_ne_zero_uint
    (by jump_dest) (by evm_ov)⟩

set_option maxHeartbeats 1000000 in
theorem potRelyX_unauthorized {cA σ I} {g : Sat256} {s0 : State} {k C : ℕ}
    {sel : UInt256} (hauth : relyAuthWord σ I ≠ ⟨1⟩)
    (h : RD potBytecode I g s0 ⟨1372⟩
      [relyGuyMaskedWord I, ⟨301⟩, sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    RDrev potBytecode g s0 := by
  have hauthSlot :
      UInt256.ofNat (fromByteArrayBigEndian
          (ffi.KEC ((relyAuthHashMem I).readWithPadding 0 64))) =
        mapSlot (relySourceWord I) ⟨0⟩ := by
    simpa [relyAuthHashMem, mapSlot, solcMappingSlot] using
      twoWordHashMem_solcMappingSlot (⟨0⟩ : UInt256) (relySourceWord I)
        solcFreePtrMem_size
  have rd1378pre := evm_run h with [
    raw jumpdest (by native_decide) (by evm_ov),
    raw caller (by native_decide) (by evm_ov),
    raw push1 ⟨0⟩ (by native_decide) (by evm_ov),
    raw swap1 (by native_decide) (by evm_ov),
    raw dup2 (by native_decide) (by evm_ov)]
  have rd1379 := rd1378pre.mstore 0 (wordAt0Mem (relySourceWord I) solcFreePtrMem)
    (UInt256.ofNat 3) (by native_decide) mem_cost (by rfl) (by native_decide) (by evm_ov)
  have rd1383pre := evm_run rd1379 with [
    raw push1 ⟨32⟩ (by native_decide) (by evm_ov),
    raw dup2 (by native_decide) (by evm_ov),
    raw swap1 (by native_decide) (by evm_ov)]
  have rd1384 := rd1383pre.mstore 0 (relyAuthHashMem I)
    (UInt256.ofNat 3) (by native_decide) mem_cost (by rfl) (by native_decide) (by evm_ov)
  have rd1387pre := evm_run rd1384 with [
    raw push1 ⟨64⟩ (by native_decide) (by evm_ov),
    raw swap1 (by native_decide) (by evm_ov)]
  have rd1388 := rd1387pre.keccak256 0 (mapSlot (relySourceWord I) ⟨0⟩)
    (UInt256.ofNat 3) (by native_decide) mem_cost hauthSlot (by native_decide)
    (by evm_ov)
  obtain ⟨k1389, C1389, rd1389raw⟩ := rd1388.sload (by native_decide) (by evm_ov)
  have rd1389 : RD potBytecode I g s0 ⟨1389⟩
      (relyAuthWord σ I :: relyGuyMaskedWord I :: ⟨301⟩ :: [sel])
      (relyAuthHashMem I) (UInt256.ofNat 3) ByteArray.empty (cA, σ) k1389 C1389 := by
    simpa [relyAuthWord, potSlotWord, relyAuthStorageSlot_eq_mapSlot_source I] using rd1389raw
  have rd1392pre := evm_run rd1389 with [
    raw push1 ⟨1⟩ (by native_decide) (by evm_ov),
    raw eq (by native_decide) (by evm_ov)]
  have heq : UInt256.eq (⟨1⟩ : UInt256) (relyAuthWord σ I) = ⟨0⟩ := by
    exact u256_eq_of_ne (by intro hbad; exact hauth hbad.symm)
  rw [heq] at rd1392pre
  have rd1395 := rd1392pre.pushConst (⟨1461⟩ : UInt256)
    (width := 2) (op := .PUSH2) (by decide) (by native_decide) (by evm_ov)
  have rd1396 := rd1395.jumpiNT (by native_decide) rfl (by evm_ov)
  exact RD.solcErrorStringRevertTail
    (pc := ⟨1396⟩)
    (len := ⟨18⟩)
    (rawWord := ⟨0x141bdd0bdb9bdd0b585d5d1a1bdc9a5e9959⟩)
    (shift := ⟨114⟩)
    (word := ⟨0x506f742f6e6f742d617574686f72697a65640000000000000000000000000000⟩)
    (op := .PUSH18)
    (width := 18)
    rd1396
    (by
      unfold solcErrorStringRevertTailWf
      repeat' first | apply And.intro | native_decide)
    (by decide)
    relyNotAuthorizedWord
    (relyAuthHashMem_size I)
    (relyAuthHashMem_read64 I)
    (by simp only [List.length_cons, List.length_nil]; omega)

set_option maxHeartbeats 1000000 in
theorem potRelyX_storeAuthorized {cA σ I} {g : Sat256} {s0 : State} {k C : ℕ}
    {sel : UInt256} (hperm : I.perm = true)
    (h : RD potBytecode I g s0 ⟨1461⟩
      [relyGuyMaskedWord I, ⟨301⟩, sel]
      (relyAuthHashMem I) (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    RDret potBytecode g s0
      (cA, sstoreAccountMap I.codeOwner σ (relyGuyStorageSlot I) ⟨1⟩)
      ByteArray.empty := by
  have hstoreSlot :
      UInt256.ofNat (fromByteArrayBigEndian
          (ffi.KEC ((relyStoreHashMem I).readWithPadding 0 64))) =
        mapSlot (relyGuyMaskedWord I) ⟨0⟩ := by
    simpa [relyStoreHashMem, mapSlot, solcMappingSlot] using
      twoWordHashMem_solcMappingSlot (⟨0⟩ : UInt256) (relyGuyMaskedWord I)
        (relyAuthHashMem_size I)
  have rd1471pre := evm_run h with [
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
          (relyGuyMaskedWord I)
        = relyGuyMaskedWord I := by
    rw [u256_land_comm]
    rw [show UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨160⟩) ⟨1⟩ =
      solcAddrMask from by decide]
    exact solcAddrMask_clean (relyGuyMaskedWord_canonical I)
  rw [hmask] at rd1471pre
  have rd1476pre := evm_run rd1471pre with [
    raw push1 ⟨0⟩ (by native_decide) (by evm_ov),
    raw swap1 (by native_decide) (by evm_ov),
    raw dup2 (by native_decide) (by evm_ov)]
  have rd1477 := rd1476pre.mstore 0
    (wordAt0Mem (relyGuyMaskedWord I) (relyAuthHashMem I))
    (UInt256.ofNat 3) (by native_decide) mem_cost (by rfl) (by native_decide)
    (by evm_ov)
  have rd1481pre := evm_run rd1477 with [
    raw push1 ⟨32⟩ (by native_decide) (by evm_ov),
    raw dup2 (by native_decide) (by evm_ov),
    raw swap1 (by native_decide) (by evm_ov)]
  have rd1482 := rd1481pre.mstore 0 (relyStoreHashMem I)
    (UInt256.ofNat 3) (by native_decide) mem_cost (by rfl) (by native_decide)
    (by evm_ov)
  have rd1485pre := evm_run rd1482 with [
    raw push1 ⟨64⟩ (by native_decide) (by evm_ov),
    raw swap1 (by native_decide) (by evm_ov)]
  have rd1486 := rd1485pre.keccak256 0 (mapSlot (relyGuyMaskedWord I) ⟨0⟩)
    (UInt256.ofNat 3) (by native_decide) mem_cost hstoreSlot (by native_decide)
    (by evm_ov)
  have rd1489pre := evm_run rd1486 with [
    raw push1 ⟨1⟩ (by native_decide) (by evm_ov),
    raw swap1 (by native_decide) (by evm_ov)]
  obtain ⟨_, _, rd1490raw⟩ := rd1489pre.sstore hperm (by native_decide)
    (by simp only [List.length_cons, List.length_nil]; omega)
  have rd301 := rd1490raw.jump (by native_decide) (by jump_dest) (by evm_ov)
  have rd302 := rd301.jumpdest (by native_decide) (by evm_ov)
  simpa [relyGuyStorageSlot_eq_mapSlot_masked I] using
    RD.stop rd302 (by native_decide) (by evm_ov)

theorem potX_rely_ok {cA gh bl σ σ₀ A I} {g : Sat256} {sel : UInt256}
    (hsz36 : 36 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hperm : I.perm = true) (hauth : relyAuthWord σ I = ⟨1⟩)
    (hreach : ∃ k C, RD potBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨462⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    RDret potBytecode g (initState cA gh bl σ σ₀ g A I)
      (cA, sstoreAccountMap I.codeOwner σ (relyGuyStorageSlot I) ⟨1⟩)
      ByteArray.empty := by
  obtain ⟨_, _, rd1372⟩ := potRelyX_decoded (g := g) hsz36 hsize hreach
  obtain ⟨_, _, rd1461⟩ := potRelyX_authorized (I := I) hauth rd1372
  exact potRelyX_storeAuthorized hperm rd1461

theorem potX_rely_unauthorized {cA gh bl σ σ₀ A I} {g : Sat256} {sel : UInt256}
    (hsz36 : 36 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hauth : relyAuthWord σ I ≠ ⟨1⟩)
    (hreach : ∃ k C, RD potBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨462⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    RDrev potBytecode g (initState cA gh bl σ σ₀ g A I) := by
  obtain ⟨_, _, rd1372⟩ := potRelyX_decoded (g := g) hsz36 hsize hreach
  exact potRelyX_unauthorized (I := I) hauth rd1372

theorem potRelyBodyCoreOk
    {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256} {sel : UInt256}
    (hcode : I.code = potBytecode) (hsize : I.calldata.size < UInt256.size)
    (hperm : I.perm = true) (hwv : I.weiValue = ⟨0⟩)
    (hsz36 : 36 ≤ I.calldata.size)
    (hauth : relyAuthWord σ_evm I = ⟨1⟩)
    (hdispatch : dispatchMsg contract I.calldata = some relyTransition)
    (hdecode :
      decodeCalldataWithMode config.abiDecodeMode (relyTransition.params.map Param.name)
        (transitionSignature relyTransition).paramTypes I.calldata = some (relyStore I))
    (hreach : ∃ k C, RD potBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) ⟨462⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ_evm) k C)
    (hAccounts : accountMapEquiv σ_evm σ_solm) :
    runtimeEquivalenceFor config contract cA gh bl σ_evm σ_solm σ₀ g A I := by
  let evmSolm := initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I
  have hauthWord : relyAuthWord σ_solm I = ⟨1⟩ := by
    have hword : relyAuthWord σ_evm I = relyAuthWord σ_solm I :=
      accountMapEquiv_storage_findD hAccounts I.codeOwner (relyAuthStorageSlot I) ⟨0⟩
    rw [← hword]
    exact hauth
  have hbody :
      ExecTransitionBody config contract evmSolm (relyStore I)
        relyTransition.body
        (.returned { contract := contract, locals := relyStore I }
          (relyPostState evmSolm I) none) := by
    simpa [evmSolm, relyAuthWord, potSlotWord, initState, Solm.EVM.storageLoad,
      State.lookupAccount] using
      potRelyBodyReturns evmSolm I
        (by simp only [evmSolm, initState]; exact hwv)
        (by simp [evmSolm, initState])
        hauthWord
  exact (potX_rely_ok (g := Sat256.ofUInt256 g) hsz36 hsize hperm hauth hreach)
    |>.reEquivExecutionGenAccountMapEquiv hcode hdispatch hdecode hbody
      (by simp [relyPostState, evmSolm, initState, storageStore_createdAccounts])
      (by
        simpa [relyPostState, evmSolm, initState, storageStore_accountMap] using
          accountMapEquiv_sstoreAccountMap I.codeOwner (relyGuyStorageSlot I) ⟨1⟩
            hAccounts)
      (by
        simpa [relyTransition] using
          (returnEquiv.fallthrough (o := ByteArray.empty) (r := none) (t := [])
            (dvs := []) rfl (by native_decide) (by native_decide)))

theorem potRelyBodyCoreUnauthorized
    {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256} {sel : UInt256}
    (hcode : I.code = potBytecode) (hsize : I.calldata.size < UInt256.size)
    (hwv : I.weiValue = ⟨0⟩)
    (hsz36 : 36 ≤ I.calldata.size)
    (hauth : relyAuthWord σ_evm I ≠ ⟨1⟩)
    (hdispatch : dispatchMsg contract I.calldata = some relyTransition)
    (hdecode :
      decodeCalldataWithMode config.abiDecodeMode (relyTransition.params.map Param.name)
        (transitionSignature relyTransition).paramTypes I.calldata = some (relyStore I))
    (hreach : ∃ k C, RD potBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) ⟨462⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ_evm) k C)
    (hAccounts : accountMapEquiv σ_evm σ_solm) :
    runtimeEquivalenceFor config contract cA gh bl σ_evm σ_solm σ₀ g A I := by
  let evmSolm := initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I
  have hauthWord : relyAuthWord σ_solm I ≠ ⟨1⟩ := by
    have hword : relyAuthWord σ_evm I = relyAuthWord σ_solm I :=
      accountMapEquiv_storage_findD hAccounts I.codeOwner (relyAuthStorageSlot I) ⟨0⟩
    intro hbad
    exact hauth (by rw [hword, hbad])
  have hbody :
      ExecTransitionBody config contract evmSolm (relyStore I)
        relyTransition.body .reverted := by
    simpa [evmSolm, relyAuthWord, potSlotWord, initState, Solm.EVM.storageLoad,
      State.lookupAccount] using
      potRelyBodyReverts evmSolm I
        (by simp only [evmSolm, initState]; exact hwv)
        (by simp [evmSolm, initState])
        hauthWord
  exact (potX_rely_unauthorized (g := Sat256.ofUInt256 g) hsz36 hsize hauth hreach)
    |>.reEquivExecutionRevert hcode hdispatch hdecode hbody

theorem potRelyBodyCoreDecodeFailed_short
    {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256} {sel : UInt256}
    (hcode : I.code = potBytecode) (hsize : I.calldata.size < UInt256.size)
    (hsz4 : 4 ≤ I.calldata.size) (hshort : I.calldata.size < 36)
    (hdispatch : dispatchMsg contract I.calldata = some relyTransition)
    (hreach : ∃ k C, RD potBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) ⟨462⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ_evm) k C) :
    runtimeEquivalenceFor config contract cA gh bl σ_evm σ_solm σ₀ g A I := by
  exact (potRelyX_shortarg (g := Sat256.ofUInt256 g) hsz4 hsize hshort hreach)
    |>.reEquivDecodingFailed hcode hdispatch (potDecode_rely_none_short hsz4 hshort)

theorem potRelyBody {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256}
    (hcode : I.code = potBytecode)
    (hsize : I.calldata.size < UInt256.size)
    (_hperm : I.perm = true)
    (hwv : I.weiValue = ⟨0⟩)
    (hsel : selIs I (potSelBytes 12))
    (hAccounts : accountMapEquiv σ_evm σ_solm) :
    runtimeEquivalenceFor config contract cA gh bl σ_evm σ_solm σ₀ g A I := by
  have hsz4 : 4 ≤ I.calldata.size :=
    calldata_size_ge_of_selIs I (potSelBytes 12) rfl hsel
  have hdispatch : dispatchMsg contract I.calldata = some relyTransition :=
    potDispatchRely hsel
  have hreach := potReachRelyBody (cA := cA) (gh := gh) (bl := bl)
    (σ := σ_evm) (σ₀ := σ₀) (A := A) (I := I) (g := Sat256.ofUInt256 g)
    hcode hwv hsz4 hsize hsel
  by_cases hsz36 : 36 ≤ I.calldata.size
  · by_cases hauth : relyAuthWord σ_evm I = ⟨1⟩
    · exact potRelyBodyCoreOk hcode hsize _hperm hwv hsz36 hauth hdispatch
        (potDecode_rely_ok hsz36) hreach hAccounts
    · exact potRelyBodyCoreUnauthorized hcode hsize hwv hsz36 hauth hdispatch
        (potDecode_rely_ok hsz36) hreach hAccounts
  · exact potRelyBodyCoreDecodeFailed_short hcode hsize hsz4 (by omega)
      hdispatch hreach

end Benchmarks.Dss.Pot
