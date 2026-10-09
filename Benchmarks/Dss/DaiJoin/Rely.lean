import Reasoning.WordArithmetic
import Benchmarks.Dss.DaiJoin.Dispatch

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

set_option maxRecDepth 2000000

namespace Benchmarks.Dss.DaiJoin

/-! ## `rely(address)` -/

abbrev relyUsrWord (I : ExecutionEnv) : UInt256 :=
  calldataWord I.calldata 4

abbrev relyUsrMaskedWord (I : ExecutionEnv) : UInt256 :=
  UInt256.land solcAddrMask (relyUsrWord I)

abbrev relySourceWord (I : ExecutionEnv) : UInt256 :=
  UInt256.ofNat I.source.val

abbrev relyUsrValue (I : ExecutionEnv) : Value :=
  .address (AccountAddress.ofNat (relyUsrWord I).toNat)

abbrev relyUsrKey (I : ExecutionEnv) : KeyValue :=
  .address (AccountAddress.ofNat (relyUsrWord I).toNat)

abbrev relyAuthKey (I : ExecutionEnv) : KeyValue :=
  .address I.source

abbrev relyStore (I : ExecutionEnv) : Store :=
  (∅ : Store).insert "usr" (relyUsrValue I)

def relyUsrStorageSlot (I : ExecutionEnv) : UInt256 :=
  wardsSlot (relyUsrKey I)

def relyAuthStorageSlot (I : ExecutionEnv) : UInt256 :=
  wardsSlot (relyAuthKey I)

def relyAuthWord (σ : AccountMap) (I : ExecutionEnv) : UInt256 :=
  solcSlotWordAt (relyAuthStorageSlot I) σ I

def relyPostState (evm : EVM.State) (I : ExecutionEnv) : EVM.State :=
  Solm.EVM.storageStore evm evm.executionEnv.codeOwner (relyUsrStorageSlot I) ⟨1⟩

abbrev relyUsrEvaledRef (I : ExecutionEnv) : EvaledStorageRef :=
  { base := "wards", steps := [.mindex (relyUsrKey I)] }

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

theorem relyUsrStorageSlot_eq_mapSlot_masked (I : ExecutionEnv) :
    relyUsrStorageSlot I = mapSlot (relyUsrMaskedWord I) ⟨0⟩ := by
  unfold relyUsrStorageSlot wardsSlot relyUsrKey relyUsrMaskedWord
  rw [keyValueToWord_address_ofNat_mask]

theorem relyAuthStorageSlot_eq_mapSlot_source (I : ExecutionEnv) :
    relyAuthStorageSlot I = mapSlot (relySourceWord I) ⟨0⟩ := by
  unfold relyAuthStorageSlot wardsSlot relyAuthKey relySourceWord
  rw [keyValueToWord_address]

theorem daiJoinDecode_rely_ok {I : ExecutionEnv} (hsz36 : 36 ≤ I.calldata.size) :
    decodeCalldataWithMode config.abiDecodeMode (relyTransition.params.map Param.name)
      (transitionSignature relyTransition).paramTypes I.calldata = some (relyStore I) := by
  simpa [config, relyTransition, relyStore, relyUsrValue, relyUsrWord, calldataWord] using
    decodeCalldata_legacyAddress_ok (cd := I.calldata) (x := "usr") hsz36

theorem daiJoinDecode_rely_none_short {I : ExecutionEnv}
    (hsz4 : 4 ≤ I.calldata.size) (hshort : I.calldata.size < 36) :
    decodeCalldataWithMode config.abiDecodeMode (relyTransition.params.map Param.name)
      (transitionSignature relyTransition).paramTypes I.calldata = none := by
  simpa [config, relyTransition] using
    decodeCalldata_legacyAddress_none_short (cd := I.calldata) (x := "usr") hsz4 hshort

theorem evalStorageRef_rely_usr (evm : EVM.State) (I : ExecutionEnv) :
    evalStorageRef config { contract := contract, locals := relyStore I } evm
      (wardsRef (.var "usr")) = .ok (relyUsrEvaledRef I) := by
  simp [evalStorageRef, evalStorageRefStep, wardsRef, relyStore, relyUsrValue,
    valueToKey?, EvalResult.bind, EvalResult.ofOption, bind, pure, evalExpr?]

theorem evalStorageRef_rely_auth (evm : EVM.State) (I : ExecutionEnv)
    (hsrc : evm.executionEnv.source = I.source) :
    evalStorageRef config { contract := contract, locals := relyStore I } evm
      (wardsRef sender) = .ok (relyAuthEvaledRef I) := by
  simp [evalStorageRef, evalStorageRefStep, wardsRef, sender, envValue, relyAuthEvaledRef,
    relyAuthKey, hsrc, valueToKey?, EvalResult.bind, EvalResult.ofOption, bind, pure,
    evalExpr?]


theorem evalExpr_rely_auth_true (evm : EVM.State) (I : ExecutionEnv)
    (hsrc : evm.executionEnv.source = I.source)
    (hload :
      Solm.EVM.storageLoad evm evm.executionEnv.codeOwner (relyAuthStorageSlot I) = ⟨1⟩) :
    evalExpr? config { contract := contract, locals := relyStore I } evm
      (.binary .eq (.storage (wardsRef sender)) (.intLit 1)) = .ok (.bool true) := by
  have hstorage :
      evalExpr? config { contract := contract, locals := relyStore I } evm
        (.storage (wardsRef sender)) = .ok (.int 1) := by
    rw [evalExpr_storage_scalar_value (hbackend := rfl)
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
        simpa [hload] using storageLocLoad_uint256 evm (relyAuthStorageSlot I))]
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
    exact evalExpr_storage_scalar_value (hbackend := rfl)
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
      (hload := by exact storageLocLoad_uint256 evm (relyAuthStorageSlot I))
  have hne :
      Value.int (Int.ofNat
          (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner
            (relyAuthStorageSlot I)).toNat) ≠ Value.int 1 := by
    intro hbad
    rw [Value.int.injEq] at hbad
    apply hload
    exact uInt256_toNat_eq_one (Int.ofNat.inj hbad)
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
      .storage (wardsRef (.var "usr")) (.int 1) =
        .ok ({ contract := contract, locals := relyStore I }, relyPostState evm I) := by
  apply assignStorageRef_storage_scalar (hbackend := rfl)
      (ty := uint256St)
      (loc := wordLoc (relyUsrStorageSlot I)) (hleaf := by first | exact Or.inl ⟨_, rfl⟩ | exact Or.inr ⟨_, rfl⟩)
      (hbase := relyStore_wards I)
      (her := evalStorageRef_rely_usr evm I)
      (hty := by simp [storageTypeAt?, storageTypeStep?, contract, storageDecls, uint256St])
      (hloc := by rfl)
  simpa [relyPostState] using
    storageLocStore_uint256 evm (relyUsrStorageSlot I) ⟨1⟩

theorem daiJoinRelyBodyReturns (evm : EVM.State) (I : ExecutionEnv)
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
      (ref := wardsRef (.var "usr"))
      (value := .int 1)
      hwv
      (evalExpr_rely_auth_true evm I hsrc hauth)
      (by simp [evalExpr?, pure])
      (relyAssign evm I)

theorem daiJoinRelyBodyStatic (evm : EVM.State) (I : ExecutionEnv)
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hsrc : evm.executionEnv.source = I.source)
    (hauth :
      Solm.EVM.storageLoad evm evm.executionEnv.codeOwner (relyAuthStorageSlot I) = ⟨1⟩)
    (hperm : evm.executionEnv.perm = false) :
    ExecTransitionBody config contract evm (relyStore I) relyTransition.body
      .staticViolation := by
  refine ExecFuncBody.execBlockStatic ?_
  simpa [relyTransition, nonpayable, auth] using
    nonpayableRequireAssignStorageBlockStatic
      (cfg := config)
      (solm := { contract := contract, locals := relyStore I })
      (evm := evm)
      (guard := .binary .eq (.storage (wardsRef sender)) (.intLit 1))
      (rhs := .intLit 1)
      (ref := wardsRef (.var "usr"))
      (value := .int 1)
      (rest := [])
      hwv
      (evalExpr_rely_auth_true evm I hsrc hauth)
      (by simp [evalExpr?, pure])
      (relyAssign evm I)
      hperm

theorem daiJoinRelyBodyReverts (evm : EVM.State) (I : ExecutionEnv)
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
      (rest := [.assign .storage (wardsRef (.var "usr")) (.intLit 1)])
      hwv
      (evalExpr_rely_auth_false evm I hsrc hauth)

abbrev relyAuthHashMem (I : ExecutionEnv) : ByteArray :=
  twoWordHashMem (relySourceWord I) ⟨0⟩ solcFreePtrMem

abbrev relyStoreHashMem (I : ExecutionEnv) : ByteArray :=
  twoWordHashMem (relyUsrMaskedWord I) ⟨0⟩ (relyAuthHashMem I)

theorem relyUsrMaskedWord_canonical (I : ExecutionEnv) :
    (relyUsrMaskedWord I).toNat < EVM.addressModulus := by
  unfold relyUsrMaskedWord
  rw [u256_land_comm solcAddrMask (relyUsrWord I)]
  exact solcAddrMask_result_canonical (relyUsrWord I)

theorem relyAuthHashMem_size (I : ExecutionEnv) :
    (relyAuthHashMem I).size = 96 := by
  exact twoWordHashMem_size_96 (relySourceWord I) ⟨0⟩ solcFreePtrMem_size

theorem relyAuthHashMem_read64 (I : ExecutionEnv) :
    (relyAuthHashMem I).readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩ := by
  exact twoWordHashMem_read64 (relySourceWord I) ⟨0⟩ solcFreePtrMem_size
    solcFreePtrMem_read64

theorem relyStoreHashMem_size (I : ExecutionEnv) :
    (relyStoreHashMem I).size = 96 := by
  exact twoWordHashMem_size_96 (relyUsrMaskedWord I) ⟨0⟩ (relyAuthHashMem_size I)

theorem relyStoreHashMem_read64 (I : ExecutionEnv) :
    (relyStoreHashMem I).readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩ := by
  exact twoWordHashMem_read64 (relyUsrMaskedWord I) ⟨0⟩ (relyAuthHashMem_size I)
    (relyAuthHashMem_read64 I)

theorem relyNotAuthorizedWord :
    UInt256.shiftLeft
        (⟨0x11185a529bda5b8bdb9bdd0b585d5d1a1bdc9a5e9959⟩ : UInt256) ⟨82⟩ =
      ⟨0x4461694a6f696e2f6e6f742d617574686f72697a656400000000000000000000⟩ := by
  native_decide

theorem daiJoinReachRelyBody {σ σ₀ A I} {g : Sat256}
    (hcode : I.code = daiJoinBytecode) (hwv : I.weiValue = ⟨0⟩)
    (hsz : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hsel : selIs I (daiJoinSelBytes 6)) :
    ∃ k C, RD daiJoinBytecode I g
        (initState σ σ₀ g A I)
        ⟨234⟩ [daiJoinSelWord I] solcFreePtrMem (UInt256.ofNat 3)
        ByteArray.empty σ k C := by
  have hword : daiJoinSelWord I = ⟨0x65fae35e⟩ :=
    daiJoinSelWord_eq_of_beq I hsz 0x65 0xfa 0xe3 0x5e ⟨0x65fae35e⟩
      (by native_decide) (by simpa [daiJoinSelBytes] using hsel)
  have hroot : UInt256.gt (armSelNat daiJoinBytecode daiJoinRootSplitPc) (daiJoinSelWord I) ≠ ⟨0⟩ := by
    rw [hword]
    native_decide
  have heq0 : ∀ j, j < 2 →
      UInt256.eq
        (armSelNat daiJoinBytecode
          (nthArmPc daiJoinBytecode daiJoinLowFirstArmPc j))
        (daiJoinSelWord I) = ⟨0⟩ := by
    intro j hj
    interval_cases j <;> rw [hword] <;> native_decide
  have htake :
      UInt256.eq
        (armSelNat daiJoinBytecode
          (nthArmPc daiJoinBytecode daiJoinLowFirstArmPc 2))
        (daiJoinSelWord I) ≠ ⟨0⟩ := by
    rw [hword]
    native_decide
  exact daiJoinReachLowBody 2 (by omega) ⟨234⟩ hcode hwv hsz hsize hroot heq0 htake
    (by jump_dest) (by native_decide)

theorem daiJoinRelyX_decoded {σ σ₀ A I} {g : Sat256} {sel : UInt256}
    (hsz36 : 36 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hreach : ∃ k C, RD daiJoinBytecode I g
      (initState σ σ₀ g A I) ⟨234⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty σ k C) :
    ∃ k C, RD daiJoinBytecode I g
        (initState σ σ₀ g A I) ⟨774⟩
        [relyUsrMaskedWord I, ⟨232⟩, sel]
        solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty σ k C := by
  obtain ⟨_, _, hdecoded⟩ := RD.solcOneAddressExternalLenOk
    (code := daiJoinBytecode) (sel := sel)
    (entry := ⟨234⟩) (ret := ⟨232⟩) (decoded := ⟨256⟩) hreach
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by jump_dest) hsz36 hsize
  obtain ⟨_, _, hroutine⟩ := RD.solcOneAddressExternalMaskAndJumpMasked
    (code := daiJoinBytecode) (decoded := ⟨256⟩) (ret := ⟨232⟩)
    (routine := ⟨774⟩) (R := [sel]) hdecoded
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by jump_dest) (by simp)
  exact ⟨_, _, by simpa [relyUsrMaskedWord, relyUsrWord, calldataWord] using hroutine⟩

theorem daiJoinRelyX_shortarg {σ σ₀ A I} {g : Sat256} {sel : UInt256}
    (hsz4 : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hshort : I.calldata.size < 36)
    (hreach : ∃ k C, RD daiJoinBytecode I g
      (initState σ σ₀ g A I) ⟨234⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty σ k C) :
    RDrev daiJoinBytecode g (initState σ σ₀ g A I) := by
  have hlt :
      UInt256.lt (UInt256.sub (UInt256.ofNat I.calldata.size) ⟨4⟩) ⟨32⟩ = ⟨1⟩ := by
    apply ult_one
    rw [usub_ofNat_word_toNat (by simpa using hsz4) hsize]
    change I.calldata.size - 4 < 32
    omega
  exact RD.solcExternalStaticArgsShortReverts
    (code := daiJoinBytecode) (sel := sel)
    (entry := ⟨234⟩) (ret := ⟨232⟩) (decoded := ⟨256⟩)
    (need := ⟨32⟩) hreach
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) hlt

set_option maxHeartbeats 1000000 in
theorem daiJoinRelyX_authorized {σ I} {g : Sat256} {s0 : State} {k C : ℕ}
    {sel : UInt256} (hauth : relyAuthWord σ I = ⟨1⟩)
    (h : RD daiJoinBytecode I g s0 ⟨774⟩
      [relyUsrMaskedWord I, ⟨232⟩, sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty σ k C) :
    ∃ k' C', RD daiJoinBytecode I g s0 ⟨867⟩
      [relyUsrMaskedWord I, ⟨232⟩, sel]
      (relyAuthHashMem I) (UInt256.ofNat 3) ByteArray.empty σ k' C' := by
  have hauthSlot :
      UInt256.ofNat (fromByteArrayBigEndian
          (KEC ((relyAuthHashMem I).readWithPadding 0 64))) =
        mapSlot (relySourceWord I) ⟨0⟩ := by
    simpa [relyAuthHashMem, mapSlot, solcMappingSlot] using
      twoWordHashMem_solcMappingSlot (⟨0⟩ : UInt256) (relySourceWord I)
        solcFreePtrMem_size
  have rd775pre := evm_run h with [
    raw jumpdest (by native_decide) (by evm_ov),
    raw caller (by native_decide) (by evm_ov),
    raw push1 ⟨0⟩ (by native_decide) (by evm_ov),
    raw swap1 (by native_decide) (by evm_ov),
    raw dup2 (by native_decide) (by evm_ov)]
  have rd781 := rd775pre.mstore 0 (wordAt0Mem (relySourceWord I) solcFreePtrMem)
    (UInt256.ofNat 3) (by native_decide) mem_cost (by rfl) (by native_decide)
    (by evm_ov)
  have rd785pre := evm_run rd781 with [
    raw push1 ⟨32⟩ (by native_decide) (by evm_ov),
    raw dup2 (by native_decide) (by evm_ov),
    raw swap1 (by native_decide) (by evm_ov)]
  have rd786 := rd785pre.mstore 0 (relyAuthHashMem I)
    (UInt256.ofNat 3) (by native_decide) mem_cost (by rfl) (by native_decide)
    (by evm_ov)
  have rd789pre := evm_run rd786 with [
    raw push1 ⟨64⟩ (by native_decide) (by evm_ov),
    raw swap1 (by native_decide) (by evm_ov)]
  have rd790 := rd789pre.keccak256 0 (mapSlot (relySourceWord I) ⟨0⟩)
    (UInt256.ofNat 3) (by native_decide) mem_cost hauthSlot (by native_decide)
    (by evm_ov)
  obtain ⟨k791, C791, rd791raw⟩ := rd790.sload (by native_decide) (by evm_ov)
  have rd791 : RD daiJoinBytecode I g s0 ⟨791⟩
      (relyAuthWord σ I :: relyUsrMaskedWord I :: ⟨232⟩ :: [sel])
      (relyAuthHashMem I) (UInt256.ofNat 3) ByteArray.empty σ k791 C791 := by
    simpa [relyAuthWord, solcSlotWordAt, relyAuthStorageSlot_eq_mapSlot_source I]
      using rd791raw
  have rd794pre := evm_run rd791 with [
    raw push1 ⟨1⟩ (by native_decide) (by evm_ov),
    raw eq (by native_decide) (by evm_ov)]
  rw [hauth, u256_eq_refl] at rd794pre
  have rd797 := rd794pre.pushConst (⟨867⟩ : UInt256)
    (width := 2) (op := .PUSH2) (by decide) (by native_decide) (by evm_ov)
  exact ⟨_, _, rd797.jumpiT (by native_decide) one_ne_zero_uint
    (by jump_dest) (by evm_ov)⟩

set_option maxHeartbeats 1000000 in
theorem daiJoinRelyX_unauthorized {σ I} {g : Sat256} {s0 : State} {k C : ℕ}
    {sel : UInt256} (hauth : relyAuthWord σ I ≠ ⟨1⟩)
    (h : RD daiJoinBytecode I g s0 ⟨774⟩
      [relyUsrMaskedWord I, ⟨232⟩, sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty σ k C) :
    RDrev daiJoinBytecode g s0 := by
  have hauthSlot :
      UInt256.ofNat (fromByteArrayBigEndian
          (KEC ((relyAuthHashMem I).readWithPadding 0 64))) =
        mapSlot (relySourceWord I) ⟨0⟩ := by
    simpa [relyAuthHashMem, mapSlot, solcMappingSlot] using
      twoWordHashMem_solcMappingSlot (⟨0⟩ : UInt256) (relySourceWord I)
        solcFreePtrMem_size
  have rd775pre := evm_run h with [
    raw jumpdest (by native_decide) (by evm_ov),
    raw caller (by native_decide) (by evm_ov),
    raw push1 ⟨0⟩ (by native_decide) (by evm_ov),
    raw swap1 (by native_decide) (by evm_ov),
    raw dup2 (by native_decide) (by evm_ov)]
  have rd781 := rd775pre.mstore 0 (wordAt0Mem (relySourceWord I) solcFreePtrMem)
    (UInt256.ofNat 3) (by native_decide) mem_cost (by rfl) (by native_decide)
    (by evm_ov)
  have rd785pre := evm_run rd781 with [
    raw push1 ⟨32⟩ (by native_decide) (by evm_ov),
    raw dup2 (by native_decide) (by evm_ov),
    raw swap1 (by native_decide) (by evm_ov)]
  have rd786 := rd785pre.mstore 0 (relyAuthHashMem I)
    (UInt256.ofNat 3) (by native_decide) mem_cost (by rfl) (by native_decide)
    (by evm_ov)
  have rd789pre := evm_run rd786 with [
    raw push1 ⟨64⟩ (by native_decide) (by evm_ov),
    raw swap1 (by native_decide) (by evm_ov)]
  have rd790 := rd789pre.keccak256 0 (mapSlot (relySourceWord I) ⟨0⟩)
    (UInt256.ofNat 3) (by native_decide) mem_cost hauthSlot (by native_decide)
    (by evm_ov)
  obtain ⟨k791, C791, rd791raw⟩ := rd790.sload (by native_decide) (by evm_ov)
  have rd791 : RD daiJoinBytecode I g s0 ⟨791⟩
      (relyAuthWord σ I :: relyUsrMaskedWord I :: ⟨232⟩ :: [sel])
      (relyAuthHashMem I) (UInt256.ofNat 3) ByteArray.empty σ k791 C791 := by
    simpa [relyAuthWord, solcSlotWordAt, relyAuthStorageSlot_eq_mapSlot_source I]
      using rd791raw
  have rd794pre := evm_run rd791 with [
    raw push1 ⟨1⟩ (by native_decide) (by evm_ov),
    raw eq (by native_decide) (by evm_ov)]
  have heq : UInt256.eq (⟨1⟩ : UInt256) (relyAuthWord σ I) = ⟨0⟩ := by
    exact u256_eq_of_ne (by intro hbad; exact hauth hbad.symm)
  rw [heq] at rd794pre
  have rd797 := rd794pre.pushConst (⟨867⟩ : UInt256)
    (width := 2) (op := .PUSH2) (by decide) (by native_decide) (by evm_ov)
  have rd798 := rd797.jumpiNT (by native_decide) rfl (by evm_ov)
  exact RD.solcErrorStringRevertTail
    (pc := ⟨798⟩)
    (len := ⟨22⟩)
    (rawWord := ⟨0x11185a529bda5b8bdb9bdd0b585d5d1a1bdc9a5e9959⟩)
    (shift := ⟨82⟩)
    (word := ⟨0x4461694a6f696e2f6e6f742d617574686f72697a656400000000000000000000⟩)
    (op := .PUSH22)
    (width := 22)
    rd798
    (by
      unfold solcErrorStringRevertTailWf
      repeat' first | apply And.intro | native_decide)
    (by decide)
    relyNotAuthorizedWord
    (relyAuthHashMem_size I)
    (relyAuthHashMem_read64 I)
    (by simp only [List.length_cons, List.length_nil]; omega)

set_option maxHeartbeats 4000000 in
theorem daiJoinRelyX_storeAuthorizedSplit {σ I} {g : Sat256} {s0 : State} {k C : ℕ}
    {sel : UInt256}
    (h : RD daiJoinBytecode I g s0 ⟨867⟩
      [relyUsrMaskedWord I, ⟨232⟩, sel]
      (relyAuthHashMem I) (UInt256.ofNat 3) ByteArray.empty σ k C) :
    (I.perm = true ∧
      RDret daiJoinBytecode g s0
        (sstoreAccountMap I.codeOwner σ (relyUsrStorageSlot I) ⟨1⟩)
        ByteArray.empty) ∨
      (I.perm = false ∧ RDstatic daiJoinBytecode g s0) := by
  have hstoreSlot :
      UInt256.ofNat (fromByteArrayBigEndian
          (KEC ((relyStoreHashMem I).readWithPadding 0 64))) =
        mapSlot (relyUsrMaskedWord I) ⟨0⟩ := by
    simpa [relyStoreHashMem, mapSlot, solcMappingSlot] using
      twoWordHashMem_solcMappingSlot (⟨0⟩ : UInt256) (relyUsrMaskedWord I)
        (relyAuthHashMem_size I)
  have rd878pre := evm_run h with [
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
          (relyUsrMaskedWord I)
        = relyUsrMaskedWord I := by
    rw [u256_land_comm]
    rw [show UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨160⟩) ⟨1⟩ =
      solcAddrMask from by decide]
    exact solcAddrMask_clean (relyUsrMaskedWord_canonical I)
  have hmask' :
      UInt256.land (relyUsrMaskedWord I)
          (UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨160⟩) ⟨1⟩)
        = relyUsrMaskedWord I := by
    rw [u256_land_comm]
    exact hmask
  rw [hmask'] at rd878pre
  have rd882pre := evm_run rd878pre with [
    raw push1 ⟨0⟩ (by native_decide) (by evm_ov),
    raw dup2 (by native_decide) (by evm_ov),
    raw dup2 (by native_decide) (by evm_ov)]
  have rd883 := rd882pre.mstore 0
    (wordAt0Mem (relyUsrMaskedWord I) (relyAuthHashMem I))
    (UInt256.ofNat 3) (by native_decide) mem_cost (by rfl) (by native_decide)
    (by evm_ov)
  have rd887pre := evm_run rd883 with [
    raw push1 ⟨32⟩ (by native_decide) (by evm_ov),
    raw dup2 (by native_decide) (by evm_ov),
    raw swap1 (by native_decide) (by evm_ov)]
  have rd888 := rd887pre.mstore 0 (relyStoreHashMem I)
    (UInt256.ofNat 3) (by native_decide) mem_cost (by rfl) (by native_decide)
    (by evm_ov)
  have rd892pre := evm_run rd888 with [
    raw push1 ⟨64⟩ (by native_decide) (by evm_ov),
    raw dup1 (by native_decide) (by evm_ov),
    raw dup3 (by native_decide) (by evm_ov)]
  have rd893 := rd892pre.keccak256 0 (mapSlot (relyUsrMaskedWord I) ⟨0⟩)
    (UInt256.ofNat 3) (by native_decide) mem_cost hstoreSlot (by native_decide)
    (by evm_ov)
  have rd896pre := evm_run rd893 with [
    raw push1 ⟨1⟩ (by native_decide) (by evm_ov),
    raw swap1 (by native_decide) (by evm_ov)]
  have hstoreDec : decode daiJoinBytecode ⟨896⟩ = some (.SSTORE, none) := by
    native_decide
  by_cases hperm : I.perm = true
  swap
  · exact Or.inr ⟨by simpa using hperm,
      rd896pre.sstoreStatic (by simpa using hperm) hstoreDec (by evm_ov)⟩
  refine Or.inl ⟨hperm, ?_⟩
  obtain ⟨_, _, rd897raw⟩ := rd896pre.sstore hperm hstoreDec
    (by simp only [List.length_cons, List.length_nil]; omega)
  have rd897 := by
    simpa [relyUsrStorageSlot_eq_mapSlot_masked I] using rd897raw
  have rd898 := rd897.mload 0 ⟨128⟩ (UInt256.ofNat 3) (by native_decide) mem_cost
    (mloadFreePtrValue (by rw [relyStoreHashMem_size I]; decide)
      (relyStoreHashMem_read64 I))
    (by native_decide) (by evm_ov)
  have rd931 := rd898.pushConst
    (⟨0xdd0e34038ac38b2a1ce960229778ac48a8719bc900b6c4f8d0475c6e8b385a60⟩ : UInt256)
    (width := 32) (op := .PUSH32) (by decide) (by native_decide) (by evm_ov)
  have rd933pre := evm_run rd931 with [
    raw swap2 (by native_decide) (by evm_ov),
    raw swap1 (by native_decide) (by evm_ov)]
  have rd934 := RD.log2
    (a := ⟨128⟩) (b := ⟨0⟩)
    (c := ⟨0xdd0e34038ac38b2a1ce960229778ac48a8719bc900b6c4f8d0475c6e8b385a60⟩)
    (d := relyUsrMaskedWord I) (t := [relyUsrMaskedWord I, ⟨232⟩, sel])
    0
    (UInt256.ofNat
      (MachineState.M (UInt256.ofNat 3).toNat (⟨128⟩ : UInt256).toNat
        (⟨0⟩ : UInt256).toNat))
    rd933pre (by native_decide) hperm mem_cost (by native_decide)
    (by simp only [List.length_cons, List.length_nil]; omega)
  have rd935pre := RD.pop (a := relyUsrMaskedWord I) (t := [⟨232⟩, sel]) rd934
    (by native_decide) (by evm_ov)
  have rd232 := RD.jump (a := ⟨232⟩) (t := [sel]) rd935pre
    (by native_decide) (by jump_dest) (by evm_ov)
  have rd232' := RD.jumpdest (pc := ⟨232⟩) (stk := [sel]) rd232
    (by native_decide) (by evm_ov)
  have hstop := RD.stop rd232' (by native_decide) (by evm_ov)
  simpa [relyUsrStorageSlot_eq_mapSlot_masked I] using hstop

theorem daiJoinX_rely_okSplit {σ σ₀ A I} {g : Sat256} {sel : UInt256}
    (hsz36 : 36 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hauth : relyAuthWord σ I = ⟨1⟩)
    (hreach : ∃ k C, RD daiJoinBytecode I g
      (initState σ σ₀ g A I) ⟨234⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty σ k C) :
    (I.perm = true ∧
      RDret daiJoinBytecode g (initState σ σ₀ g A I)
        (sstoreAccountMap I.codeOwner σ (relyUsrStorageSlot I) ⟨1⟩)
        ByteArray.empty) ∨
      (I.perm = false ∧ RDstatic daiJoinBytecode g (initState σ σ₀ g A I)) := by
  obtain ⟨_, _, rd719⟩ := daiJoinRelyX_decoded (g := g) hsz36 hsize hreach
  obtain ⟨_, _, rd797⟩ := daiJoinRelyX_authorized (I := I) hauth rd719
  exact daiJoinRelyX_storeAuthorizedSplit rd797

theorem daiJoinX_rely_ok {σ σ₀ A I} {g : Sat256} {sel : UInt256}
    (hsz36 : 36 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hperm : I.perm = true) (hauth : relyAuthWord σ I = ⟨1⟩)
    (hreach : ∃ k C, RD daiJoinBytecode I g
      (initState σ σ₀ g A I) ⟨234⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty σ k C) :
    RDret daiJoinBytecode g (initState σ σ₀ g A I)
      (sstoreAccountMap I.codeOwner σ (relyUsrStorageSlot I) ⟨1⟩)
      ByteArray.empty :=
  permSplit_true hperm (daiJoinX_rely_okSplit hsz36 hsize hauth hreach)

theorem daiJoinX_rely_unauthorized {σ σ₀ A I} {g : Sat256} {sel : UInt256}
    (hsz36 : 36 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hauth : relyAuthWord σ I ≠ ⟨1⟩)
    (hreach : ∃ k C, RD daiJoinBytecode I g
      (initState σ σ₀ g A I) ⟨234⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty σ k C) :
    RDrev daiJoinBytecode g (initState σ σ₀ g A I) := by
  obtain ⟨_, _, rd719⟩ := daiJoinRelyX_decoded (g := g) hsz36 hsize hreach
  exact daiJoinRelyX_unauthorized (I := I) hauth rd719

theorem daiJoinRelyBodyCoreOk
    {σ σ₀ A I} {g : UInt256} {sel : UInt256}
    (hcode : I.code = daiJoinBytecode)
    (hsize : I.calldata.size < UInt256.size)
    (hperm : I.perm = true) (hwv : I.weiValue = ⟨0⟩)
    (hsz36 : 36 ≤ I.calldata.size)
    (hauth : relyAuthWord σ I = ⟨1⟩)
    (hdispatch : dispatchMsg contract I.calldata = some relyTransition)
    (hdecode :
      decodeCalldataWithMode config.abiDecodeMode (relyTransition.params.map Param.name)
        (transitionSignature relyTransition).paramTypes I.calldata = some (relyStore I))
    (hreach : ∃ k C, RD daiJoinBytecode I (Sat256.ofUInt256 g)
      (initState σ σ₀ (Sat256.ofUInt256 g) A I) ⟨234⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty σ k C) :
    runtimeRefinementFor config contract σ σ₀ g A I := by
  let evmSolm := initState σ σ₀ (Sat256.ofUInt256 g) A I
  have hbody :
      ExecTransitionBody config contract evmSolm (relyStore I)
        relyTransition.body
        (.returned { contract := contract, locals := relyStore I }
          (relyPostState evmSolm I) none) := by
    simpa [evmSolm, relyAuthWord, solcSlotWordAt, initState, Solm.EVM.storageLoad,
      State.lookupAccount] using
      daiJoinRelyBodyReturns evmSolm I
        (by simp only [evmSolm, initState]; exact hwv)
        (by simp [evmSolm, initState])
        hauth
  exact (daiJoinX_rely_ok (g := Sat256.ofUInt256 g) hsz36 hsize hperm hauth hreach)
    |>.reEquivExecutionGen hcode hdispatch hdecode hbody
      (by simp [relyPostState, evmSolm, initState, storageStore_accountMap])
      (by
        simpa [relyTransition] using
          (returnEquiv.fallthrough (o := ByteArray.empty) (r := none) (t := [])
            (dvs := []) rfl (by native_decide) (by native_decide)))

theorem daiJoinRelyBodyCoreStatic
    {σ σ₀ A I} {g : UInt256} {sel : UInt256}
    (hcode : I.code = daiJoinBytecode)
    (hsize : I.calldata.size < UInt256.size)
    (hperm : I.perm = false) (hwv : I.weiValue = ⟨0⟩)
    (hsz36 : 36 ≤ I.calldata.size)
    (hauth : relyAuthWord σ I = ⟨1⟩)
    (hdispatch : dispatchMsg contract I.calldata = some relyTransition)
    (hdecode :
      decodeCalldataWithMode config.abiDecodeMode (relyTransition.params.map Param.name)
        (transitionSignature relyTransition).paramTypes I.calldata = some (relyStore I))
    (hreach : ∃ k C, RD daiJoinBytecode I (Sat256.ofUInt256 g)
      (initState σ σ₀ (Sat256.ofUInt256 g) A I) ⟨234⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty σ k C) :
    runtimeRefinementFor config contract σ σ₀ g A I := by
  let evmSolm := initState σ σ₀ (Sat256.ofUInt256 g) A I
  have hbody :
      ExecTransitionBody config contract evmSolm (relyStore I)
        relyTransition.body
        .staticViolation := by
    simpa [evmSolm, relyAuthWord, solcSlotWordAt, initState, Solm.EVM.storageLoad,
      State.lookupAccount] using
      daiJoinRelyBodyStatic evmSolm I
        (by simp only [evmSolm, initState]; exact hwv)
        (by simp [evmSolm, initState])
        hauth
        (by simp only [evmSolm, initState]; exact hperm)
  exact (permSplit_false hperm (daiJoinX_rely_okSplit
      (g := Sat256.ofUInt256 g) hsz36 hsize hauth hreach))
    |>.reEquivStaticHalt hcode hdispatch hdecode hbody

theorem daiJoinRelyBodyCoreUnauthorized
    {σ σ₀ A I} {g : UInt256} {sel : UInt256}
    (hcode : I.code = daiJoinBytecode)
    (hsize : I.calldata.size < UInt256.size)
    (hwv : I.weiValue = ⟨0⟩)
    (hsz36 : 36 ≤ I.calldata.size)
    (hauth : relyAuthWord σ I ≠ ⟨1⟩)
    (hdispatch : dispatchMsg contract I.calldata = some relyTransition)
    (hdecode :
      decodeCalldataWithMode config.abiDecodeMode (relyTransition.params.map Param.name)
        (transitionSignature relyTransition).paramTypes I.calldata = some (relyStore I))
    (hreach : ∃ k C, RD daiJoinBytecode I (Sat256.ofUInt256 g)
      (initState σ σ₀ (Sat256.ofUInt256 g) A I) ⟨234⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty σ k C) :
    runtimeRefinementFor config contract σ σ₀ g A I := by
  let evmSolm := initState σ σ₀ (Sat256.ofUInt256 g) A I
  have hbody :
      ExecTransitionBody config contract evmSolm (relyStore I)
        relyTransition.body .reverted := by
    simpa [evmSolm, relyAuthWord, solcSlotWordAt, initState, Solm.EVM.storageLoad,
      State.lookupAccount] using
      daiJoinRelyBodyReverts evmSolm I
        (by simp only [evmSolm, initState]; exact hwv)
        (by simp [evmSolm, initState])
        hauth
  exact (daiJoinX_rely_unauthorized (g := Sat256.ofUInt256 g) hsz36 hsize hauth hreach)
    |>.reEquivExecutionRevert hcode hdispatch hdecode hbody

theorem daiJoinRelyBodyCoreDecodeFailed_short
    {σ σ₀ A I} {g : UInt256} {sel : UInt256}
    (hcode : I.code = daiJoinBytecode)
    (hsize : I.calldata.size < UInt256.size)
    (hsz4 : 4 ≤ I.calldata.size) (hshort : I.calldata.size < 36)
    (hdispatch : dispatchMsg contract I.calldata = some relyTransition)
    (hreach : ∃ k C, RD daiJoinBytecode I (Sat256.ofUInt256 g)
      (initState σ σ₀ (Sat256.ofUInt256 g) A I) ⟨234⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty σ k C) :
    runtimeRefinementFor config contract σ σ₀ g A I := by
  exact (daiJoinRelyX_shortarg (g := Sat256.ofUInt256 g) hsz4 hsize hshort hreach)
    |>.reEquivDecodingFailed hcode hdispatch (daiJoinDecode_rely_none_short hsz4 hshort)

theorem daiJoinRelyBodyCore {σ σ₀ A I} {g : UInt256}
    (hcode : I.code = daiJoinBytecode)
    (hsize : I.calldata.size < UInt256.size)
    (hperm : I.perm = true)
    (hwv : I.weiValue = ⟨0⟩)
    (hsel : selIs I (daiJoinSelBytes 6)) :
    runtimeRefinementFor config contract σ σ₀ g A I := by
  have hsz4 : 4 ≤ I.calldata.size :=
    calldata_size_ge_of_selIs I (daiJoinSelBytes 6) rfl hsel
  have hdispatch : dispatchMsg contract I.calldata = some relyTransition :=
    daiJoinDispatchRely hsel
  have hreach := daiJoinReachRelyBody
    (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := Sat256.ofUInt256 g)
    hcode hwv hsz4 hsize hsel
  by_cases hsz36 : 36 ≤ I.calldata.size
  · by_cases hauth : relyAuthWord σ I = ⟨1⟩
    · exact daiJoinRelyBodyCoreOk hcode hsize hperm hwv hsz36 hauth hdispatch
        (daiJoinDecode_rely_ok hsz36) hreach
    · exact daiJoinRelyBodyCoreUnauthorized hcode hsize hwv hsz36 hauth hdispatch
        (daiJoinDecode_rely_ok hsz36) hreach
  · exact daiJoinRelyBodyCoreDecodeFailed_short hcode hsize hsz4 (by omega)
      hdispatch hreach

theorem daiJoinRelyBodyCoreAnyPerm {σ σ₀ A I} {g : UInt256}
    (hcode : I.code = daiJoinBytecode)
    (hsize : I.calldata.size < UInt256.size)
    (hwv : I.weiValue = ⟨0⟩)
    (hsel : selIs I (daiJoinSelBytes 6)) :
    runtimeRefinementFor config contract σ σ₀ g A I := by
  by_cases hperm : I.perm = true
  · exact daiJoinRelyBodyCore hcode hsize hperm hwv hsel
  have hstatic : I.perm = false := by simpa using hperm
  have hsz4 : 4 ≤ I.calldata.size :=
    calldata_size_ge_of_selIs I (daiJoinSelBytes 6) rfl hsel
  have hdispatch : dispatchMsg contract I.calldata = some relyTransition :=
    daiJoinDispatchRely hsel
  have hreach := daiJoinReachRelyBody
    (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := Sat256.ofUInt256 g)
    hcode hwv hsz4 hsize hsel
  by_cases hsz36 : 36 ≤ I.calldata.size
  · by_cases hauth : relyAuthWord σ I = ⟨1⟩
    · exact daiJoinRelyBodyCoreStatic hcode hsize hstatic hwv hsz36 hauth hdispatch
        (daiJoinDecode_rely_ok hsz36) hreach
    · exact daiJoinRelyBodyCoreUnauthorized hcode hsize hwv hsz36 hauth hdispatch
        (daiJoinDecode_rely_ok hsz36) hreach
  · exact daiJoinRelyBodyCoreDecodeFailed_short hcode hsize hsz4 (by omega)
      hdispatch hreach

end Benchmarks.Dss.DaiJoin
