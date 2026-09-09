import Benchmarks.Dss.Jug.Dispatch

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

set_option maxRecDepth 2000000

namespace Benchmarks.Dss.Jug

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
  jugSlotWord (relyAuthStorageSlot I) σ I

def relyPostState (evm : EVM.State) (I : ExecutionEnv) : EVM.State :=
  Solm.EVM.storageStore evm evm.executionEnv.codeOwner (relyUsrStorageSlot I) ⟨1⟩

abbrev relyUsrEvaledRef (I : ExecutionEnv) : EvaledStorageRef :=
  { base := "wards", steps := [.mindex (relyUsrKey I)] }

abbrev relyAuthEvaledRef (I : ExecutionEnv) : EvaledStorageRef :=
  { base := "wards", steps := [.mindex (relyAuthKey I)] }

theorem relyStore_wards (I : ExecutionEnv) :
    (relyStore I).get? "wards" = none := by
  unfold relyStore
  rw [store_get_ne _ _ (by decide +native)]
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

theorem jugDecode_rely_ok {I : ExecutionEnv} (hsz36 : 36 ≤ I.calldata.size) :
    decodeCalldataWithMode config.abiDecodeMode (relyTransition.params.map Param.name)
      (transitionSignature relyTransition).paramTypes I.calldata = some (relyStore I) := by
  simpa [config, relyTransition, relyStore, relyUsrValue, relyUsrWord, calldataWord] using
    decodeCalldata_legacyAddress_ok (cd := I.calldata) (x := "usr") hsz36

theorem jugDecode_rely_none_short {I : ExecutionEnv}
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
        simpa [hload] using jugStorageLocLoad_uint256 evm (relyAuthStorageSlot I))]
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
        exact jugStorageLocLoad_uint256 evm (relyAuthStorageSlot I))
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

theorem evalStorageRef_auth_of_wards_none (evm : EVM.State) (I : ExecutionEnv)
    (locals : Store)
    (hsrc : evm.executionEnv.source = I.source) :
    evalStorageRef config { contract := contract, locals := locals } evm
      (wardsRef sender) = .ok (relyAuthEvaledRef I) := by
  simp [evalStorageRef, evalStorageRefStep, wardsRef, sender, envValue, relyAuthEvaledRef,
    relyAuthKey, hsrc, valueToKey?, EvalResult.bind, EvalResult.ofOption, bind, pure,
    evalExpr?]

theorem evalExpr_auth_true_of_wards_none (evm : EVM.State) (I : ExecutionEnv)
    (locals : Store)
    (hwards : locals.get? "wards" = none)
    (hsrc : evm.executionEnv.source = I.source)
    (hload :
      Solm.EVM.storageLoad evm evm.executionEnv.codeOwner (relyAuthStorageSlot I) = ⟨1⟩) :
    evalExpr? config { contract := contract, locals := locals } evm
      (.binary .eq (.storage (wardsRef sender)) (.intLit 1)) = .ok (.bool true) := by
  have hstorage :
      evalExpr? config { contract := contract, locals := locals } evm
        (.storage (wardsRef sender)) = .ok (.int 1) := by
    rw [evalExpr_storage_scalar_value
      (cfg := config)
      (solm := { contract := contract, locals := locals })
      (slot := wardsRef sender)
      (er := relyAuthEvaledRef I)
      (t := .int uint256Int)
      (loc := wordLoc (relyAuthStorageSlot I))
      (value := .int 1)
      (hbase := hwards)
      (her := evalStorageRef_auth_of_wards_none evm I locals hsrc)
      (hty := by simp [storageTypeAt?, storageTypeStep?, contract, storageDecls, uint256St])
      (hloc := by rfl)
      (hload := by
        simpa [hload] using jugStorageLocLoad_uint256 evm (relyAuthStorageSlot I))]
  simp only [evalExpr?, hstorage, EvalResult.bind, bind, pure]
  rfl

theorem evalExpr_auth_false_of_wards_none (evm : EVM.State) (I : ExecutionEnv)
    (locals : Store)
    (hwards : locals.get? "wards" = none)
    (hsrc : evm.executionEnv.source = I.source)
    (hload :
      Solm.EVM.storageLoad evm evm.executionEnv.codeOwner (relyAuthStorageSlot I) ≠ ⟨1⟩) :
    evalExpr? config { contract := contract, locals := locals } evm
      (.binary .eq (.storage (wardsRef sender)) (.intLit 1)) = .ok (.bool false) := by
  have hstorage :
      evalExpr? config { contract := contract, locals := locals } evm
        (.storage (wardsRef sender)) =
          .ok (.int (Int.ofNat
            (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner
              (relyAuthStorageSlot I)).toNat)) := by
    exact evalExpr_storage_scalar_value
      (cfg := config)
      (solm := { contract := contract, locals := locals })
      (slot := wardsRef sender)
      (er := relyAuthEvaledRef I)
      (t := .int uint256Int)
      (loc := wordLoc (relyAuthStorageSlot I))
      (hbase := hwards)
      (her := evalStorageRef_auth_of_wards_none evm I locals hsrc)
      (hty := by simp [storageTypeAt?, storageTypeStep?, contract, storageDecls, uint256St])
      (hloc := by rfl)
      (hload := by
        exact jugStorageLocLoad_uint256 evm (relyAuthStorageSlot I))
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
      .storage (wardsRef (.var "usr")) (.int 1) =
        .ok ({ contract := contract, locals := relyStore I }, relyPostState evm I) := by
  apply assignStorageRef_storage_scalar
      (ty := uint256St)
      (loc := wordLoc (relyUsrStorageSlot I))
      (hbase := relyStore_wards I)
      (her := evalStorageRef_rely_usr evm I)
      (hty := by simp [storageTypeAt?, storageTypeStep?, contract, storageDecls, uint256St])
      (hloc := by rfl)
  simpa [relyPostState] using
    jugStorageLocStore_uint256 evm (relyUsrStorageSlot I) ⟨1⟩

theorem jugRelyBodyReturns (evm : EVM.State) (I : ExecutionEnv)
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

theorem jugRelyBodyReverts (evm : EVM.State) (I : ExecutionEnv)
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

noncomputable abbrev relyAuthHashMem (I : ExecutionEnv) : ByteArray :=
  twoWordHashMem (relySourceWord I) ⟨0⟩ solcFreePtrMem

noncomputable abbrev relyStoreHashMem (I : ExecutionEnv) : ByteArray :=
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

theorem relyNotAuthorizedWord :
    UInt256.shiftLeft (⟨0x129d59cbdb9bdd0b585d5d1a1bdc9a5e9959⟩ : UInt256) ⟨114⟩ =
      ⟨0x4a75672f6e6f742d617574686f72697a65640000000000000000000000000000⟩ := by
  decide +native

theorem jugReachRelyBody {cA gh bl σ σ₀ A I} {g : Sat256}
    (hcode : I.code = jugBytecode) (hwv : I.weiValue = ⟨0⟩)
    (hsz : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hsel : selIs I (jugSelBytes 8)) :
    ∃ k C, RD jugBytecode I g (initState cA gh bl σ σ₀ g A I)
        ⟨391⟩ [jugSelWord I] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty
        (cA, σ) k C := by
  have hword : jugSelWord I = ⟨0x65fae35e⟩ :=
    jugSelWord_eq_of_beq I hsz 0x65 0xfa 0xe3 0x5e ⟨0x65fae35e⟩
      (by decide +native) (by simpa [jugSelBytes] using hsel)
  have hroot : UInt256.gt (armSelNat jugBytecode jugRootSplitPc) (jugSelWord I) = ⟨0⟩ := by
    rw [hword]
    decide +native
  have heq0 : ∀ j, j < 1 →
      UInt256.eq (armSelNat jugBytecode (nthArmPc jugBytecode jugHighFirstArmPc j))
        (jugSelWord I) = ⟨0⟩ := by
    intro j hj
    interval_cases j
    rw [hword]
    decide +native
  have htake :
      UInt256.eq (armSelNat jugBytecode (nthArmPc jugBytecode jugHighFirstArmPc 1))
        (jugSelWord I) ≠ ⟨0⟩ := by
    rw [hword]
    decide +native
  exact jugReachHighBody 1 (by omega) ⟨391⟩ hcode hwv hsz hsize hroot heq0 htake
    (by jump_dest) (by decide +native)

theorem jugRelyX_decoded {cA gh bl σ σ₀ A I} {g : Sat256} {sel : UInt256}
    (hsz36 : 36 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hreach : ∃ k C, RD jugBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨391⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    ∃ k C, RD jugBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨1720⟩
        [relyUsrMaskedWord I, ⟨226⟩, sel]
        solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
  obtain ⟨_, _, hdecoded⟩ := RD.solcOneAddressExternalLenOk
    (code := jugBytecode) (sel := sel) (entry := ⟨391⟩) (ret := ⟨226⟩)
    (decoded := ⟨413⟩) hreach
    (by decide +native) (by decide +native) (by decide +native) (by decide +native)
    (by decide +native) (by decide +native) (by decide +native) (by decide +native)
    (by decide +native) (by decide +native) (by decide +native) (by decide +native)
    (by jump_dest) hsz36 hsize
  obtain ⟨_, _, hroutine⟩ := RD.solcOneAddressExternalMaskAndJumpMasked
    (code := jugBytecode) (decoded := ⟨413⟩) (ret := ⟨226⟩) (routine := ⟨1720⟩)
    (R := [sel]) hdecoded
    (by decide +native) (by decide +native) (by decide +native) (by decide +native)
    (by decide +native) (by decide +native) (by decide +native) (by decide +native)
    (by decide +native) (by decide +native) (by decide +native) (by jump_dest) (by simp)
  exact ⟨_, _, by simpa [relyUsrMaskedWord, relyUsrWord, calldataWord] using hroutine⟩

theorem jugRelyX_shortarg {cA gh bl σ σ₀ A I} {g : Sat256} {sel : UInt256}
    (hsz4 : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hshort : I.calldata.size < 36)
    (hreach : ∃ k C, RD jugBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨391⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    RDrev jugBytecode g (initState cA gh bl σ σ₀ g A I) := by
  have hlt :
      UInt256.lt (UInt256.sub (UInt256.ofNat I.calldata.size) ⟨4⟩) ⟨32⟩ = ⟨1⟩ := by
    apply ult_one
    rw [usub_ofNat_word_toNat (by simpa using hsz4) hsize]
    change I.calldata.size - 4 < 32
    omega
  exact RD.solcExternalStaticArgsShortReverts
    (code := jugBytecode) (sel := sel) (entry := ⟨391⟩) (ret := ⟨226⟩)
    (decoded := ⟨413⟩) (need := ⟨32⟩) hreach
    (by decide +native) (by decide +native) (by decide +native) (by decide +native)
    (by decide +native) (by decide +native) (by decide +native) (by decide +native)
    (by decide +native) (by decide +native) (by decide +native) (by decide +native)
    (by decide +native) (by decide +native) (by decide +native) hlt

set_option maxHeartbeats 1000000 in
theorem jugRelyX_authorized {cA σ I} {g : Sat256} {s0 : State} {k C : ℕ}
    {sel : UInt256} (hauth : relyAuthWord σ I = ⟨1⟩)
    (h : RD jugBytecode I g s0 ⟨1720⟩
      [relyUsrMaskedWord I, ⟨226⟩, sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    ∃ k' C', RD jugBytecode I g s0 ⟨1809⟩
      [relyUsrMaskedWord I, ⟨226⟩, sel]
      (relyAuthHashMem I) (UInt256.ofNat 3) ByteArray.empty (cA, σ) k' C' := by
  have hauthSlot :
      UInt256.ofNat (fromByteArrayBigEndian
          (ffi.KEC ((relyAuthHashMem I).readWithPadding 0 64))) =
        mapSlot (relySourceWord I) ⟨0⟩ := by
    simpa [relyAuthHashMem, mapSlot, solcMappingSlot] using
      twoWordHashMem_solcMappingSlot (⟨0⟩ : UInt256) (relySourceWord I)
        solcFreePtrMem_size
  have rd1726pre := evm_run h with [
    raw jumpdest (by decide +native) (by evm_ov),
    raw caller (by decide +native) (by evm_ov),
    raw push1 ⟨0⟩ (by decide +native) (by evm_ov),
    raw swap1 (by decide +native) (by evm_ov),
    raw dup2 (by decide +native) (by evm_ov)]
  have rd1727 := rd1726pre.mstore 0 (wordAt0Mem (relySourceWord I) solcFreePtrMem)
    (UInt256.ofNat 3) (by decide +native) mem_cost (by rfl) (by decide +native) (by evm_ov)
  have rd1731pre := evm_run rd1727 with [
    raw push1 ⟨32⟩ (by decide +native) (by evm_ov),
    raw dup2 (by decide +native) (by evm_ov),
    raw swap1 (by decide +native) (by evm_ov)]
  have rd1732 := rd1731pre.mstore 0 (relyAuthHashMem I)
    (UInt256.ofNat 3) (by decide +native) mem_cost (by rfl) (by decide +native) (by evm_ov)
  have rd1735pre := evm_run rd1732 with [
    raw push1 ⟨64⟩ (by decide +native) (by evm_ov),
    raw swap1 (by decide +native) (by evm_ov)]
  have rd1736 := rd1735pre.keccak256 0 (mapSlot (relySourceWord I) ⟨0⟩)
    (UInt256.ofNat 3) (by decide +native) mem_cost hauthSlot (by decide +native)
    (by evm_ov)
  obtain ⟨k1737, C1737, rd1737raw⟩ := rd1736.sload (by decide +native) (by evm_ov)
  have rd1737 : RD jugBytecode I g s0 ⟨1737⟩
      (relyAuthWord σ I :: relyUsrMaskedWord I :: ⟨226⟩ :: [sel])
      (relyAuthHashMem I) (UInt256.ofNat 3) ByteArray.empty (cA, σ) k1737 C1737 := by
    simpa [relyAuthWord, jugSlotWord, relyAuthStorageSlot_eq_mapSlot_source I] using rd1737raw
  have rd1740pre := evm_run rd1737 with [
    raw push1 ⟨1⟩ (by decide +native) (by evm_ov),
    raw eq (by decide +native) (by evm_ov)]
  rw [hauth, u256_eq_refl] at rd1740pre
  have rd1743 := rd1740pre.pushConst (⟨1809⟩ : UInt256)
    (width := 2) (op := .PUSH2) (by decide) (by decide +native) (by evm_ov)
  exact ⟨_, _, rd1743.jumpiT (by decide +native) one_ne_zero_uint
    (by jump_dest) (by evm_ov)⟩

set_option maxHeartbeats 1000000 in
theorem jugRelyX_unauthorized {cA σ I} {g : Sat256} {s0 : State} {k C : ℕ}
    {sel : UInt256} (hauth : relyAuthWord σ I ≠ ⟨1⟩)
    (h : RD jugBytecode I g s0 ⟨1720⟩
      [relyUsrMaskedWord I, ⟨226⟩, sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    RDrev jugBytecode g s0 := by
  have hauthSlot :
      UInt256.ofNat (fromByteArrayBigEndian
          (ffi.KEC ((relyAuthHashMem I).readWithPadding 0 64))) =
        mapSlot (relySourceWord I) ⟨0⟩ := by
    simpa [relyAuthHashMem, mapSlot, solcMappingSlot] using
      twoWordHashMem_solcMappingSlot (⟨0⟩ : UInt256) (relySourceWord I)
        solcFreePtrMem_size
  have rd1726pre := evm_run h with [
    raw jumpdest (by decide +native) (by evm_ov),
    raw caller (by decide +native) (by evm_ov),
    raw push1 ⟨0⟩ (by decide +native) (by evm_ov),
    raw swap1 (by decide +native) (by evm_ov),
    raw dup2 (by decide +native) (by evm_ov)]
  have rd1727 := rd1726pre.mstore 0 (wordAt0Mem (relySourceWord I) solcFreePtrMem)
    (UInt256.ofNat 3) (by decide +native) mem_cost (by rfl) (by decide +native) (by evm_ov)
  have rd1731pre := evm_run rd1727 with [
    raw push1 ⟨32⟩ (by decide +native) (by evm_ov),
    raw dup2 (by decide +native) (by evm_ov),
    raw swap1 (by decide +native) (by evm_ov)]
  have rd1732 := rd1731pre.mstore 0 (relyAuthHashMem I)
    (UInt256.ofNat 3) (by decide +native) mem_cost (by rfl) (by decide +native) (by evm_ov)
  have rd1735pre := evm_run rd1732 with [
    raw push1 ⟨64⟩ (by decide +native) (by evm_ov),
    raw swap1 (by decide +native) (by evm_ov)]
  have rd1736 := rd1735pre.keccak256 0 (mapSlot (relySourceWord I) ⟨0⟩)
    (UInt256.ofNat 3) (by decide +native) mem_cost hauthSlot (by decide +native)
    (by evm_ov)
  obtain ⟨k1737, C1737, rd1737raw⟩ := rd1736.sload (by decide +native) (by evm_ov)
  have rd1737 : RD jugBytecode I g s0 ⟨1737⟩
      (relyAuthWord σ I :: relyUsrMaskedWord I :: ⟨226⟩ :: [sel])
      (relyAuthHashMem I) (UInt256.ofNat 3) ByteArray.empty (cA, σ) k1737 C1737 := by
    simpa [relyAuthWord, jugSlotWord, relyAuthStorageSlot_eq_mapSlot_source I] using rd1737raw
  have rd1740pre := evm_run rd1737 with [
    raw push1 ⟨1⟩ (by decide +native) (by evm_ov),
    raw eq (by decide +native) (by evm_ov)]
  have heq : UInt256.eq (⟨1⟩ : UInt256) (relyAuthWord σ I) = ⟨0⟩ := by
    exact u256_eq_of_ne (by intro hbad; exact hauth hbad.symm)
  rw [heq] at rd1740pre
  have rd1743 := rd1740pre.pushConst (⟨1809⟩ : UInt256)
    (width := 2) (op := .PUSH2) (by decide) (by decide +native) (by evm_ov)
  have rd1744 := rd1743.jumpiNT (by decide +native) rfl (by evm_ov)
  exact RD.solcErrorStringRevertTail
    (pc := ⟨1744⟩)
    (len := ⟨18⟩)
    (rawWord := ⟨0x129d59cbdb9bdd0b585d5d1a1bdc9a5e9959⟩)
    (shift := ⟨114⟩)
    (word := ⟨0x4a75672f6e6f742d617574686f72697a65640000000000000000000000000000⟩)
    (op := .PUSH18)
    (width := 18)
    rd1744
    (by
      unfold solcErrorStringRevertTailWf
      repeat' first | apply And.intro | decide +native)
    (by decide)
    relyNotAuthorizedWord
    (relyAuthHashMem_size I)
    (relyAuthHashMem_read64 I)
    (by simp only [List.length_cons, List.length_nil]; omega)

set_option maxHeartbeats 1000000 in
theorem jugRelyX_storeAuthorized {cA σ I} {g : Sat256} {s0 : State} {k C : ℕ}
    {sel : UInt256} (hperm : I.perm = true)
    (h : RD jugBytecode I g s0 ⟨1809⟩
      [relyUsrMaskedWord I, ⟨226⟩, sel]
      (relyAuthHashMem I) (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    RDret jugBytecode g s0
      (cA, sstoreAccountMap I.codeOwner σ (relyUsrStorageSlot I) ⟨1⟩)
      ByteArray.empty := by
  have hstoreSlot :
      UInt256.ofNat (fromByteArrayBigEndian
          (ffi.KEC ((relyStoreHashMem I).readWithPadding 0 64))) =
        mapSlot (relyUsrMaskedWord I) ⟨0⟩ := by
    simpa [relyStoreHashMem, mapSlot, solcMappingSlot] using
      twoWordHashMem_solcMappingSlot (⟨0⟩ : UInt256) (relyUsrMaskedWord I)
        (relyAuthHashMem_size I)
  have rd1818pre := evm_run h with [
    raw jumpdest (by decide +native) (by evm_ov),
    raw push1 ⟨1⟩ (by decide +native) (by evm_ov),
    raw push1 ⟨1⟩ (by decide +native) (by evm_ov),
    raw push1 ⟨160⟩ (by decide +native) (by evm_ov),
    raw shl (by decide +native) (by evm_ov),
    raw sub (by decide +native) (by evm_ov),
    raw and (by decide +native) (by evm_ov)]
  have hmask :
      UInt256.land
          (UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨160⟩) ⟨1⟩)
          (relyUsrMaskedWord I)
        = relyUsrMaskedWord I := by
    rw [u256_land_comm]
    rw [show UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨160⟩) ⟨1⟩ =
      solcAddrMask from by decide]
    exact solcAddrMask_clean (relyUsrMaskedWord_canonical I)
  rw [hmask] at rd1818pre
  have rd1823pre := evm_run rd1818pre with [
    raw push1 ⟨0⟩ (by decide +native) (by evm_ov),
    raw swap1 (by decide +native) (by evm_ov),
    raw dup2 (by decide +native) (by evm_ov)]
  have rd1824 := rd1823pre.mstore 0
    (wordAt0Mem (relyUsrMaskedWord I) (relyAuthHashMem I))
    (UInt256.ofNat 3) (by decide +native) mem_cost (by rfl) (by decide +native)
    (by evm_ov)
  have rd1828pre := evm_run rd1824 with [
    raw push1 ⟨32⟩ (by decide +native) (by evm_ov),
    raw dup2 (by decide +native) (by evm_ov),
    raw swap1 (by decide +native) (by evm_ov)]
  have rd1829 := rd1828pre.mstore 0 (relyStoreHashMem I)
    (UInt256.ofNat 3) (by decide +native) mem_cost (by rfl) (by decide +native)
    (by evm_ov)
  have rd1832pre := evm_run rd1829 with [
    raw push1 ⟨64⟩ (by decide +native) (by evm_ov),
    raw swap1 (by decide +native) (by evm_ov)]
  have rd1833 := rd1832pre.keccak256 0 (mapSlot (relyUsrMaskedWord I) ⟨0⟩)
    (UInt256.ofNat 3) (by decide +native) mem_cost hstoreSlot (by decide +native)
    (by evm_ov)
  have rd1836pre := evm_run rd1833 with [
    raw push1 ⟨1⟩ (by decide +native) (by evm_ov),
    raw swap1 (by decide +native) (by evm_ov)]
  obtain ⟨_, _, rd1837raw⟩ := rd1836pre.sstore hperm (by decide +native)
    (by simp only [List.length_cons, List.length_nil]; omega)
  have rd226 := rd1837raw.jump (by decide +native) (by jump_dest) (by evm_ov)
  have rd227 := rd226.jumpdest (by decide +native) (by evm_ov)
  simpa [relyUsrStorageSlot_eq_mapSlot_masked I] using
    RD.stop rd227 (by decide +native) (by evm_ov)

theorem jugX_rely_ok {cA gh bl σ σ₀ A I} {g : Sat256} {sel : UInt256}
    (hsz36 : 36 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hperm : I.perm = true) (hauth : relyAuthWord σ I = ⟨1⟩)
    (hreach : ∃ k C, RD jugBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨391⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    RDret jugBytecode g (initState cA gh bl σ σ₀ g A I)
      (cA, sstoreAccountMap I.codeOwner σ (relyUsrStorageSlot I) ⟨1⟩)
      ByteArray.empty := by
  obtain ⟨_, _, rd1720⟩ := jugRelyX_decoded (g := g) hsz36 hsize hreach
  obtain ⟨_, _, rd1809⟩ := jugRelyX_authorized (I := I) hauth rd1720
  exact jugRelyX_storeAuthorized hperm rd1809

theorem jugX_rely_unauthorized {cA gh bl σ σ₀ A I} {g : Sat256} {sel : UInt256}
    (hsz36 : 36 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hauth : relyAuthWord σ I ≠ ⟨1⟩)
    (hreach : ∃ k C, RD jugBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨391⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    RDrev jugBytecode g (initState cA gh bl σ σ₀ g A I) := by
  obtain ⟨_, _, rd1720⟩ := jugRelyX_decoded (g := g) hsz36 hsize hreach
  exact jugRelyX_unauthorized (I := I) hauth rd1720

theorem jugRelyBodyCoreOk
    {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256} {sel : UInt256}
    (hcode : I.code = jugBytecode) (hsize : I.calldata.size < UInt256.size)
    (hperm : I.perm = true) (hwv : I.weiValue = ⟨0⟩)
    (hsz36 : 36 ≤ I.calldata.size)
    (hauth : relyAuthWord σ_evm I = ⟨1⟩)
    (hdispatch : dispatchMsg contract I.calldata = some relyTransition)
    (hdecode :
      decodeCalldataWithMode config.abiDecodeMode (relyTransition.params.map Param.name)
        (transitionSignature relyTransition).paramTypes I.calldata = some (relyStore I))
    (hreach : ∃ k C, RD jugBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) ⟨391⟩ [sel]
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
    simpa [evmSolm, relyAuthWord, jugSlotWord, initState, Solm.EVM.storageLoad,
      State.lookupAccount] using
      jugRelyBodyReturns evmSolm I
        (by simp only [evmSolm, initState]; exact hwv)
        (by simp [evmSolm, initState])
        hauthWord
  exact (jugX_rely_ok (g := Sat256.ofUInt256 g) hsz36 hsize hperm hauth hreach)
    |>.reEquivExecutionGenAccountMapEquiv hcode hdispatch hdecode hbody
      (by simp [relyPostState, evmSolm, initState, storageStore_createdAccounts])
      (by
        simpa [relyPostState, evmSolm, initState, storageStore_accountMap] using
          accountMapEquiv_sstoreAccountMap I.codeOwner (relyUsrStorageSlot I) ⟨1⟩
            hAccounts)
      (by
        simpa [relyTransition] using
          (returnEquiv.fallthrough (o := ByteArray.empty) (r := none) (t := [])
            (dvs := []) rfl (by decide +native) (by decide +native)))

theorem jugRelyBodyCoreUnauthorized
    {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256} {sel : UInt256}
    (hcode : I.code = jugBytecode) (hsize : I.calldata.size < UInt256.size)
    (hwv : I.weiValue = ⟨0⟩)
    (hsz36 : 36 ≤ I.calldata.size)
    (hauth : relyAuthWord σ_evm I ≠ ⟨1⟩)
    (hdispatch : dispatchMsg contract I.calldata = some relyTransition)
    (hdecode :
      decodeCalldataWithMode config.abiDecodeMode (relyTransition.params.map Param.name)
        (transitionSignature relyTransition).paramTypes I.calldata = some (relyStore I))
    (hreach : ∃ k C, RD jugBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) ⟨391⟩ [sel]
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
    simpa [evmSolm, relyAuthWord, jugSlotWord, initState, Solm.EVM.storageLoad,
      State.lookupAccount] using
      jugRelyBodyReverts evmSolm I
        (by simp only [evmSolm, initState]; exact hwv)
        (by simp [evmSolm, initState])
        hauthWord
  exact (jugX_rely_unauthorized (g := Sat256.ofUInt256 g) hsz36 hsize hauth hreach)
    |>.reEquivExecutionRevert hcode hdispatch hdecode hbody

theorem jugRelyBodyCoreDecodeFailed_short
    {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256} {sel : UInt256}
    (hcode : I.code = jugBytecode) (hsize : I.calldata.size < UInt256.size)
    (hsz4 : 4 ≤ I.calldata.size) (hshort : I.calldata.size < 36)
    (hdispatch : dispatchMsg contract I.calldata = some relyTransition)
    (hreach : ∃ k C, RD jugBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) ⟨391⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ_evm) k C) :
    runtimeEquivalenceFor config contract cA gh bl σ_evm σ_solm σ₀ g A I := by
  exact (jugRelyX_shortarg (g := Sat256.ofUInt256 g) hsz4 hsize hshort hreach)
    |>.reEquivDecodingFailed hcode hdispatch (jugDecode_rely_none_short hsz4 hshort)

theorem jugRelyBody {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256}
    (hcode : I.code = jugBytecode)
    (hsize : I.calldata.size < UInt256.size)
    (hperm : I.perm = true)
    (hwv : I.weiValue = ⟨0⟩)
    (hsel : selIs I (jugSelBytes 8))
    (hAccounts : accountMapEquiv σ_evm σ_solm) :
    runtimeEquivalenceFor config contract cA gh bl σ_evm σ_solm σ₀ g A I := by
  have hsz4 : 4 ≤ I.calldata.size :=
    calldata_size_ge_of_selIs I (jugSelBytes 8) rfl hsel
  have hdispatch : dispatchMsg contract I.calldata = some relyTransition :=
    jugDispatchRely hsel
  have hreach := jugReachRelyBody (cA := cA) (gh := gh) (bl := bl)
    (σ := σ_evm) (σ₀ := σ₀) (A := A) (I := I) (g := Sat256.ofUInt256 g)
    hcode hwv hsz4 hsize hsel
  by_cases hsz36 : 36 ≤ I.calldata.size
  · by_cases hauth : relyAuthWord σ_evm I = ⟨1⟩
    · exact jugRelyBodyCoreOk hcode hsize hperm hwv hsz36 hauth hdispatch
        (jugDecode_rely_ok hsz36) hreach hAccounts
    · exact jugRelyBodyCoreUnauthorized hcode hsize hwv hsz36 hauth hdispatch
        (jugDecode_rely_ok hsz36) hreach hAccounts
  · exact jugRelyBodyCoreDecodeFailed_short hcode hsize hsz4 (by omega)
      hdispatch hreach

end Benchmarks.Dss.Jug
