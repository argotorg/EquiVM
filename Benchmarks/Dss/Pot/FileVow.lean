import Benchmarks.Dss.Pot.FileDsr

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

set_option maxRecDepth 2000000
set_option maxHeartbeats 0

namespace Benchmarks.Dss.Pot

/-! ## `file(bytes32,address)` external (auth): sets `vow` (address slot 6) when `what == "vow"`.
    Group `@54` arm 4, entry `@637`, logic `@2143`.  Selector `0xd4e8be83`. -/

abbrev fileVowWhat (I : ExecutionEnv) : List UInt8 :=
  (I.calldata.toList.drop 4).take 32

abbrev fileVowData (I : ExecutionEnv) : AccountAddress :=
  AccountAddress.ofNat (calldataWord I.calldata 36).toNat

abbrev fileVowDataWord (I : ExecutionEnv) : UInt256 :=
  calldataWord I.calldata 36

abbrev fileVowDataMaskedWord (I : ExecutionEnv) : UInt256 :=
  UInt256.land solcAddrMask (fileVowDataWord I)

abbrev fileVowBytes : List UInt8 :=
  [118, 111, 119, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
   0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]

abbrev fileVowLocals (I : ExecutionEnv) : Store :=
  ((∅ : Store).insert "what" (.fixedBytes bytes32Width (fileVowWhat I))).insert
    "addr" (.address (fileVowData I))

/-! ### Calldata `(bytes32,address)` decode -/

theorem fileVowWhat_length {I : ExecutionEnv} (hsz36 : 36 ≤ I.calldata.size) :
    (fileVowWhat I).length = 32 := by
  simp [fileVowWhat, List.length_take, List.length_drop, byteArray_toList_eq]
  omega

theorem fileVowWhatWord_eq {I : ExecutionEnv} (hsz36 : 36 ≤ I.calldata.size) :
    ABI.bytesToWord (fileVowWhat I) = calldataWord I.calldata 4 := by
  simpa [fileVowWhat] using decode_word_at_eq I.calldata 4 (by omega) (by norm_num)

theorem fileVowWhatWord_eq_of_bytes_eq {I : ExecutionEnv} {bs : List UInt8}
    (hsz36 : 36 ≤ I.calldata.size) (hbs : fileVowWhat I = bs) :
    calldataWord I.calldata 4 = ABI.bytesToWord bs := by
  rw [← hbs]
  exact (fileVowWhatWord_eq (I := I) hsz36).symm

theorem fileVowWhat_eq_of_word_eq {I : ExecutionEnv} {bs : List UInt8}
    (hsz36 : 36 ≤ I.calldata.size) (hword : calldataWord I.calldata 4 = ABI.bytesToWord bs)
    (hbsLen : bs.length = 32) :
    fileVowWhat I = bs := by
  have hto := toBytesBE_bytesToWord_of_length (bs := fileVowWhat I)
    (fileVowWhat_length (I := I) hsz36)
  rw [fileVowWhatWord_eq (I := I) hsz36, hword] at hto
  exact hto.symm.trans (toBytesBE_bytesToWord_of_length (bs := bs) hbsLen)

theorem fileVowWhatWord_ne_of_bytes_ne {I : ExecutionEnv} {bs : List UInt8}
    (hsz36 : 36 ≤ I.calldata.size) (hneq : fileVowWhat I ≠ bs)
    (hbsLen : bs.length = 32) :
    calldataWord I.calldata 4 ≠ ABI.bytesToWord bs := by
  intro hword
  exact hneq (fileVowWhat_eq_of_word_eq hsz36 hword hbsLen)

theorem fileVowDataMaskedWord_canonical (I : ExecutionEnv) :
    (fileVowDataMaskedWord I).toNat < EVM.addressModulus := by
  unfold fileVowDataMaskedWord
  rw [u256_land_comm solcAddrMask (fileVowDataWord I)]
  exact solcAddrMask_result_canonical (fileVowDataWord I)

theorem fileVowData_value_masked (I : ExecutionEnv) :
    (.address (fileVowData I) : Value) =
      .address (AccountAddress.ofNat (fileVowDataMaskedWord I).toNat) := by
  simpa [fileVowData, fileVowDataMaskedWord, fileVowDataWord] using
    (solcAddressValue_masked (calldataWord I.calldata 36))

theorem decodeABIValues_bytes32_address_legacy_ok {bytes : List UInt8}
    (hlen0 : (bytes.take 32).length = 32)
    (hlen32 : ((bytes.drop 32).take 32).length = 32) :
    decodeABIValues? [abiBytes32, abiAddress] bytes 0 0 64 64 DecodeMode.legacySolc05 =
      some ([.fixedBytes abiBytes32Width (bytes.take 32),
        .address (AccountAddress.ofNat
          (ABI.bytesToWord ((bytes.drop 32).take 32)).toNat)], 64) := by
  simp [decodeABIValues?, abiBytes32, abiBytes32Width, abiAddress, isDynamicABIType,
    staticABIEncodedSize?, decodeABIValue?, readBytes?, hlen0]
  simp [readWord?, readBytes?, decodeABIWord?, UInt256.toNat, hlen32]

theorem decodeABIValues_bytes32_address_legacy_none_short {bytes : List UInt8}
    (hshort : bytes.length < 64) :
    decodeABIValues? [abiBytes32, abiAddress] bytes 0 0 64 64 DecodeMode.legacySolc05 =
      none := by
  simp only [decodeABIValues?, abiBytes32, abiBytes32Width, abiAddress, isDynamicABIType,
    Bool.false_eq_true, if_false, staticABIEncodedSize?, bind, Option.bind, Nat.zero_add]
  by_cases h32 : bytes.length < 32
  · have htake0n : ¬ (bytes.take 32).length = 32 := by
      rw [List.length_take]
      omega
    have hnot : ¬ 32 ≤ bytes.length := by omega
    simp [decodeABIValue?, readBytes?, hnot]
  · have htake0 : (bytes.take 32).length = 32 := by
      rw [List.length_take]
      omega
    have htake32n : ¬ ((bytes.drop 32).take 32).length = 32 := by
      rw [List.length_take, List.length_drop]
      omega
    simp [decodeABIValue?, readBytes?, htake0]
    have hnot : ¬ 32 ≤ bytes.length - 32 := by
      rw [List.length_take, List.length_drop] at htake32n
      omega
    simp [readWord?, readBytes?, hnot]

theorem decodeCalldata_legacyBytes32_address_ok {cd : ByteArray} {x y : Solm.Ident}
    (hsz68 : 68 ≤ cd.size) :
    decodeCalldataWithMode DecodeMode.legacySolc05 [x, y] [abiBytes32, abiAddress] cd =
      some (((∅ : Solm.Store).insert x
        (.fixedBytes abiBytes32Width ((cd.toList.drop 4).take 32))).insert y
        (.address (AccountAddress.ofNat (calldataWord cd 36).toNat))) := by
  have htlen : cd.toList.length = cd.size := by
    rw [byteArray_toList_eq, Array.length_toList]
    rfl
  have htake4 : ((cd.toList.drop 4).take 32).length = 32 := by
    rw [List.length_take, List.length_drop, htlen]
    omega
  have htake36 : ((cd.toList.drop 36).take 32).length = 32 := by
    rw [List.length_take, List.length_drop, htlen]
    omega
  have hword36 : ABI.bytesToWord ((cd.toList.drop 36).take 32) = calldataWord cd 36 :=
    decode_word_at_eq cd 36 (by omega) (by norm_num)
  unfold decodeCalldataWithMode decodeCalldata
  rw [if_neg (by rw [htlen]; omega : ¬ cd.toList.length < 4)]
  rw [if_neg (by simp [abiBytes32, abiAddress, isDynamicABIType])]
  simp only [decodeCalldata.decodeArgs]
  rw [show abiTupleHeadSize? [abiBytes32, abiAddress] = some 64 by native_decide]
  simp only [bind, Option.bind]
  rw [decodeABIValues_bytes32_address_legacy_ok (bytes := cd.toList.drop 4)
    (by simpa using htake4)
    (by simpa [List.drop_drop, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using htake36)]
  rw [if_neg (by rw [List.length_drop, htlen]; omega : ¬ (cd.toList.drop 4).length < 64)]
  simp [decodeCalldata.insertValues]
  rw [hword36]

theorem decodeCalldata_legacyBytes32_address_none_short {cd : ByteArray}
    {x y : Solm.Ident} (hsz4 : 4 ≤ cd.size) (hshort : cd.size < 68) :
    decodeCalldataWithMode DecodeMode.legacySolc05 [x, y] [abiBytes32, abiAddress] cd =
      none := by
  have htlen : cd.toList.length = cd.size := by
    rw [byteArray_toList_eq, Array.length_toList]
    rfl
  unfold decodeCalldataWithMode decodeCalldata
  rw [if_neg (by rw [htlen]; omega : ¬ cd.toList.length < 4)]
  rw [if_neg (by simp [abiBytes32, abiAddress, isDynamicABIType])]
  simp only [decodeCalldata.decodeArgs]
  rw [show abiTupleHeadSize? [abiBytes32, abiAddress] = some 64 by native_decide]
  simp only [bind, Option.bind]
  by_cases hbytes : (cd.toList.drop 4).length < 64
  · rw [if_pos hbytes]
  · rw [if_neg hbytes]
    rw [decodeABIValues_bytes32_address_legacy_none_short (bytes := cd.toList.drop 4) (by
      rw [List.length_drop, htlen]
      omega)]

theorem potDecode_fileVow_ok {I : ExecutionEnv} (hsz68 : 68 ≤ I.calldata.size) :
    decodeCalldataWithMode config.abiDecodeMode (fileVowTransition.params.map Param.name)
      (transitionSignature fileVowTransition).paramTypes I.calldata =
        some (fileVowLocals I) := by
  simpa [config, fileVowTransition, bytes32, bytes32Width, addr, fileVowLocals,
    fileVowWhat, fileVowData, abiBytes32, abiBytes32Width, abiAddress] using
    (decodeCalldata_legacyBytes32_address_ok (cd := I.calldata) (x := "what")
      (y := "addr") hsz68)

theorem potDecode_fileVow_none_short {I : ExecutionEnv}
    (hsz4 : 4 ≤ I.calldata.size) (hshort : I.calldata.size < 68) :
    decodeCalldataWithMode config.abiDecodeMode (fileVowTransition.params.map Param.name)
      (transitionSignature fileVowTransition).paramTypes I.calldata = none := by
  simpa [config, fileVowTransition, bytes32, bytes32Width, addr, abiBytes32,
    abiBytes32Width, abiAddress] using
    (decodeCalldata_legacyBytes32_address_none_short (cd := I.calldata) (x := "what")
      (y := "addr") hsz4 hshort)

/-! ### Local-store lookups -/

theorem fileVowLocals_get_what (I : ExecutionEnv) :
    (fileVowLocals I).get? "what" =
      some (.fixedBytes bytes32Width (fileVowWhat I)) := by
  rw [fileVowLocals, store_get_ne _ _ (by decide), store_get_self]

theorem fileVowLocals_get_addr (I : ExecutionEnv) :
    (fileVowLocals I).get? "addr" = some (.address (fileVowData I)) := by
  rw [fileVowLocals, store_get_self]

theorem fileVowLocals_get_wards (I : ExecutionEnv) :
    (fileVowLocals I).get? "wards" = none := by
  rw [fileVowLocals, store_get_ne _ _ (by decide), store_get_ne _ _ (by decide)]
  simp

theorem fileVowLocals_get_vow (I : ExecutionEnv) :
    (fileVowLocals I).get? "vow" = none := by
  rw [fileVowLocals, store_get_ne _ _ (by decide), store_get_ne _ _ (by decide)]
  simp

/-! ### Solm-side expression evaluation -/

theorem evalExpr_fileVowAddr {evm : EVM.State} {I : ExecutionEnv} {locals : Store}
    (h : locals.get? "addr" = some (.address (fileVowData I))) :
    evalExpr? config { contract := contract, locals := locals } evm (.var "addr") =
      .ok (.address (fileVowData I)) := by
  rw [evalExpr?]
  change EvalResult.ofOption EvalError.unboundVariable (locals.get? "addr") =
    .ok (.address (fileVowData I))
  rw [h]
  rfl

theorem evalExpr_fileVowWhatEq_true {evm : EVM.State} {I : ExecutionEnv} {locals : Store}
    {bs : List UInt8}
    (hget : locals.get? "what" = some (.fixedBytes bytes32Width (fileVowWhat I)))
    (hwhat : fileVowWhat I = bs) :
    evalExpr? config { contract := contract, locals := locals } evm
      (.binary .eq (.var "what") (.fixedBytesLit bytes32Width bs)) = .ok (.bool true) := by
  have hvar :
      evalExpr? config { contract := contract, locals := locals } evm (.var "what") =
        .ok (.fixedBytes bytes32Width (fileVowWhat I)) := by
    rw [evalExpr?]
    change EvalResult.ofOption EvalError.unboundVariable (locals.get? "what") =
      .ok (.fixedBytes bytes32Width (fileVowWhat I))
    rw [hget]
    rfl
  rw [evalExpr?]
  simp only [hvar, EvalResult.bind, bind]
  simp [evalExpr?, evalBinaryOp?, hwhat]
  all_goals decide

theorem evalExpr_fileVowWhatEq_false {evm : EVM.State} {I : ExecutionEnv} {locals : Store}
    {bs : List UInt8}
    (hget : locals.get? "what" = some (.fixedBytes bytes32Width (fileVowWhat I)))
    (hwhat : fileVowWhat I ≠ bs) :
    evalExpr? config { contract := contract, locals := locals } evm
      (.binary .eq (.var "what") (.fixedBytesLit bytes32Width bs)) = .ok (.bool false) := by
  have hvar :
      evalExpr? config { contract := contract, locals := locals } evm (.var "what") =
        .ok (.fixedBytes bytes32Width (fileVowWhat I)) := by
    rw [evalExpr?]
    change EvalResult.ofOption EvalError.unboundVariable (locals.get? "what") =
      .ok (.fixedBytes bytes32Width (fileVowWhat I))
    rw [hget]
    rfl
  rw [evalExpr?]
  simp only [hvar, EvalResult.bind, bind]
  simp [evalExpr?, evalBinaryOp?, hwhat]
  all_goals decide

theorem evalStorageRef_fileVow_auth (evm : EVM.State) (I : ExecutionEnv)
    (hsrc : evm.executionEnv.source = I.source) :
    evalStorageRef config { contract := contract, locals := fileVowLocals I } evm
      (wardsRef sender) = .ok (relyAuthEvaledRef I) := by
  simp [evalStorageRef, evalStorageRefStep, wardsRef, sender, envValue, relyAuthEvaledRef,
    relyAuthKey, hsrc, valueToKey?, EvalResult.bind, EvalResult.ofOption, bind, pure,
    evalExpr?]

theorem evalExpr_fileVow_auth_true (evm : EVM.State) (I : ExecutionEnv)
    (hsrc : evm.executionEnv.source = I.source)
    (hload :
      Solm.EVM.storageLoad evm evm.executionEnv.codeOwner (relyAuthStorageSlot I) = ⟨1⟩) :
    evalExpr? config { contract := contract, locals := fileVowLocals I } evm
      (.binary .eq (.storage (wardsRef sender)) (.intLit 1)) = .ok (.bool true) := by
  have hstorage :
      evalExpr? config { contract := contract, locals := fileVowLocals I } evm
        (.storage (wardsRef sender)) = .ok (.int 1) := by
    rw [evalExpr_storage_scalar_value
      (cfg := config)
      (solm := { contract := contract, locals := fileVowLocals I })
      (slot := wardsRef sender)
      (er := relyAuthEvaledRef I)
      (t := .int uint256Int)
      (loc := wordLoc (relyAuthStorageSlot I))
      (value := .int 1)
      (hbase := fileVowLocals_get_wards I)
      (her := evalStorageRef_fileVow_auth evm I hsrc)
      (hty := by simp [storageTypeAt?, storageTypeStep?, contract, storageDecls, uint256St])
      (hloc := by rfl)
      (hload := by simpa [hload] using potStorageLocLoad_uint256 evm (relyAuthStorageSlot I))]
  simp only [evalExpr?, hstorage, EvalResult.bind, bind, pure]
  rfl

theorem evalExpr_fileVow_auth_false (evm : EVM.State) (I : ExecutionEnv)
    (hsrc : evm.executionEnv.source = I.source)
    (hload :
      Solm.EVM.storageLoad evm evm.executionEnv.codeOwner (relyAuthStorageSlot I) ≠ ⟨1⟩) :
    evalExpr? config { contract := contract, locals := fileVowLocals I } evm
      (.binary .eq (.storage (wardsRef sender)) (.intLit 1)) = .ok (.bool false) := by
  have hstorage :
      evalExpr? config { contract := contract, locals := fileVowLocals I } evm
        (.storage (wardsRef sender)) =
          .ok (.int (Int.ofNat
            (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner
              (relyAuthStorageSlot I)).toNat)) := by
    exact evalExpr_storage_scalar_value
      (cfg := config)
      (solm := { contract := contract, locals := fileVowLocals I })
      (slot := wardsRef sender)
      (er := relyAuthEvaledRef I)
      (t := .int uint256Int)
      (loc := wordLoc (relyAuthStorageSlot I))
      (hbase := fileVowLocals_get_wards I)
      (her := evalStorageRef_fileVow_auth evm I hsrc)
      (hty := by simp [storageTypeAt?, storageTypeStep?, contract, storageDecls, uint256St])
      (hloc := by rfl)
      (hload := potStorageLocLoad_uint256 evm (relyAuthStorageSlot I))
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
            (relyAuthStorageSlot I)).toNat) == Value.int 1) = false := beq_eq_false_iff_ne.mpr hne
  simp only [evalExpr?, hstorage, EvalResult.bind, bind, pure]
  change evalBinaryOp? BinaryOp.eq
      (Value.int (Int.ofNat
        (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner (relyAuthStorageSlot I)).toNat))
      (Value.int 1) = .ok (.bool false)
  simp only [evalBinaryOp?]
  rw [hbeq]

theorem assign_fileVowStorage (evm : EVM.State) (I : ExecutionEnv) :
    let evm' := Solm.EVM.storageStore evm evm.executionEnv.codeOwner ⟨6⟩
      (setAddressOffset0Word (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨6⟩)
        (fileVowDataMaskedWord I))
    assignStorageRef? config { contract := contract, locals := fileVowLocals I } evm
      .storage vowRef (.address (fileVowData I)) =
        .ok ({ contract := contract, locals := fileVowLocals I }, evm') := by
  intro evm'
  rw [fileVowData_value_masked I]
  apply assignStorageRef_storage_scalar_value
      (ty := addrSt)
      (er := ({ base := "vow", steps := [] } : EvaledStorageRef))
      (loc := addrLoc ⟨6⟩)
      (hbase := fileVowLocals_get_vow I)
      (her := by simp [vowRef, evalStorageRef, evalStorageRefSteps, EvalResult.bind, pure, bind])
      (hty := by simp [storageTypeAt?, contract, storageDecls, addrSt])
      (hloc := by rfl)
      (hscalar := by trivial)
  simpa [addrLoc, evm'] using
    storageLocStore_address_offset0 evm ⟨6⟩ (fileVowDataMaskedWord I)
      (fileVowDataMaskedWord_canonical I)

/-! ### Solm-side transition body results -/

theorem potFileVowSourceBody {cA gh bl σ σ₀ A I} {g : UInt256}
    (hwv : I.weiValue = ⟨0⟩)
    (hauth : relyAuthWord σ I = ⟨1⟩)
    (hwhat : fileVowWhat I = fileVowBytes) :
    let locals := fileVowLocals I
    let evm0 := initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I
    let evm1 := Solm.EVM.storageStore evm0 I.codeOwner ⟨6⟩
      (setAddressOffset0Word (Solm.EVM.storageLoad evm0 I.codeOwner ⟨6⟩)
        (fileVowDataMaskedWord I))
    ExecTransitionBody config contract evm0 locals fileVowTransition.body
      (.returned { contract := contract, locals := locals } evm1 none) := by
  intro locals evm0 evm1
  have hguard :
      evalExpr? config { contract := contract, locals := locals } evm0
        (.binary .eq (.storage (wardsRef sender)) (.intLit 1)) = .ok (.bool true) := by
    simpa [locals] using evalExpr_fileVow_auth_true evm0 I
      (by simp [evm0, initState])
      (by
        simpa [evm0, relyAuthWord, potSlotWord, initState, Solm.EVM.storageLoad,
          State.lookupAccount] using hauth)
  have hcond :
      evalExpr? config { contract := contract, locals := locals } evm0
        (.binary .eq (.var "what") vowParamLit) = .ok (.bool true) := by
    simpa [vowParamLit, fileVowBytes] using
      (evalExpr_fileVowWhatEq_true (evm := evm0) (I := I) (locals := locals)
        (bs := fileVowBytes) (by simpa [locals] using fileVowLocals_get_what I) hwhat)
  have haddr :
      evalExpr? config { contract := contract, locals := locals } evm0 (.var "addr") =
        .ok (.address (fileVowData I)) := by
    exact evalExpr_fileVowAddr (evm := evm0) (I := I) (locals := locals)
      (fileVowLocals_get_addr I)
  have hassign :
      assignStorageRef? config { contract := contract, locals := locals } evm0
        .storage vowRef (.address (fileVowData I)) =
          .ok ({ contract := contract, locals := locals }, evm1) := by
    simpa [locals, evm1, evm0, initState] using assign_fileVowStorage evm0 I
  have hthen :
      ExecBlock config { contract := contract, locals := locals } evm0
        [.assign .storage vowRef (.var "addr")]
        (.ok { contract := contract, locals := locals } evm1) :=
    ExecBlock.consNormal (ExecStmt.assign haddr hassign) ExecBlock.nil
  have hblock :
      ExecBlock config { contract := contract, locals := locals } evm0 fileVowTransition.body
        (.ok { contract := contract, locals := locals } evm1) := by
    refine ExecBlock.consNormal (ExecStmt.requireTrue ?_) ?_
    · exact evalCallvalueEq_true (by simp [evm0, initState]; exact hwv)
    refine ExecBlock.consNormal (ExecStmt.requireTrue hguard) ?_
    exact ExecBlock.consNormal (ExecStmt.iteTrue hcond hthen) ExecBlock.nil
  simpa [ExecTransitionBody, locals, evm0, evm1] using ExecFuncBody.execBlockOK hblock

theorem potFileVowSourceBodyAuthReverts {cA gh bl σ σ₀ A I} {g : UInt256}
    (hwv : I.weiValue = ⟨0⟩)
    (hauth : relyAuthWord σ I ≠ ⟨1⟩) :
    let locals := fileVowLocals I
    let evm0 := initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I
    ExecTransitionBody config contract evm0 locals fileVowTransition.body .reverted := by
  intro locals evm0
  have hguard :
      evalExpr? config { contract := contract, locals := locals } evm0
        (.binary .eq (.storage (wardsRef sender)) (.intLit 1)) = .ok (.bool false) := by
    simpa [locals] using evalExpr_fileVow_auth_false evm0 I
      (by simp [evm0, initState])
      (by
        simpa [evm0, relyAuthWord, potSlotWord, initState, Solm.EVM.storageLoad,
          State.lookupAccount] using hauth)
  refine ExecFuncBody.execBlockRevert ?_
  simpa [fileVowTransition, nonpayable, auth] using
    nonpayableSecondRequireReverts
      (cfg := config)
      (solm := { contract := contract, locals := locals })
      (evm := evm0)
      (guard := .binary .eq (.storage (wardsRef sender)) (.intLit 1))
      (rest := [.ite (.binary .eq (.var "what") vowParamLit)
        [.assign .storage vowRef (.var "addr")] [.require (.boolLit false)]])
      (by simp [evm0, initState]; exact hwv)
      hguard

theorem potFileVowSourceBodyUnrecognized {cA gh bl σ σ₀ A I} {g : UInt256}
    (hwv : I.weiValue = ⟨0⟩)
    (hauth : relyAuthWord σ I = ⟨1⟩)
    (hwhat : fileVowWhat I ≠ fileVowBytes) :
    let locals := fileVowLocals I
    let evm0 := initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I
    ExecTransitionBody config contract evm0 locals fileVowTransition.body .reverted := by
  intro locals evm0
  have hguard :
      evalExpr? config { contract := contract, locals := locals } evm0
        (.binary .eq (.storage (wardsRef sender)) (.intLit 1)) = .ok (.bool true) := by
    simpa [locals] using evalExpr_fileVow_auth_true evm0 I
      (by simp [evm0, initState])
      (by
        simpa [evm0, relyAuthWord, potSlotWord, initState, Solm.EVM.storageLoad,
          State.lookupAccount] using hauth)
  have hcond :
      evalExpr? config { contract := contract, locals := locals } evm0
        (.binary .eq (.var "what") vowParamLit) = .ok (.bool false) := by
    simpa [vowParamLit, fileVowBytes] using
      (evalExpr_fileVowWhatEq_false (evm := evm0) (I := I) (locals := locals)
        (bs := fileVowBytes) (by simpa [locals] using fileVowLocals_get_what I) hwhat)
  have hreqFalse :
      evalExpr? config { contract := contract, locals := locals } evm0 (.boolLit false) =
        .ok (.bool false) := by
    simp [evalExpr?, pure]
  have helse :
      ExecBlock config { contract := contract, locals := locals } evm0
        [.require (.boolLit false)] .reverted :=
    ExecBlock.consRevert (ExecStmt.requireFalse hreqFalse)
  have hblock :
      ExecBlock config { contract := contract, locals := locals } evm0 fileVowTransition.body
        .reverted := by
    refine ExecBlock.consNormal (ExecStmt.requireTrue ?_) ?_
    · exact evalCallvalueEq_true (by simp [evm0, initState]; exact hwv)
    refine ExecBlock.consNormal (ExecStmt.requireTrue hguard) ?_
    exact ExecBlock.consRevert (ExecStmt.iteFalse hcond helse)
  simpa [ExecTransitionBody, locals, evm0] using ExecFuncBody.execBlockRevert hblock

/-! ### EVM-side trace -/

theorem potReachFileVowBody {cA gh bl σ σ₀ A I} {g : Sat256}
    (hcode : I.code = potBytecode) (hwv : I.weiValue = ⟨0⟩)
    (hsz : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hsel : selIs I (potSelBytes 8)) :
    ∃ k C, RD potBytecode I g (initState cA gh bl σ σ₀ g A I)
        ⟨637⟩ [potSelWord I] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty
        (cA, σ) k C := by
  have hword : potSelWord I = ⟨0xd4e8be83⟩ :=
    potSelWord_eq_of_beq I hsz 0xd4 0xe8 0xbe 0x83 ⟨0xd4e8be83⟩
      (by native_decide) (by simpa [potSelBytes] using hsel)
  have hroot : UInt256.gt (armSelNat potBytecode potRootSplitPc) (potSelWord I) = ⟨0⟩ := by
    rw [hword]; native_decide
  have h43 : UInt256.gt (armSelNat potBytecode potSplit43Pc) (potSelWord I) = ⟨0⟩ := by
    rw [hword]; native_decide
  have heq0 : ∀ j, j < 4 →
      UInt256.eq (armSelNat potBytecode (nthArmPc potBytecode potG54FirstArmPc j))
        (potSelWord I) = ⟨0⟩ := by
    intro j hj; interval_cases j <;> rw [hword] <;> native_decide
  have htake :
      UInt256.eq (armSelNat potBytecode (nthArmPc potBytecode potG54FirstArmPc 4))
        (potSelWord I) ≠ ⟨0⟩ := by rw [hword]; native_decide
  exact potReachG54Body 4 (by omega) ⟨637⟩ hcode hwv hsz hsize hroot h43 heq0 htake
    (by jump_dest) (by native_decide)

theorem RD.potFileVowDecodeToRoutine {code : ByteArray} {g : Sat256} {s0 : State}
    {ee : ExecutionEnv} {k C : ℕ} {ret de sel : UInt256} {R : List UInt256}
    {mem rdata : ByteArray} {aw : UInt256}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    (h : RD code ee g s0 ⟨659⟩ (de :: ⟨4⟩ :: ret :: sel :: R) mem aw rdata acc k C)
    (hwf : code = potBytecode)
    (hroutine : (D_J code 0).contains ⟨2143⟩ = true)
    (hov : R.length + 13 ≤ 1024) :
    ∃ k' C', RD code ee g s0 ⟨2143⟩
      (UInt256.land solcAddrMask (calldataWord ee.calldata 36) ::
        calldataWord ee.calldata 4 :: ret :: sel :: R)
      mem aw rdata acc k' C' := by
  subst hwf
  have rd660 := h.jumpdest (by native_decide) (by evm_ov)
  have rd661 := rd660.pop (by native_decide) (by evm_ov)
  have rd662 := rd661.dup1 (by native_decide) (by evm_ov)
  have rd663 := rd662.calldataload (by native_decide) (by evm_ov)
  have rd664 := rd663.swap1 (by native_decide) (by evm_ov)
  have rd666 := rd664.push1 ⟨32⟩ (by native_decide) (by evm_ov)
  have rd667 := rd666.add (by native_decide) (by evm_ov)
  have rd668 := rd667.calldataload (by native_decide) (by evm_ov)
  have rd670 := rd668.push1 ⟨1⟩ (by native_decide) (by evm_ov)
  have rd672 := rd670.push1 ⟨1⟩ (by native_decide) (by evm_ov)
  have rd674 := rd672.push1 ⟨160⟩ (by native_decide) (by evm_ov)
  have rd675 := rd674.shl (by native_decide) (by evm_ov)
  have rd676 := rd675.sub (by native_decide) (by evm_ov)
  have rd677 := rd676.and (by native_decide) (by evm_ov)
  have rd680 := rd677.push2 ⟨2143⟩ (by native_decide) (by evm_ov)
  exact ⟨_, _, by
    simpa [calldataWord, show (⟨4⟩ : UInt256).toNat = 4 from by decide,
      show (⟨36⟩ : UInt256).toNat = 36 from by decide,
      show UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨160⟩) ⟨1⟩ =
        solcAddrMask from by decide]
      using rd680.jump (by native_decide) hroutine (by evm_ov)⟩

theorem potFileVowX_decoded {cA gh bl σ σ₀ A I} {g : Sat256} {sel : UInt256}
    (hsz68 : 68 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hreach : ∃ k C, RD potBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨637⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    ∃ k C, RD potBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨2143⟩
        [fileVowDataMaskedWord I, calldataWord I.calldata 4, ⟨301⟩, sel]
        solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
  obtain ⟨_, _, hdecoded⟩ := RD.solcExternalStaticArgsLenOk
    (code := potBytecode) (sel := sel) (entry := ⟨637⟩) (ret := ⟨301⟩)
    (decoded := ⟨659⟩) (need := ⟨64⟩) hreach
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by jump_dest)
    (by exact solcDecodeLenCheckOkUnsigned (by simpa using hsz68) hsize)
  obtain ⟨_, _, hroutine⟩ := RD.potFileVowDecodeToRoutine
    (code := potBytecode) (ret := ⟨301⟩) (sel := sel) (R := [])
    hdecoded rfl (by jump_dest) (by simp)
  exact ⟨_, _, by simpa [fileVowDataMaskedWord, fileVowDataWord] using hroutine⟩

set_option maxHeartbeats 1000000 in
theorem potFileVowX_authorized {cA σ I} {g : Sat256} {s0 : State} {k C : ℕ}
    {sel data what : UInt256} (hauth : relyAuthWord σ I = ⟨1⟩)
    (h : RD potBytecode I g s0 ⟨2143⟩
      [data, what, ⟨301⟩, sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    ∃ k' C', RD potBytecode I g s0 ⟨2232⟩
      [data, what, ⟨301⟩, sel]
      (relyAuthHashMem I) (UInt256.ofNat 3) ByteArray.empty (cA, σ) k' C' := by
  have hauthSlot :
      UInt256.ofNat (fromByteArrayBigEndian
          (ffi.KEC ((relyAuthHashMem I).readWithPadding 0 64))) =
        mapSlot (relySourceWord I) ⟨0⟩ := by
    simpa [relyAuthHashMem, mapSlot, solcMappingSlot] using
      twoWordHashMem_solcMappingSlot (⟨0⟩ : UInt256) (relySourceWord I)
        solcFreePtrMem_size
  have rd2149pre := evm_run h with [
    raw jumpdest (by native_decide) (by evm_ov),
    raw caller (by native_decide) (by evm_ov),
    raw push1 ⟨0⟩ (by native_decide) (by evm_ov),
    raw swap1 (by native_decide) (by evm_ov),
    raw dup2 (by native_decide) (by evm_ov)]
  have rd2150 := rd2149pre.mstore 0 (wordAt0Mem (relySourceWord I) solcFreePtrMem)
    (UInt256.ofNat 3) (by native_decide) mem_cost (by rfl) (by native_decide) (by evm_ov)
  have rd2154pre := evm_run rd2150 with [
    raw push1 ⟨32⟩ (by native_decide) (by evm_ov),
    raw dup2 (by native_decide) (by evm_ov),
    raw swap1 (by native_decide) (by evm_ov)]
  have rd2155 := rd2154pre.mstore 0 (relyAuthHashMem I)
    (UInt256.ofNat 3) (by native_decide) mem_cost (by rfl) (by native_decide) (by evm_ov)
  have rd2158pre := evm_run rd2155 with [
    raw push1 ⟨64⟩ (by native_decide) (by evm_ov),
    raw swap1 (by native_decide) (by evm_ov)]
  have rd2159 := rd2158pre.keccak256 0 (mapSlot (relySourceWord I) ⟨0⟩)
    (UInt256.ofNat 3) (by native_decide) mem_cost hauthSlot (by native_decide)
    (by evm_ov)
  obtain ⟨k2160, C2160, rd2160raw⟩ := rd2159.sload (by native_decide) (by evm_ov)
  have rd2160 : RD potBytecode I g s0 ⟨2160⟩
      (relyAuthWord σ I :: data :: what :: ⟨301⟩ :: [sel])
      (relyAuthHashMem I) (UInt256.ofNat 3) ByteArray.empty (cA, σ) k2160 C2160 := by
    simpa [relyAuthWord, potSlotWord, relyAuthStorageSlot_eq_mapSlot_source I] using rd2160raw
  have rd2163pre := evm_run rd2160 with [
    raw push1 ⟨1⟩ (by native_decide) (by evm_ov),
    raw eq (by native_decide) (by evm_ov)]
  rw [hauth, u256_eq_refl] at rd2163pre
  have rd2166 := rd2163pre.pushConst (⟨2232⟩ : UInt256)
    (width := 2) (op := .PUSH2) (by decide) (by native_decide) (by evm_ov)
  exact ⟨_, _, rd2166.jumpiT (by native_decide) one_ne_zero_uint
    (by jump_dest) (by evm_ov)⟩

set_option maxHeartbeats 1000000 in
theorem potFileVowX_unauthorized {cA σ I} {g : Sat256} {s0 : State} {k C : ℕ}
    {sel data what : UInt256} (hauth : relyAuthWord σ I ≠ ⟨1⟩)
    (h : RD potBytecode I g s0 ⟨2143⟩
      [data, what, ⟨301⟩, sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    RDrev potBytecode g s0 := by
  have hauthSlot :
      UInt256.ofNat (fromByteArrayBigEndian
          (ffi.KEC ((relyAuthHashMem I).readWithPadding 0 64))) =
        mapSlot (relySourceWord I) ⟨0⟩ := by
    simpa [relyAuthHashMem, mapSlot, solcMappingSlot] using
      twoWordHashMem_solcMappingSlot (⟨0⟩ : UInt256) (relySourceWord I)
        solcFreePtrMem_size
  have rd2149pre := evm_run h with [
    raw jumpdest (by native_decide) (by evm_ov),
    raw caller (by native_decide) (by evm_ov),
    raw push1 ⟨0⟩ (by native_decide) (by evm_ov),
    raw swap1 (by native_decide) (by evm_ov),
    raw dup2 (by native_decide) (by evm_ov)]
  have rd2150 := rd2149pre.mstore 0 (wordAt0Mem (relySourceWord I) solcFreePtrMem)
    (UInt256.ofNat 3) (by native_decide) mem_cost (by rfl) (by native_decide) (by evm_ov)
  have rd2154pre := evm_run rd2150 with [
    raw push1 ⟨32⟩ (by native_decide) (by evm_ov),
    raw dup2 (by native_decide) (by evm_ov),
    raw swap1 (by native_decide) (by evm_ov)]
  have rd2155 := rd2154pre.mstore 0 (relyAuthHashMem I)
    (UInt256.ofNat 3) (by native_decide) mem_cost (by rfl) (by native_decide) (by evm_ov)
  have rd2158pre := evm_run rd2155 with [
    raw push1 ⟨64⟩ (by native_decide) (by evm_ov),
    raw swap1 (by native_decide) (by evm_ov)]
  have rd2159 := rd2158pre.keccak256 0 (mapSlot (relySourceWord I) ⟨0⟩)
    (UInt256.ofNat 3) (by native_decide) mem_cost hauthSlot (by native_decide)
    (by evm_ov)
  obtain ⟨k2160, C2160, rd2160raw⟩ := rd2159.sload (by native_decide) (by evm_ov)
  have rd2160 : RD potBytecode I g s0 ⟨2160⟩
      (relyAuthWord σ I :: data :: what :: ⟨301⟩ :: [sel])
      (relyAuthHashMem I) (UInt256.ofNat 3) ByteArray.empty (cA, σ) k2160 C2160 := by
    simpa [relyAuthWord, potSlotWord, relyAuthStorageSlot_eq_mapSlot_source I] using rd2160raw
  have rd2163pre := evm_run rd2160 with [
    raw push1 ⟨1⟩ (by native_decide) (by evm_ov),
    raw eq (by native_decide) (by evm_ov)]
  have heq : UInt256.eq (⟨1⟩ : UInt256) (relyAuthWord σ I) = ⟨0⟩ := by
    exact u256_eq_of_ne (by intro hbad; exact hauth hbad.symm)
  rw [heq] at rd2163pre
  have rd2166 := rd2163pre.pushConst (⟨2232⟩ : UInt256)
    (width := 2) (op := .PUSH2) (by decide) (by native_decide) (by evm_ov)
  have rd2167 := rd2166.jumpiNT (by native_decide) rfl (by evm_ov)
  exact RD.solcErrorStringRevertTail
    (pc := ⟨2167⟩)
    (len := ⟨18⟩)
    (rawWord := ⟨0x141bdd0bdb9bdd0b585d5d1a1bdc9a5e9959⟩)
    (shift := ⟨114⟩)
    (word := ⟨0x506f742f6e6f742d617574686f72697a65640000000000000000000000000000⟩)
    (op := .PUSH18)
    (width := 18)
    rd2167
    (by
      unfold solcErrorStringRevertTailWf
      repeat' first | apply And.intro | native_decide)
    (by decide)
    relyNotAuthorizedWord
    (relyAuthHashMem_size I)
    (relyAuthHashMem_read64 I)
    (by simp only [List.length_cons, List.length_nil]; omega)

set_option maxHeartbeats 1000000 in
theorem potFileVowX_storeAuthorized {cA σ I} {g : Sat256} {s0 : State} {k C : ℕ}
    {sel : UInt256} (hperm : I.perm = true)
    (hmatch : calldataWord I.calldata 4 = ABI.bytesToWord fileVowBytes)
    (h : RD potBytecode I g s0 ⟨2232⟩
      [fileVowDataMaskedWord I, calldataWord I.calldata 4, ⟨301⟩, sel]
      (relyAuthHashMem I) (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    RDret potBytecode g s0
      (cA, sstoreAccountMap I.codeOwner σ ⟨6⟩
        (setAddressOffset0Word (solcSlotWord σ I ⟨6⟩) (fileVowDataMaskedWord I)))
      ByteArray.empty := by
  have rd2233 := h.jumpdest (by native_decide) (by evm_ov)
  have rd2234 := rd2233.dup2 (by native_decide) (by evm_ov)
  have rd2238 := rd2234.pushConst (⟨0x766f77⟩ : UInt256)
    (width := 3) (op := .PUSH3) (by decide) (by native_decide) (by evm_ov)
  have rd2240 := rd2238.push1 ⟨232⟩ (by native_decide) (by evm_ov)
  have rd2241 := rd2240.shl (by native_decide) (by evm_ov)
  have hconst : UInt256.shiftLeft (⟨0x766f77⟩ : UInt256) ⟨232⟩ =
      ABI.bytesToWord fileVowBytes := by native_decide
  rw [hmatch, ← hconst] at rd2241
  have rd2242 := rd2241.eq (by native_decide) (by evm_ov)
  rw [uInt256_eq_self] at rd2242
  have rd2243 := rd2242.iszero (by native_decide) (by evm_ov)
  rw [show UInt256.isZero (⟨1⟩ : UInt256) = ⟨0⟩ from by decide] at rd2243
  have rd2246 := rd2243.pushConst (⟨1249⟩ : UInt256)
    (width := 2) (op := .PUSH2) (by decide) (by native_decide) (by evm_ov)
  have rd2247 := rd2246.jumpiNT (by native_decide)
    (by decide : (⟨0⟩ : UInt256) = ⟨0⟩) (by evm_ov)
  have rd2249 := rd2247.push1 ⟨6⟩ (by native_decide) (by evm_ov)
  have rd2250 := rd2249.dup1 (by native_decide) (by evm_ov)
  obtain ⟨_, _, rd2251⟩ := rd2250.sload (by native_decide) (by evm_ov)
  have rd2253 := rd2251.push1 ⟨1⟩ (by native_decide) (by evm_ov)
  have rd2255 := rd2253.push1 ⟨1⟩ (by native_decide) (by evm_ov)
  have rd2257 := rd2255.push1 ⟨160⟩ (by native_decide) (by evm_ov)
  have rd2258 := rd2257.shl (by native_decide) (by evm_ov)
  have rd2259 := rd2258.sub (by native_decide) (by evm_ov)
  have rd2260 := rd2259.not (by native_decide) (by evm_ov)
  have rd2261 := rd2260.and (by native_decide) (by evm_ov)
  have rd2263 := rd2261.push1 ⟨1⟩ (by native_decide) (by evm_ov)
  have rd2265 := rd2263.push1 ⟨1⟩ (by native_decide) (by evm_ov)
  have rd2267 := rd2265.push1 ⟨160⟩ (by native_decide) (by evm_ov)
  have rd2268 := rd2267.shl (by native_decide) (by evm_ov)
  have rd2269 := rd2268.sub (by native_decide) (by evm_ov)
  have rd2270 := rd2269.dup4 (by native_decide) (by evm_ov)
  have rd2271 := rd2270.and (by native_decide) (by evm_ov)
  have rd2272 := rd2271.lor (by native_decide) (by evm_ov)
  have rd2273 := rd2272.swap1 (by native_decide) (by evm_ov)
  obtain ⟨_, _, rd2274⟩ := rd2273.sstore hperm (by native_decide) (by evm_ov)
  have rd2277 := rd2274.push2 ⟨1326⟩ (by native_decide) (by evm_ov)
  have rd1326 := rd2277.jump (by native_decide) (by jump_dest) (by evm_ov)
  have rd1327 := rd1326.jumpdest (by native_decide) (by evm_ov)
  have rd1328 := rd1327.pop (by native_decide) (by evm_ov)
  have rd1329 := rd1328.pop (by native_decide) (by evm_ov)
  have hword :
      UInt256.lor (UInt256.land (fileVowDataMaskedWord I) solcAddrMask)
          (UInt256.land (UInt256.lnot solcAddrMask) (solcSlotWord σ I ⟨6⟩)) =
        setAddressOffset0Word (solcSlotWord σ I ⟨6⟩) (fileVowDataMaskedWord I) := by
    calc
      UInt256.lor (UInt256.land (fileVowDataMaskedWord I) solcAddrMask)
          (UInt256.land (UInt256.lnot solcAddrMask) (solcSlotWord σ I ⟨6⟩)) =
          UInt256.lor (UInt256.land (fileVowDataMaskedWord I) solcAddrMask)
            (UInt256.land (solcSlotWord σ I ⟨6⟩) (UInt256.lnot solcAddrMask)) := by
            rw [u256_land_comm (UInt256.lnot solcAddrMask) (solcSlotWord σ I ⟨6⟩)]
      _ = UInt256.lor (UInt256.land (solcSlotWord σ I ⟨6⟩) (UInt256.lnot solcAddrMask))
            (UInt256.land (fileVowDataMaskedWord I) solcAddrMask) := by
            exact u256_lor_comm _ _
      _ = setAddressOffset0Word (solcSlotWord σ I ⟨6⟩) (fileVowDataMaskedWord I) := by
            rfl
  have rd301 := rd1329.jump (by native_decide) (by jump_dest) (by evm_ov)
  have rd302 := rd301.jumpdest (by native_decide) (by evm_ov)
  simpa [solcSlotWord, setAddressOffset0Word, hword,
    show UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨160⟩) ⟨1⟩ =
      solcAddrMask from by decide]
    using RD.stop rd302 (by native_decide) (by evm_ov)

set_option maxHeartbeats 1000000 in
theorem potFileVowX_unrecognized {cA σ I} {g : Sat256} {s0 : State} {k C : ℕ}
    {sel : UInt256}
    (hneq : calldataWord I.calldata 4 ≠ ABI.bytesToWord fileVowBytes)
    (h : RD potBytecode I g s0 ⟨2232⟩
      [fileVowDataMaskedWord I, calldataWord I.calldata 4, ⟨301⟩, sel]
      (relyAuthHashMem I) (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    RDrev potBytecode g s0 := by
  have rd2233 := h.jumpdest (by native_decide) (by evm_ov)
  have rd2234 := rd2233.dup2 (by native_decide) (by evm_ov)
  have rd2238 := rd2234.pushConst (⟨0x766f77⟩ : UInt256)
    (width := 3) (op := .PUSH3) (by decide) (by native_decide) (by evm_ov)
  have rd2240 := rd2238.push1 ⟨232⟩ (by native_decide) (by evm_ov)
  have rd2241 := rd2240.shl (by native_decide) (by evm_ov)
  have hconst : UInt256.shiftLeft (⟨0x766f77⟩ : UInt256) ⟨232⟩ =
      ABI.bytesToWord fileVowBytes := by native_decide
  rw [hconst] at rd2241
  have rd2242 := rd2241.eq (by native_decide) (by evm_ov)
  have heq0 : UInt256.eq (ABI.bytesToWord fileVowBytes) (calldataWord I.calldata 4) = ⟨0⟩ :=
    u256_eq_of_ne (fun h => hneq h.symm)
  rw [heq0] at rd2242
  have rd2243 := rd2242.iszero (by native_decide) (by evm_ov)
  rw [show UInt256.isZero (⟨0⟩ : UInt256) = ⟨1⟩ from by decide] at rd2243
  have rd2246 := rd2243.pushConst (⟨1249⟩ : UInt256)
    (width := 2) (op := .PUSH2) (by decide) (by native_decide) (by evm_ov)
  have rd1249 := rd2246.jumpiT (by native_decide) one_ne_zero_uint (by jump_dest)
    (by evm_ov)
  exact RD.potFileUnrecognizedRevert rd1249
    (relyAuthHashMem_size I)
    (relyAuthHashMem_read64 I)
    (by simp only [List.length_cons, List.length_nil]; omega)

theorem potFileVowX_shortarg {cA gh bl σ σ₀ A I} {g : Sat256} {sel : UInt256}
    (hsz4 : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hshort : I.calldata.size < 68)
    (hreach : ∃ k C, RD potBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨637⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    RDrev potBytecode g (initState cA gh bl σ σ₀ g A I) := by
  have hlt :
      UInt256.lt (UInt256.sub (UInt256.ofNat I.calldata.size) ⟨4⟩) ⟨64⟩ = ⟨1⟩ := by
    apply ult_one
    rw [usub_ofNat_word_toNat (by simpa using hsz4) hsize]
    change I.calldata.size - 4 < 64
    omega
  exact RD.solcExternalStaticArgsShortReverts
    (code := potBytecode) (sel := sel) (entry := ⟨637⟩) (ret := ⟨301⟩)
    (decoded := ⟨659⟩) (need := ⟨64⟩) hreach
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) hlt

/-! ### Body core lemmas -/

theorem potFileVowBodyCoreOk
    {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256} {sel : UInt256}
    (hcode : I.code = potBytecode) (hsize : I.calldata.size < UInt256.size)
    (hperm : I.perm = true) (hwv : I.weiValue = ⟨0⟩)
    (hsz68 : 68 ≤ I.calldata.size)
    (hauth : relyAuthWord σ_evm I = ⟨1⟩)
    (hwhat : fileVowWhat I = fileVowBytes)
    (hdispatch : dispatchMsg contract I.calldata = some fileVowTransition)
    (hdecode :
      decodeCalldataWithMode config.abiDecodeMode (fileVowTransition.params.map Param.name)
        (transitionSignature fileVowTransition).paramTypes I.calldata = some (fileVowLocals I))
    (hreach : ∃ k C, RD potBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) ⟨637⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ_evm) k C)
    (hAccounts : accountMapEquiv σ_evm σ_solm) :
    runtimeEquivalenceFor config contract cA gh bl σ_evm σ_solm σ₀ g A I := by
  let data := fileVowDataMaskedWord I
  let locals := fileVowLocals I
  let stored := setAddressOffset0Word (solcSlotWord σ_evm I ⟨6⟩) data
  let evm0 := initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I
  let evm1 := Solm.EVM.storageStore evm0 I.codeOwner ⟨6⟩ stored
  have hauthSolm : relyAuthWord σ_solm I = ⟨1⟩ := by
    have hword : relyAuthWord σ_evm I = relyAuthWord σ_solm I :=
      accountMapEquiv_storage_findD hAccounts I.codeOwner (relyAuthStorageSlot I) ⟨0⟩
    rw [← hword]; exact hauth
  have hvowWord : potSlotWord ⟨6⟩ σ_evm I = potSlotWord ⟨6⟩ σ_solm I :=
    accountMapEquiv_storage_findD hAccounts I.codeOwner ⟨6⟩ ⟨0⟩
  have hstoredSolm :
      stored = setAddressOffset0Word (solcSlotWord σ_solm I ⟨6⟩) data := by
    simpa [stored, potSlotWord] using congrArg (fun old => setAddressOffset0Word old data)
      hvowWord
  have hbody :
      ExecTransitionBody config contract evm0 locals fileVowTransition.body
        (.returned { contract := contract, locals := locals } evm1 none) := by
    simpa [evm0, evm1, locals, stored, data, hstoredSolm, solcSlotWord, initState,
      Solm.EVM.storageLoad] using
      (potFileVowSourceBody (cA := cA) (gh := gh) (bl := bl) (σ := σ_solm)
        (σ₀ := σ₀) (A := A) (I := I) (g := g) hwv hauthSolm hwhat)
  obtain ⟨_, _, hdecoded⟩ := potFileVowX_decoded (g := Sat256.ofUInt256 g) hsz68 hsize hreach
  obtain ⟨_, _, hauthd⟩ := potFileVowX_authorized (I := I) hauth hdecoded
  have hmatch : calldataWord I.calldata 4 = ABI.bytesToWord fileVowBytes :=
    fileVowWhatWord_eq_of_bytes_eq (by omega) hwhat
  have hret := potFileVowX_storeAuthorized hperm hmatch hauthd
  have hret' :
      RDret potBytecode (Sat256.ofUInt256 g)
        (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I)
        (cA, sstoreAccountMap I.codeOwner σ_evm ⟨6⟩ stored) ByteArray.empty := by
    simpa [stored, data] using hret
  exact hret'.reEquivExecutionGenAccountMapEquiv hcode hdispatch hdecode hbody
    (by simp [evm1, evm0, initState, storageStore_createdAccounts])
    (by
      simpa [evm1, evm0, initState, storageStore_accountMap, stored, data, hstoredSolm,
        solcSlotWord, Solm.EVM.storageLoad] using
        accountMapEquiv_sstoreAccountMap I.codeOwner ⟨6⟩ stored hAccounts)
    (by
      simpa [fileVowTransition] using
        (returnEquiv.fallthrough (o := ByteArray.empty) (r := none) (t := [])
          (dvs := []) rfl (by native_decide) (by native_decide)))

theorem potFileVowBodyCoreUnauthorized
    {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256} {sel : UInt256}
    (hcode : I.code = potBytecode) (hsize : I.calldata.size < UInt256.size)
    (hwv : I.weiValue = ⟨0⟩)
    (hsz68 : 68 ≤ I.calldata.size)
    (hauth : relyAuthWord σ_evm I ≠ ⟨1⟩)
    (hdispatch : dispatchMsg contract I.calldata = some fileVowTransition)
    (hdecode :
      decodeCalldataWithMode config.abiDecodeMode (fileVowTransition.params.map Param.name)
        (transitionSignature fileVowTransition).paramTypes I.calldata = some (fileVowLocals I))
    (hreach : ∃ k C, RD potBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) ⟨637⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ_evm) k C)
    (hAccounts : accountMapEquiv σ_evm σ_solm) :
    runtimeEquivalenceFor config contract cA gh bl σ_evm σ_solm σ₀ g A I := by
  let locals := fileVowLocals I
  let evm0 := initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I
  have hauthSolm : relyAuthWord σ_solm I ≠ ⟨1⟩ := by
    have hword : relyAuthWord σ_evm I = relyAuthWord σ_solm I :=
      accountMapEquiv_storage_findD hAccounts I.codeOwner (relyAuthStorageSlot I) ⟨0⟩
    intro hbad; exact hauth (by rw [hword, hbad])
  have hbody :
      ExecTransitionBody config contract evm0 locals fileVowTransition.body .reverted := by
    simpa [evm0, locals] using
      (potFileVowSourceBodyAuthReverts (cA := cA) (gh := gh) (bl := bl) (σ := σ_solm)
        (σ₀ := σ₀) (A := A) (I := I) (g := g) hwv hauthSolm)
  obtain ⟨_, _, hdecoded⟩ := potFileVowX_decoded (g := Sat256.ofUInt256 g) hsz68 hsize hreach
  exact (potFileVowX_unauthorized (I := I) hauth hdecoded)
    |>.reEquivExecutionRevert hcode hdispatch hdecode hbody

theorem potFileVowBodyCoreUnrecognized
    {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256} {sel : UInt256}
    (hcode : I.code = potBytecode) (hsize : I.calldata.size < UInt256.size)
    (hwv : I.weiValue = ⟨0⟩)
    (hsz68 : 68 ≤ I.calldata.size)
    (hauth : relyAuthWord σ_evm I = ⟨1⟩)
    (hwhat : fileVowWhat I ≠ fileVowBytes)
    (hdispatch : dispatchMsg contract I.calldata = some fileVowTransition)
    (hdecode :
      decodeCalldataWithMode config.abiDecodeMode (fileVowTransition.params.map Param.name)
        (transitionSignature fileVowTransition).paramTypes I.calldata = some (fileVowLocals I))
    (hreach : ∃ k C, RD potBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) ⟨637⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ_evm) k C)
    (hAccounts : accountMapEquiv σ_evm σ_solm) :
    runtimeEquivalenceFor config contract cA gh bl σ_evm σ_solm σ₀ g A I := by
  let locals := fileVowLocals I
  let evm0 := initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I
  have hauthSolm : relyAuthWord σ_solm I = ⟨1⟩ := by
    have hword : relyAuthWord σ_evm I = relyAuthWord σ_solm I :=
      accountMapEquiv_storage_findD hAccounts I.codeOwner (relyAuthStorageSlot I) ⟨0⟩
    rw [← hword]; exact hauth
  have hbody :
      ExecTransitionBody config contract evm0 locals fileVowTransition.body .reverted := by
    simpa [evm0, locals] using
      (potFileVowSourceBodyUnrecognized (cA := cA) (gh := gh) (bl := bl) (σ := σ_solm)
        (σ₀ := σ₀) (A := A) (I := I) (g := g) hwv hauthSolm hwhat)
  obtain ⟨_, _, hdecoded⟩ := potFileVowX_decoded (g := Sat256.ofUInt256 g) hsz68 hsize hreach
  obtain ⟨_, _, hauthd⟩ := potFileVowX_authorized (I := I) hauth hdecoded
  have hneq : calldataWord I.calldata 4 ≠ ABI.bytesToWord fileVowBytes :=
    fileVowWhatWord_ne_of_bytes_ne (by omega) hwhat (by native_decide)
  exact (potFileVowX_unrecognized (I := I) hneq hauthd)
    |>.reEquivExecutionRevert hcode hdispatch hdecode hbody

theorem potFileVowBodyCoreDecodeFailed_short
    {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256} {sel : UInt256}
    (hcode : I.code = potBytecode) (hsize : I.calldata.size < UInt256.size)
    (hsz4 : 4 ≤ I.calldata.size) (hshort : I.calldata.size < 68)
    (hdispatch : dispatchMsg contract I.calldata = some fileVowTransition)
    (hreach : ∃ k C, RD potBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) ⟨637⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ_evm) k C) :
    runtimeEquivalenceFor config contract cA gh bl σ_evm σ_solm σ₀ g A I := by
  exact (potFileVowX_shortarg (g := Sat256.ofUInt256 g) hsz4 hsize hshort hreach)
    |>.reEquivDecodingFailed hcode hdispatch (potDecode_fileVow_none_short hsz4 hshort)

/-- `file(bytes32,address)` external (auth): sets `vow` when `what == "vow"`. -/
theorem potFileVowBody {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256}
    (hcode : I.code = potBytecode)
    (hsize : I.calldata.size < UInt256.size)
    (_hperm : I.perm = true)
    (hwv : I.weiValue = ⟨0⟩)
    (hsel : selIs I (potSelBytes 8))
    (hAccounts : accountMapEquiv σ_evm σ_solm) :
    runtimeEquivalenceFor config contract cA gh bl σ_evm σ_solm σ₀ g A I := by
  have hsz4 : 4 ≤ I.calldata.size :=
    calldata_size_ge_of_selIs I (potSelBytes 8) rfl hsel
  have hdispatch : dispatchMsg contract I.calldata = some fileVowTransition :=
    potDispatchFileVow hsel
  have hreach := potReachFileVowBody (cA := cA) (gh := gh) (bl := bl)
    (σ := σ_evm) (σ₀ := σ₀) (A := A) (I := I) (g := Sat256.ofUInt256 g)
    hcode hwv hsz4 hsize hsel
  by_cases hsz68 : 68 ≤ I.calldata.size
  · by_cases hauth : relyAuthWord σ_evm I = ⟨1⟩
    · by_cases hwhat : fileVowWhat I = fileVowBytes
      · exact potFileVowBodyCoreOk hcode hsize _hperm hwv hsz68 hauth hwhat hdispatch
          (potDecode_fileVow_ok hsz68) hreach hAccounts
      · exact potFileVowBodyCoreUnrecognized hcode hsize hwv hsz68 hauth hwhat hdispatch
          (potDecode_fileVow_ok hsz68) hreach hAccounts
    · exact potFileVowBodyCoreUnauthorized hcode hsize hwv hsz68 hauth hdispatch
        (potDecode_fileVow_ok hsz68) hreach hAccounts
  · exact potFileVowBodyCoreDecodeFailed_short hcode hsize hsz4 (by omega)
      hdispatch hreach

end Benchmarks.Dss.Pot
