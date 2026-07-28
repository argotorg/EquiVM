import Benchmarks.Dss.Jug.FileBase

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

set_option maxRecDepth 2000000
set_option maxHeartbeats 0

namespace Benchmarks.Dss.Jug

/-! ## `file(bytes32,address)` -/

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
    "data" (.address (fileVowData I))

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

-- LIBRARY CANDIDATE: legacy solc05 decoding for `(bytes32,address)`.
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

-- LIBRARY CANDIDATE: legacy solc05 short-calldata rejection for `(bytes32,address)`.
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

theorem jugDecode_fileVow_ok {I : ExecutionEnv} (hsz68 : 68 ≤ I.calldata.size) :
    decodeCalldataWithMode config.abiDecodeMode (fileVowTransition.params.map Param.name)
      (transitionSignature fileVowTransition).paramTypes I.calldata =
        some (fileVowLocals I) := by
  simpa [config, fileVowTransition, bytes32, bytes32Width, addr, fileVowLocals,
    fileVowWhat, fileVowData, abiBytes32, abiBytes32Width, abiAddress] using
    (decodeCalldata_legacyBytes32_address_ok (cd := I.calldata) (x := "what")
      (y := "data") hsz68)

theorem jugDecode_fileVow_none_short {I : ExecutionEnv}
    (hsz4 : 4 ≤ I.calldata.size) (hshort : I.calldata.size < 68) :
    decodeCalldataWithMode config.abiDecodeMode (fileVowTransition.params.map Param.name)
      (transitionSignature fileVowTransition).paramTypes I.calldata = none := by
  simpa [config, fileVowTransition, bytes32, bytes32Width, addr, abiBytes32,
    abiBytes32Width, abiAddress] using
    (decodeCalldata_legacyBytes32_address_none_short (cd := I.calldata) (x := "what")
      (y := "data") hsz4 hshort)

theorem fileVowLocals_get_what (I : ExecutionEnv) :
    (fileVowLocals I).get? "what" =
      some (.fixedBytes bytes32Width (fileVowWhat I)) := by
  rw [fileVowLocals, store_get_ne _ _ (by decide), store_get_self]

theorem fileVowLocals_get_data (I : ExecutionEnv) :
    (fileVowLocals I).get? "data" = some (.address (fileVowData I)) := by
  rw [fileVowLocals, store_get_self]

theorem fileVowLocals_get_wards (I : ExecutionEnv) :
    (fileVowLocals I).get? "wards" = none := by
  rw [fileVowLocals, store_get_ne _ _ (by decide), store_get_ne _ _ (by decide)]
  simp

theorem fileVowLocals_get_vow (I : ExecutionEnv) :
    (fileVowLocals I).get? "vow" = none := by
  rw [fileVowLocals, store_get_ne _ _ (by decide), store_get_ne _ _ (by decide)]
  simp

theorem evalExpr_fileVowData {evm : EVM.State} {I : ExecutionEnv} {locals : Store}
    (h : locals.get? "data" = some (.address (fileVowData I))) :
    evalExpr? config { contract := contract, locals := locals } evm (.var "data") =
      .ok (.address (fileVowData I)) := by
  rw [evalExpr?]
  change EvalResult.ofOption EvalError.unboundVariable (locals.get? "data") =
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

theorem assign_fileVowStorage (evm : EVM.State) (I : ExecutionEnv) :
    let evm' := Solm.EVM.storageStore evm evm.executionEnv.codeOwner ⟨3⟩
      (setAddressOffset0Word (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨3⟩)
        (fileVowDataMaskedWord I))
    assignStorageRef? config { contract := contract, locals := fileVowLocals I } evm
      .storage vowRef (.address (fileVowData I)) =
        .ok ({ contract := contract, locals := fileVowLocals I }, evm') := by
  intro evm'
  rw [fileVowData_value_masked I]
  apply assignStorageRef_storage_scalar_value
      (ty := addrSt)
      (er := ({ base := "vow", steps := [] } : EvaledStorageRef))
      (loc := addrLoc ⟨3⟩)
      (hbase := fileVowLocals_get_vow I)
      (her := by simp [vowRef, evalStorageRef, evalStorageRefSteps, EvalResult.bind, pure, bind])
      (hty := by simp [storageTypeAt?, contract, storageDecls, addrSt])
      (hloc := by rfl)
      (hscalar := by trivial)
  simpa [addrLoc, evm'] using
    storageLocStore_address_offset0 evm ⟨3⟩ (fileVowDataMaskedWord I)
      (fileVowDataMaskedWord_canonical I)

theorem jugFileVowSourceBody {cA gh bl σ σ₀ A I} {g : UInt256}
    (hwv : I.weiValue = ⟨0⟩)
    (hauth : relyAuthWord σ I = ⟨1⟩)
    (hwhat : fileVowWhat I = fileVowBytes) :
    let locals := fileVowLocals I
    let evm0 := initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I
    let evm1 := Solm.EVM.storageStore evm0 I.codeOwner ⟨3⟩
      (setAddressOffset0Word (Solm.EVM.storageLoad evm0 I.codeOwner ⟨3⟩)
        (fileVowDataMaskedWord I))
    ExecTransitionBody config contract evm0 locals fileVowTransition.body
      (.returned { contract := contract, locals := locals } evm1 none) := by
  intro locals evm0 evm1
  have hguard :
      evalExpr? config { contract := contract, locals := locals } evm0
        (.binary .eq (.storage (wardsRef sender)) (.intLit 1)) = .ok (.bool true) := by
    exact evalExpr_auth_true_of_wards_none evm0 I locals
      (by simpa [locals] using fileVowLocals_get_wards I)
      (by simp [evm0, initState])
      (by
        simpa [evm0, relyAuthWord, jugSlotWord, initState, Solm.EVM.storageLoad,
          State.lookupAccount] using hauth)
  have hcond :
      evalExpr? config { contract := contract, locals := locals } evm0
        (.binary .eq (.var "what") vowParamLit) = .ok (.bool true) := by
    simpa [vowParamLit, fileVowBytes] using
      (evalExpr_fileVowWhatEq_true (evm := evm0) (I := I) (locals := locals)
        (bs := fileVowBytes) (by simpa [locals] using fileVowLocals_get_what I) hwhat)
  have hdata :
      evalExpr? config { contract := contract, locals := locals } evm0 (.var "data") =
        .ok (.address (fileVowData I)) := by
    exact evalExpr_fileVowData (evm := evm0) (I := I) (locals := locals)
      (by simpa [locals] using fileVowLocals_get_data I)
  have hassign :
      assignStorageRef? config { contract := contract, locals := locals } evm0
        .storage vowRef (.address (fileVowData I)) =
          .ok ({ contract := contract, locals := locals }, evm1) := by
    simpa [locals, evm1, evm0, initState] using assign_fileVowStorage evm0 I
  have hthen :
      ExecBlock config { contract := contract, locals := locals } evm0
        [.assign .storage vowRef (.var "data")]
        (.ok { contract := contract, locals := locals } evm1) := by
    exact ExecBlock.consNormal (ExecStmt.assign hdata hassign) ExecBlock.nil
  have hblock :
      ExecBlock config { contract := contract, locals := locals } evm0 fileVowTransition.body
        (.ok { contract := contract, locals := locals } evm1) := by
    refine ExecBlock.consNormal (ExecStmt.requireTrue ?_) ?_
    · exact evalCallvalueEq_true (by simp [evm0, initState]; exact hwv)
    refine ExecBlock.consNormal (ExecStmt.requireTrue hguard) ?_
    exact ExecBlock.consNormal (ExecStmt.iteTrue hcond hthen) ExecBlock.nil
  simpa [ExecTransitionBody, locals, evm0, evm1] using ExecFuncBody.execBlockOK hblock

theorem jugFileVowSourceBodyAuthReverts {cA gh bl σ σ₀ A I} {g : UInt256}
    (hwv : I.weiValue = ⟨0⟩)
    (hauth : relyAuthWord σ I ≠ ⟨1⟩) :
    let locals := fileVowLocals I
    let evm0 := initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I
    ExecTransitionBody config contract evm0 locals fileVowTransition.body .reverted := by
  intro locals evm0
  have hguard :
      evalExpr? config { contract := contract, locals := locals } evm0
        (.binary .eq (.storage (wardsRef sender)) (.intLit 1)) = .ok (.bool false) := by
    exact evalExpr_auth_false_of_wards_none evm0 I locals
      (by simpa [locals] using fileVowLocals_get_wards I)
      (by simp [evm0, initState])
      (by
        simpa [evm0, relyAuthWord, jugSlotWord, initState, Solm.EVM.storageLoad,
          State.lookupAccount] using hauth)
  refine ExecFuncBody.execBlockRevert ?_
  simpa [fileVowTransition, nonpayable, auth] using
    nonpayableSecondRequireReverts
      (cfg := config)
      (solm := { contract := contract, locals := locals })
      (evm := evm0)
      (guard := .binary .eq (.storage (wardsRef sender)) (.intLit 1))
      (rest := [.ite (.binary .eq (.var "what") vowParamLit)
        [.assign .storage vowRef (.var "data")] [.require (.boolLit false)]])
      (by simp [evm0, initState]; exact hwv)
      hguard

theorem jugFileVowSourceBodyUnrecognized {cA gh bl σ σ₀ A I} {g : UInt256}
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
    exact evalExpr_auth_true_of_wards_none evm0 I locals
      (by simpa [locals] using fileVowLocals_get_wards I)
      (by simp [evm0, initState])
      (by
        simpa [evm0, relyAuthWord, jugSlotWord, initState, Solm.EVM.storageLoad,
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
        [.require (.boolLit false)] .reverted := by
    exact ExecBlock.consRevert (ExecStmt.requireFalse hreqFalse)
  have hblock :
      ExecBlock config { contract := contract, locals := locals } evm0 fileVowTransition.body
        .reverted := by
    refine ExecBlock.consNormal (ExecStmt.requireTrue ?_) ?_
    · exact evalCallvalueEq_true (by simp [evm0, initState]; exact hwv)
    refine ExecBlock.consNormal (ExecStmt.requireTrue hguard) ?_
    exact ExecBlock.consRevert (ExecStmt.iteFalse hcond helse)
  simpa [ExecTransitionBody, locals, evm0] using ExecFuncBody.execBlockRevert hblock

theorem jugReachFileVowBody {cA gh bl σ σ₀ A I} {g : Sat256}
    (hcode : I.code = jugBytecode) (hwv : I.weiValue = ⟨0⟩)
    (hsz : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hsel : selIs I (jugSelBytes 5)) :
    ∃ k C, RD jugBytecode I g (initState cA gh bl σ σ₀ g A I)
        ⟨505⟩ [jugSelWord I] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty
        (cA, σ) k C := by
  have hword : jugSelWord I = ⟨0xd4e8be83⟩ :=
    jugSelWord_eq_of_beq I hsz 0xd4 0xe8 0xbe 0x83 ⟨0xd4e8be83⟩
      (by native_decide) (by simpa [jugSelBytes] using hsel)
  have hroot : UInt256.gt (armSelNat jugBytecode jugRootSplitPc) (jugSelWord I) = ⟨0⟩ := by
    rw [hword]
    native_decide
  have heq0 : ∀ j, j < 4 →
      UInt256.eq (armSelNat jugBytecode (nthArmPc jugBytecode jugHighFirstArmPc j))
        (jugSelWord I) = ⟨0⟩ := by
    intro j hj
    interval_cases j <;> rw [hword] <;> native_decide
  have htake :
      UInt256.eq (armSelNat jugBytecode (nthArmPc jugBytecode jugHighFirstArmPc 4))
        (jugSelWord I) ≠ ⟨0⟩ := by
    rw [hword]
    native_decide
  exact jugReachHighBody 4 (by omega) ⟨505⟩ hcode hwv hsz hsize hroot heq0 htake
    (by jump_dest) (by native_decide)

theorem RD.jugFileVowDecodeToRoutine {code : ByteArray} {g : Sat256} {s0 : State}
    {ee : ExecutionEnv} {k C : ℕ} {ret de sel : UInt256} {R : List UInt256}
    {mem rdata : ByteArray} {aw : UInt256}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    (h : RD code ee g s0 ⟨527⟩ (de :: ⟨4⟩ :: ret :: sel :: R) mem aw rdata acc k C)
    (hwf : code = jugBytecode)
    (hroutine : (D_J code 0).contains ⟨1971⟩ = true)
    (hov : R.length + 13 ≤ 1024) :
    ∃ k' C', RD code ee g s0 ⟨1971⟩
      (UInt256.land solcAddrMask (calldataWord ee.calldata 36) ::
        calldataWord ee.calldata 4 :: ret :: sel :: R)
      mem aw rdata acc k' C' := by
  subst hwf
  have rd528 := h.jumpdest (by native_decide) (by evm_ov)
  have rd529 := rd528.pop (by native_decide) (by evm_ov)
  have rd530 := rd529.dup1 (by native_decide) (by evm_ov)
  have rd531 := rd530.calldataload (by native_decide) (by evm_ov)
  have rd532 := rd531.swap1 (by native_decide) (by evm_ov)
  have rd534 := rd532.push1 ⟨32⟩ (by native_decide) (by evm_ov)
  have rd535 := rd534.add (by native_decide) (by evm_ov)
  have rd536 := rd535.calldataload (by native_decide) (by evm_ov)
  have rd538 := rd536.push1 ⟨1⟩ (by native_decide) (by evm_ov)
  have rd540 := rd538.push1 ⟨1⟩ (by native_decide) (by evm_ov)
  have rd542 := rd540.push1 ⟨160⟩ (by native_decide) (by evm_ov)
  have rd543 := rd542.shl (by native_decide) (by evm_ov)
  have rd544 := rd543.sub (by native_decide) (by evm_ov)
  have rd545 := rd544.and (by native_decide) (by evm_ov)
  have rd548 := rd545.push2 ⟨1971⟩ (by native_decide) (by evm_ov)
  exact ⟨_, _, by
    simpa [calldataWord, show (⟨4⟩ : UInt256).toNat = 4 from by decide,
      show (⟨36⟩ : UInt256).toNat = 36 from by decide,
      show UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨160⟩) ⟨1⟩ =
        solcAddrMask from by decide]
      using rd548.jump (by native_decide) hroutine (by evm_ov)⟩

theorem jugFileVowX_decoded {cA gh bl σ σ₀ A I} {g : Sat256} {sel : UInt256}
    (hsz68 : 68 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hreach : ∃ k C, RD jugBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨505⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    ∃ k C, RD jugBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨1971⟩
        [fileVowDataMaskedWord I, calldataWord I.calldata 4, ⟨226⟩, sel]
        solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
  obtain ⟨_, _, hdecoded⟩ := RD.solcExternalStaticArgsLenOk
    (code := jugBytecode) (sel := sel) (entry := ⟨505⟩) (ret := ⟨226⟩)
    (decoded := ⟨527⟩) (need := ⟨64⟩) hreach
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by jump_dest)
    (by
      exact solcDecodeLenCheckOkUnsigned (by simpa using hsz68) hsize)
  obtain ⟨_, _, hroutine⟩ := RD.jugFileVowDecodeToRoutine
    (code := jugBytecode) (ret := ⟨226⟩) (sel := sel) (R := [])
    hdecoded rfl (by jump_dest) (by simp)
  exact ⟨_, _, by simpa [fileVowDataMaskedWord, fileVowDataWord] using hroutine⟩

set_option maxHeartbeats 1000000 in
theorem jugFileVowX_authorized {cA σ I} {g : Sat256} {s0 : State} {k C : ℕ}
    {sel : UInt256} (hauth : relyAuthWord σ I = ⟨1⟩)
    (h : RD jugBytecode I g s0 ⟨1971⟩
      [fileVowDataMaskedWord I, calldataWord I.calldata 4, ⟨226⟩, sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    ∃ k' C', RD jugBytecode I g s0 ⟨2060⟩
      [fileVowDataMaskedWord I, calldataWord I.calldata 4, ⟨226⟩, sel]
      (relyAuthHashMem I) (UInt256.ofNat 3) ByteArray.empty (cA, σ) k' C' := by
  have hauthSlot :
      UInt256.ofNat (fromByteArrayBigEndian
          (ffi.KEC ((relyAuthHashMem I).readWithPadding 0 64))) =
        mapSlot (relySourceWord I) ⟨0⟩ := by
    simpa [relyAuthHashMem, mapSlot, solcMappingSlot] using
      twoWordHashMem_solcMappingSlot (⟨0⟩ : UInt256) (relySourceWord I)
        solcFreePtrMem_size
  have rd1977pre := evm_run h with [
    raw jumpdest (by native_decide) (by evm_ov),
    raw caller (by native_decide) (by evm_ov),
    raw push1 ⟨0⟩ (by native_decide) (by evm_ov),
    raw swap1 (by native_decide) (by evm_ov),
    raw dup2 (by native_decide) (by evm_ov)]
  have rd1978 := rd1977pre.mstore 0 (wordAt0Mem (relySourceWord I) solcFreePtrMem)
    (UInt256.ofNat 3) (by native_decide) mem_cost (by rfl) (by native_decide) (by evm_ov)
  have rd1982pre := evm_run rd1978 with [
    raw push1 ⟨32⟩ (by native_decide) (by evm_ov),
    raw dup2 (by native_decide) (by evm_ov),
    raw swap1 (by native_decide) (by evm_ov)]
  have rd1983 := rd1982pre.mstore 0 (relyAuthHashMem I)
    (UInt256.ofNat 3) (by native_decide) mem_cost (by rfl) (by native_decide) (by evm_ov)
  have rd1986pre := evm_run rd1983 with [
    raw push1 ⟨64⟩ (by native_decide) (by evm_ov),
    raw swap1 (by native_decide) (by evm_ov)]
  have rd1987 := rd1986pre.keccak256 0 (mapSlot (relySourceWord I) ⟨0⟩)
    (UInt256.ofNat 3) (by native_decide) mem_cost hauthSlot (by native_decide)
    (by evm_ov)
  obtain ⟨k1988, C1988, rd1988raw⟩ := rd1987.sload (by native_decide) (by evm_ov)
  have rd1988 : RD jugBytecode I g s0 ⟨1988⟩
      (relyAuthWord σ I :: fileVowDataMaskedWord I :: calldataWord I.calldata 4 ::
        ⟨226⟩ :: [sel])
      (relyAuthHashMem I) (UInt256.ofNat 3) ByteArray.empty (cA, σ) k1988 C1988 := by
    simpa [relyAuthWord, jugSlotWord, relyAuthStorageSlot_eq_mapSlot_source I] using rd1988raw
  have rd1991pre := evm_run rd1988 with [
    raw push1 ⟨1⟩ (by native_decide) (by evm_ov),
    raw eq (by native_decide) (by evm_ov)]
  rw [hauth, u256_eq_refl] at rd1991pre
  have rd1994 := rd1991pre.pushConst (⟨2060⟩ : UInt256)
    (width := 2) (op := .PUSH2) (by decide) (by native_decide) (by evm_ov)
  exact ⟨_, _, rd1994.jumpiT (by native_decide) one_ne_zero_uint
    (by jump_dest) (by evm_ov)⟩

set_option maxHeartbeats 1000000 in
theorem jugFileVowX_unauthorized {cA σ I} {g : Sat256} {s0 : State} {k C : ℕ}
    {sel : UInt256} (hauth : relyAuthWord σ I ≠ ⟨1⟩)
    (h : RD jugBytecode I g s0 ⟨1971⟩
      [fileVowDataMaskedWord I, calldataWord I.calldata 4, ⟨226⟩, sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    RDrev jugBytecode g s0 := by
  have hauthSlot :
      UInt256.ofNat (fromByteArrayBigEndian
          (ffi.KEC ((relyAuthHashMem I).readWithPadding 0 64))) =
        mapSlot (relySourceWord I) ⟨0⟩ := by
    simpa [relyAuthHashMem, mapSlot, solcMappingSlot] using
      twoWordHashMem_solcMappingSlot (⟨0⟩ : UInt256) (relySourceWord I)
        solcFreePtrMem_size
  have rd1977pre := evm_run h with [
    raw jumpdest (by native_decide) (by evm_ov),
    raw caller (by native_decide) (by evm_ov),
    raw push1 ⟨0⟩ (by native_decide) (by evm_ov),
    raw swap1 (by native_decide) (by evm_ov),
    raw dup2 (by native_decide) (by evm_ov)]
  have rd1978 := rd1977pre.mstore 0 (wordAt0Mem (relySourceWord I) solcFreePtrMem)
    (UInt256.ofNat 3) (by native_decide) mem_cost (by rfl) (by native_decide) (by evm_ov)
  have rd1982pre := evm_run rd1978 with [
    raw push1 ⟨32⟩ (by native_decide) (by evm_ov),
    raw dup2 (by native_decide) (by evm_ov),
    raw swap1 (by native_decide) (by evm_ov)]
  have rd1983 := rd1982pre.mstore 0 (relyAuthHashMem I)
    (UInt256.ofNat 3) (by native_decide) mem_cost (by rfl) (by native_decide) (by evm_ov)
  have rd1986pre := evm_run rd1983 with [
    raw push1 ⟨64⟩ (by native_decide) (by evm_ov),
    raw swap1 (by native_decide) (by evm_ov)]
  have rd1987 := rd1986pre.keccak256 0 (mapSlot (relySourceWord I) ⟨0⟩)
    (UInt256.ofNat 3) (by native_decide) mem_cost hauthSlot (by native_decide)
    (by evm_ov)
  obtain ⟨k1988, C1988, rd1988raw⟩ := rd1987.sload (by native_decide) (by evm_ov)
  have rd1988 : RD jugBytecode I g s0 ⟨1988⟩
      (relyAuthWord σ I :: fileVowDataMaskedWord I :: calldataWord I.calldata 4 ::
        ⟨226⟩ :: [sel])
      (relyAuthHashMem I) (UInt256.ofNat 3) ByteArray.empty (cA, σ) k1988 C1988 := by
    simpa [relyAuthWord, jugSlotWord, relyAuthStorageSlot_eq_mapSlot_source I] using rd1988raw
  have rd1991pre := evm_run rd1988 with [
    raw push1 ⟨1⟩ (by native_decide) (by evm_ov),
    raw eq (by native_decide) (by evm_ov)]
  have heq : UInt256.eq (⟨1⟩ : UInt256) (relyAuthWord σ I) = ⟨0⟩ := by
    exact u256_eq_of_ne (by intro hbad; exact hauth hbad.symm)
  rw [heq] at rd1991pre
  have rd1994 := rd1991pre.pushConst (⟨2060⟩ : UInt256)
    (width := 2) (op := .PUSH2) (by decide) (by native_decide) (by evm_ov)
  have rd1995 := rd1994.jumpiNT (by native_decide) rfl (by evm_ov)
  exact RD.solcErrorStringRevertTail
    (pc := ⟨1995⟩)
    (len := ⟨18⟩)
    (rawWord := ⟨0x129d59cbdb9bdd0b585d5d1a1bdc9a5e9959⟩)
    (shift := ⟨114⟩)
    (word := ⟨0x4a75672f6e6f742d617574686f72697a65640000000000000000000000000000⟩)
    (op := .PUSH18)
    (width := 18)
    rd1995
    (by
      unfold solcErrorStringRevertTailWf
      repeat' first | apply And.intro | native_decide)
    (by decide)
    relyNotAuthorizedWord
    (relyAuthHashMem_size I)
    (relyAuthHashMem_read64 I)
    (by simp only [List.length_cons, List.length_nil]; omega)

theorem jugFileVowX_storeAuthorized {cA σ I} {g : Sat256} {s0 : State} {k C : ℕ}
    {sel : UInt256} (hperm : I.perm = true)
    (hmatch : calldataWord I.calldata 4 = ABI.bytesToWord fileVowBytes)
    (h : RD jugBytecode I g s0 ⟨2060⟩
      [fileVowDataMaskedWord I, calldataWord I.calldata 4, ⟨226⟩, sel]
      (relyAuthHashMem I) (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    RDret jugBytecode g s0
      (cA, sstoreAccountMap I.codeOwner σ ⟨3⟩
        (setAddressOffset0Word (solcSlotWord σ I ⟨3⟩) (fileVowDataMaskedWord I)))
      ByteArray.empty := by
  have rd2061 := h.jumpdest (by native_decide) (by evm_ov)
  have rd2062 := rd2061.dup2 (by native_decide) (by evm_ov)
  have rd2066 := rd2062.pushConst (⟨0x766f77⟩ : UInt256)
    (width := 3) (op := .PUSH3) (by decide) (by native_decide) (by evm_ov)
  have rd2068 := rd2066.push1 ⟨232⟩ (by native_decide) (by evm_ov)
  have rd2069 := rd2068.shl (by native_decide) (by evm_ov)
  have hconst : UInt256.shiftLeft (⟨0x766f77⟩ : UInt256) ⟨232⟩ =
      ABI.bytesToWord fileVowBytes := by
    native_decide
  rw [hmatch, ← hconst] at rd2069
  have rd2070 := rd2069.eq (by native_decide) (by evm_ov)
  rw [uInt256_eq_self] at rd2070
  have rd2071 := rd2070.iszero (by native_decide) (by evm_ov)
  rw [show UInt256.isZero (⟨1⟩ : UInt256) = ⟨0⟩ from by decide] at rd2071
  have rd2074 := rd2071.pushConst (⟨821⟩ : UInt256)
    (width := 2) (op := .PUSH2) (by decide) (by native_decide) (by evm_ov)
  have rd2075 := rd2074.jumpiNT (by native_decide)
    (by decide : (⟨0⟩ : UInt256) = ⟨0⟩) (by evm_ov)
  have rd2077 := rd2075.push1 ⟨3⟩ (by native_decide) (by evm_ov)
  have rd2078 := rd2077.dup1 (by native_decide) (by evm_ov)
  obtain ⟨_, _, rd2079⟩ := rd2078.sload (by native_decide) (by evm_ov)
  have rd2081 := rd2079.push1 ⟨1⟩ (by native_decide) (by evm_ov)
  have rd2083 := rd2081.push1 ⟨1⟩ (by native_decide) (by evm_ov)
  have rd2085 := rd2083.push1 ⟨160⟩ (by native_decide) (by evm_ov)
  have rd2086 := rd2085.shl (by native_decide) (by evm_ov)
  have rd2087 := rd2086.sub (by native_decide) (by evm_ov)
  have rd2088 := rd2087.not (by native_decide) (by evm_ov)
  have rd2089 := rd2088.and (by native_decide) (by evm_ov)
  have rd2091 := rd2089.push1 ⟨1⟩ (by native_decide) (by evm_ov)
  have rd2093 := rd2091.push1 ⟨1⟩ (by native_decide) (by evm_ov)
  have rd2095 := rd2093.push1 ⟨160⟩ (by native_decide) (by evm_ov)
  have rd2096 := rd2095.shl (by native_decide) (by evm_ov)
  have rd2097 := rd2096.sub (by native_decide) (by evm_ov)
  have rd2098 := rd2097.dup4 (by native_decide) (by evm_ov)
  have rd2099 := rd2098.and (by native_decide) (by evm_ov)
  have rd2100 := rd2099.lor (by native_decide) (by evm_ov)
  have rd2101 := rd2100.swap1 (by native_decide) (by evm_ov)
  obtain ⟨_, _, rd2102⟩ := rd2101.sstore hperm (by native_decide) (by evm_ov)
  have rd2105 := rd2102.push2 ⟨1013⟩ (by native_decide) (by evm_ov)
  have rd1013 := rd2105.jump (by native_decide) (by jump_dest) (by evm_ov)
  have rd1014 := rd1013.jumpdest (by native_decide) (by evm_ov)
  have rd1015 := rd1014.pop (by native_decide) (by evm_ov)
  have rd1016 := rd1015.pop (by native_decide) (by evm_ov)
  have hword :
      UInt256.lor (UInt256.land (fileVowDataMaskedWord I) solcAddrMask)
          (UInt256.land (UInt256.lnot solcAddrMask) (solcSlotWord σ I ⟨3⟩)) =
        setAddressOffset0Word (solcSlotWord σ I ⟨3⟩) (fileVowDataMaskedWord I) := by
    calc
      UInt256.lor (UInt256.land (fileVowDataMaskedWord I) solcAddrMask)
          (UInt256.land (UInt256.lnot solcAddrMask) (solcSlotWord σ I ⟨3⟩)) =
          UInt256.lor (UInt256.land (fileVowDataMaskedWord I) solcAddrMask)
            (UInt256.land (solcSlotWord σ I ⟨3⟩) (UInt256.lnot solcAddrMask)) := by
            rw [u256_land_comm (UInt256.lnot solcAddrMask) (solcSlotWord σ I ⟨3⟩)]
      _ = UInt256.lor (UInt256.land (solcSlotWord σ I ⟨3⟩) (UInt256.lnot solcAddrMask))
            (UInt256.land (fileVowDataMaskedWord I) solcAddrMask) := by
            exact u256_lor_comm _ _
      _ = setAddressOffset0Word (solcSlotWord σ I ⟨3⟩) (fileVowDataMaskedWord I) := by
            rfl
  have rd226 := rd1016.jump (by native_decide) (by jump_dest) (by evm_ov)
  have rd227 := rd226.jumpdest (by native_decide) (by evm_ov)
  simpa [solcSlotWord, setAddressOffset0Word, hword,
    show UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨160⟩) ⟨1⟩ =
      solcAddrMask from by decide]
    using RD.stop rd227 (by native_decide) (by evm_ov)

theorem jugFileVowX_unrecognized {cA σ I} {g : Sat256} {s0 : State} {k C : ℕ}
    {sel : UInt256}
    (hneq : calldataWord I.calldata 4 ≠ ABI.bytesToWord fileVowBytes)
    (h : RD jugBytecode I g s0 ⟨2060⟩
      [fileVowDataMaskedWord I, calldataWord I.calldata 4, ⟨226⟩, sel]
      (relyAuthHashMem I) (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    RDrev jugBytecode g s0 := by
  have rd2061 := h.jumpdest (by native_decide) (by evm_ov)
  have rd2062 := rd2061.dup2 (by native_decide) (by evm_ov)
  have rd2066 := rd2062.pushConst (⟨0x766f77⟩ : UInt256)
    (width := 3) (op := .PUSH3) (by decide) (by native_decide) (by evm_ov)
  have rd2068 := rd2066.push1 ⟨232⟩ (by native_decide) (by evm_ov)
  have rd2069 := rd2068.shl (by native_decide) (by evm_ov)
  have hconst : UInt256.shiftLeft (⟨0x766f77⟩ : UInt256) ⟨232⟩ =
      ABI.bytesToWord fileVowBytes := by
    native_decide
  rw [hconst] at rd2069
  have rd2070 := rd2069.eq (by native_decide) (by evm_ov)
  have heq0 : UInt256.eq (ABI.bytesToWord fileVowBytes) (calldataWord I.calldata 4) = ⟨0⟩ := by
    exact u256_eq_of_ne (fun h => hneq h.symm)
  rw [heq0] at rd2070
  have rd2071 := rd2070.iszero (by native_decide) (by evm_ov)
  rw [show UInt256.isZero (⟨0⟩ : UInt256) = ⟨1⟩ from by decide] at rd2071
  have rd2074 := rd2071.pushConst (⟨821⟩ : UInt256)
    (width := 2) (op := .PUSH2) (by decide) (by native_decide) (by evm_ov)
  have rd821 := rd2074.jumpiT (by native_decide) one_ne_zero_uint (by jump_dest)
    (by evm_ov)
  exact RD.jugFileUnrecognizedRevert rd821
    (relyAuthHashMem_size I)
    (relyAuthHashMem_read64 I)
    (by simp only [List.length_cons, List.length_nil]; omega)

theorem jugFileVowX_shortarg {cA gh bl σ σ₀ A I} {g : Sat256} {sel : UInt256}
    (hsz4 : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hshort : I.calldata.size < 68)
    (hreach : ∃ k C, RD jugBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨505⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    RDrev jugBytecode g (initState cA gh bl σ σ₀ g A I) := by
  have hlt :
      UInt256.lt (UInt256.sub (UInt256.ofNat I.calldata.size) ⟨4⟩) ⟨64⟩ = ⟨1⟩ := by
    apply ult_one
    rw [usub_ofNat_word_toNat (by simpa using hsz4) hsize]
    change I.calldata.size - 4 < 64
    omega
  exact RD.solcExternalStaticArgsShortReverts
    (code := jugBytecode) (sel := sel) (entry := ⟨505⟩) (ret := ⟨226⟩)
    (decoded := ⟨527⟩) (need := ⟨64⟩) hreach
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) hlt

theorem jugFileVowBodyCoreOk
    {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256} {sel : UInt256}
    (hcode : I.code = jugBytecode) (hsize : I.calldata.size < UInt256.size)
    (hperm : I.perm = true) (hwv : I.weiValue = ⟨0⟩)
    (hsz68 : 68 ≤ I.calldata.size)
    (hauth : relyAuthWord σ_evm I = ⟨1⟩)
    (hwhat : fileVowWhat I = fileVowBytes)
    (hdispatch : dispatchMsg contract I.calldata = some fileVowTransition)
    (hdecode :
      decodeCalldataWithMode config.abiDecodeMode (fileVowTransition.params.map Param.name)
        (transitionSignature fileVowTransition).paramTypes I.calldata = some (fileVowLocals I))
    (hreach : ∃ k C, RD jugBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) ⟨505⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ_evm) k C)
    (hAccounts : accountMapEquiv σ_evm σ_solm) :
    runtimeEquivalenceFor config contract cA gh bl σ_evm σ_solm σ₀ g A I := by
  let data := fileVowDataMaskedWord I
  let locals := fileVowLocals I
  let stored := setAddressOffset0Word (solcSlotWord σ_evm I ⟨3⟩) data
  let evm0 := initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I
  let evm1 := Solm.EVM.storageStore evm0 I.codeOwner ⟨3⟩ stored
  have hauthSolm : relyAuthWord σ_solm I = ⟨1⟩ := by
    have hword : relyAuthWord σ_evm I = relyAuthWord σ_solm I :=
      accountMapEquiv_storage_findD hAccounts I.codeOwner (relyAuthStorageSlot I) ⟨0⟩
    rw [← hword]
    exact hauth
  have hvowWord : jugSlotWord ⟨3⟩ σ_evm I = jugSlotWord ⟨3⟩ σ_solm I :=
    accountMapEquiv_storage_findD hAccounts I.codeOwner ⟨3⟩ ⟨0⟩
  have hstoredSolm :
      stored = setAddressOffset0Word (solcSlotWord σ_solm I ⟨3⟩) data := by
    simpa [stored, jugSlotWord] using congrArg (fun old => setAddressOffset0Word old data)
      hvowWord
  have hbody :
      ExecTransitionBody config contract evm0 locals fileVowTransition.body
        (.returned { contract := contract, locals := locals } evm1 none) := by
    simpa [evm0, evm1, locals, stored, data, hstoredSolm, solcSlotWord, initState,
      Solm.EVM.storageLoad] using
      (jugFileVowSourceBody (cA := cA) (gh := gh) (bl := bl) (σ := σ_solm)
        (σ₀ := σ₀) (A := A) (I := I) (g := g) hwv hauthSolm hwhat)
  obtain ⟨_, _, hdecoded⟩ := jugFileVowX_decoded (g := Sat256.ofUInt256 g)
    hsz68 hsize hreach
  obtain ⟨_, _, hswitch⟩ := jugFileVowX_authorized (I := I) hauth hdecoded
  have hmatch : calldataWord I.calldata 4 = ABI.bytesToWord fileVowBytes :=
    fileVowWhatWord_eq_of_bytes_eq (by omega) hwhat
  have hret := jugFileVowX_storeAuthorized hperm hmatch hswitch
  have hret' :
      RDret jugBytecode (Sat256.ofUInt256 g)
        (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I)
        (cA, sstoreAccountMap I.codeOwner σ_evm ⟨3⟩ stored) ByteArray.empty := by
    simpa [stored, data] using hret
  exact hret'.reEquivExecutionGenAccountMapEquiv hcode hdispatch hdecode hbody
    (by simp [evm1, evm0, initState, storageStore_createdAccounts])
    (by
      simpa [evm1, evm0, initState, storageStore_accountMap, stored, data, hstoredSolm,
        solcSlotWord, Solm.EVM.storageLoad] using
        accountMapEquiv_sstoreAccountMap I.codeOwner ⟨3⟩ stored hAccounts)
    (by
      simpa [fileVowTransition] using
        (returnEquiv.fallthrough (o := ByteArray.empty) (r := none) (t := [])
          (dvs := []) rfl (by native_decide) (by native_decide)))

theorem jugFileVowBodyCoreUnauthorized
    {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256} {sel : UInt256}
    (hcode : I.code = jugBytecode) (hsize : I.calldata.size < UInt256.size)
    (hwv : I.weiValue = ⟨0⟩)
    (hsz68 : 68 ≤ I.calldata.size)
    (hauth : relyAuthWord σ_evm I ≠ ⟨1⟩)
    (hdispatch : dispatchMsg contract I.calldata = some fileVowTransition)
    (hdecode :
      decodeCalldataWithMode config.abiDecodeMode (fileVowTransition.params.map Param.name)
        (transitionSignature fileVowTransition).paramTypes I.calldata = some (fileVowLocals I))
    (hreach : ∃ k C, RD jugBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) ⟨505⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ_evm) k C)
    (hAccounts : accountMapEquiv σ_evm σ_solm) :
    runtimeEquivalenceFor config contract cA gh bl σ_evm σ_solm σ₀ g A I := by
  let locals := fileVowLocals I
  let evm0 := initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I
  have hauthSolm : relyAuthWord σ_solm I ≠ ⟨1⟩ := by
    have hword : relyAuthWord σ_evm I = relyAuthWord σ_solm I :=
      accountMapEquiv_storage_findD hAccounts I.codeOwner (relyAuthStorageSlot I) ⟨0⟩
    intro hbad
    exact hauth (by rw [hword, hbad])
  have hbody :
      ExecTransitionBody config contract evm0 locals fileVowTransition.body .reverted := by
    simpa [evm0, locals] using
      (jugFileVowSourceBodyAuthReverts (cA := cA) (gh := gh) (bl := bl) (σ := σ_solm)
        (σ₀ := σ₀) (A := A) (I := I) (g := g) hwv hauthSolm)
  obtain ⟨_, _, hdecoded⟩ := jugFileVowX_decoded (g := Sat256.ofUInt256 g)
    hsz68 hsize hreach
  exact (jugFileVowX_unauthorized (I := I) hauth hdecoded)
    |>.reEquivExecutionRevert hcode hdispatch hdecode hbody

theorem jugFileVowBodyCoreUnrecognized
    {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256} {sel : UInt256}
    (hcode : I.code = jugBytecode) (hsize : I.calldata.size < UInt256.size)
    (hwv : I.weiValue = ⟨0⟩)
    (hsz68 : 68 ≤ I.calldata.size)
    (hauth : relyAuthWord σ_evm I = ⟨1⟩)
    (hwhat : fileVowWhat I ≠ fileVowBytes)
    (hdispatch : dispatchMsg contract I.calldata = some fileVowTransition)
    (hdecode :
      decodeCalldataWithMode config.abiDecodeMode (fileVowTransition.params.map Param.name)
        (transitionSignature fileVowTransition).paramTypes I.calldata = some (fileVowLocals I))
    (hreach : ∃ k C, RD jugBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) ⟨505⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ_evm) k C)
    (hAccounts : accountMapEquiv σ_evm σ_solm) :
    runtimeEquivalenceFor config contract cA gh bl σ_evm σ_solm σ₀ g A I := by
  let locals := fileVowLocals I
  let evm0 := initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I
  have hauthSolm : relyAuthWord σ_solm I = ⟨1⟩ := by
    have hword : relyAuthWord σ_evm I = relyAuthWord σ_solm I :=
      accountMapEquiv_storage_findD hAccounts I.codeOwner (relyAuthStorageSlot I) ⟨0⟩
    rw [← hword]
    exact hauth
  have hbody :
      ExecTransitionBody config contract evm0 locals fileVowTransition.body .reverted := by
    simpa [evm0, locals] using
      (jugFileVowSourceBodyUnrecognized (cA := cA) (gh := gh) (bl := bl) (σ := σ_solm)
        (σ₀ := σ₀) (A := A) (I := I) (g := g) hwv hauthSolm hwhat)
  obtain ⟨_, _, hdecoded⟩ := jugFileVowX_decoded (g := Sat256.ofUInt256 g)
    hsz68 hsize hreach
  obtain ⟨_, _, hswitch⟩ := jugFileVowX_authorized (I := I) hauth hdecoded
  have hneq : calldataWord I.calldata 4 ≠ ABI.bytesToWord fileVowBytes :=
    fileVowWhatWord_ne_of_bytes_ne (by omega) hwhat (by native_decide)
  exact (jugFileVowX_unrecognized hneq hswitch)
    |>.reEquivExecutionRevert hcode hdispatch hdecode hbody

theorem jugFileVowBodyCoreDecodeFailed_short
    {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256} {sel : UInt256}
    (hcode : I.code = jugBytecode) (hsize : I.calldata.size < UInt256.size)
    (hsz4 : 4 ≤ I.calldata.size) (hshort : I.calldata.size < 68)
    (hdispatch : dispatchMsg contract I.calldata = some fileVowTransition)
    (hreach : ∃ k C, RD jugBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) ⟨505⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ_evm) k C) :
    runtimeEquivalenceFor config contract cA gh bl σ_evm σ_solm σ₀ g A I := by
  exact (jugFileVowX_shortarg (g := Sat256.ofUInt256 g) hsz4 hsize hshort hreach)
    |>.reEquivDecodingFailed hcode hdispatch (jugDecode_fileVow_none_short hsz4 hshort)

theorem jugFileVowBody {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256}
    (hcode : I.code = jugBytecode)
    (hsize : I.calldata.size < UInt256.size)
    (hperm : I.perm = true)
    (hwv : I.weiValue = ⟨0⟩)
    (hsel : selIs I (jugSelBytes 5))
    (hAccounts : accountMapEquiv σ_evm σ_solm) :
    runtimeEquivalenceFor config contract cA gh bl σ_evm σ_solm σ₀ g A I := by
  have hsz4 : 4 ≤ I.calldata.size :=
    calldata_size_ge_of_selIs I (jugSelBytes 5) rfl hsel
  have hdispatch : dispatchMsg contract I.calldata = some fileVowTransition :=
    jugDispatchFileVow hsel
  have hreach := jugReachFileVowBody (cA := cA) (gh := gh) (bl := bl)
    (σ := σ_evm) (σ₀ := σ₀) (A := A) (I := I) (g := Sat256.ofUInt256 g)
    hcode hwv hsz4 hsize hsel
  by_cases hsz68 : 68 ≤ I.calldata.size
  · by_cases hauth : relyAuthWord σ_evm I = ⟨1⟩
    · by_cases hwhat : fileVowWhat I = fileVowBytes
      · exact jugFileVowBodyCoreOk hcode hsize hperm hwv hsz68 hauth hwhat hdispatch
          (jugDecode_fileVow_ok hsz68) hreach hAccounts
      · exact jugFileVowBodyCoreUnrecognized hcode hsize hwv hsz68 hauth hwhat hdispatch
          (jugDecode_fileVow_ok hsz68) hreach hAccounts
    · exact jugFileVowBodyCoreUnauthorized hcode hsize hwv hsz68 hauth hdispatch
        (jugDecode_fileVow_ok hsz68) hreach hAccounts
  · exact jugFileVowBodyCoreDecodeFailed_short hcode hsize hsz4 (by omega)
      hdispatch hreach

end Benchmarks.Dss.Jug
