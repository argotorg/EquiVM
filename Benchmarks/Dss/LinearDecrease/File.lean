import Benchmarks.Dss.LinearDecrease.Rely

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

set_option maxRecDepth 2000000
set_option maxHeartbeats 0

namespace Benchmarks.Dss.LinearDecrease

/-! ## `file(bytes32,uint256)` -/

abbrev fileWhat (I : ExecutionEnv) : List UInt8 :=
  (I.calldata.toList.drop 4).take 32

abbrev fileData (I : ExecutionEnv) : UInt256 :=
  calldataWord I.calldata 36

abbrev fileTauBytes : List UInt8 :=
  [116, 97, 117, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
   0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]

abbrev fileLocals (I : ExecutionEnv) : Store :=
  ((∅ : Store).insert "what" (.fixedBytes bytes32Width (fileWhat I))).insert
    "data" (.int (Int.ofNat (fileData I).toNat))

theorem fileWhat_length {I : ExecutionEnv} (hsz36 : 36 ≤ I.calldata.size) :
    (fileWhat I).length = 32 := by
  simp [fileWhat, List.length_take, List.length_drop, byteArray_toList_eq]
  omega

theorem fileTauBytes_length : fileTauBytes.length = 32 := by
  decide +native

theorem fileTauBytes_word :
    ABI.bytesToWord fileTauBytes =
      UInt256.shiftLeft (⟨0x746175⟩ : UInt256) ⟨232⟩ := by
  decide +native

theorem fileWhatWord_eq {I : ExecutionEnv} (hsz36 : 36 ≤ I.calldata.size) :
    ABI.bytesToWord (fileWhat I) = calldataWord I.calldata 4 := by
  simpa [fileWhat] using decode_word_at_eq I.calldata 4 (by omega) (by norm_num)

theorem fileWhat_eq_of_word_eq {I : ExecutionEnv} {bs : List UInt8}
    (hsz36 : 36 ≤ I.calldata.size) (hword : calldataWord I.calldata 4 = ABI.bytesToWord bs)
    (hbsLen : bs.length = 32) :
    fileWhat I = bs := by
  have hto := toBytesBE_bytesToWord_of_length (bs := fileWhat I)
    (fileWhat_length (I := I) hsz36)
  rw [fileWhatWord_eq (I := I) hsz36, hword] at hto
  exact hto.symm.trans (toBytesBE_bytesToWord_of_length (bs := bs) hbsLen)

theorem fileWhatWord_ne_of_bytes_ne {I : ExecutionEnv} {bs : List UInt8}
    (hsz36 : 36 ≤ I.calldata.size) (hneq : fileWhat I ≠ bs)
    (hbsLen : bs.length = 32) :
    calldataWord I.calldata 4 ≠ ABI.bytesToWord bs := by
  intro hword
  exact hneq (fileWhat_eq_of_word_eq hsz36 hword hbsLen)

-- LIBRARY CANDIDATE: legacy solc05 decoding for `(bytes32,uint256)`.
theorem stairstepDecodeABIValues_bytes32_uint256_legacy_ok {bytes : List UInt8}
    (hlen0 : (bytes.take 32).length = 32)
    (hlen32 : ((bytes.drop 32).take 32).length = 32) :
    decodeABIValues? [abiBytes32, abiUInt256] bytes 0 0 64 64 DecodeMode.legacySolc05 =
      some ([.fixedBytes abiBytes32Width (bytes.take 32),
        .int (Int.ofNat (ABI.bytesToWord ((bytes.drop 32).take 32)).toNat)], 64) := by
  simp [decodeABIValues?, abiBytes32, abiBytes32Width, abiUInt256, isDynamicABIType,
    staticABIEncodedSize?, decodeABIValue?, readBytes?, hlen0]
  simp [readWord?, readBytes?, decodeABIWord?, hlen32]
  rw [Int.emod_eq_of_lt]
  · simp [UInt256.toNat]
  · exact Int.natCast_nonneg _
  · exact_mod_cast (ABI.bytesToWord ((bytes.drop 32).take 32)).val.isLt

-- LIBRARY CANDIDATE: legacy solc05 short-calldata rejection for `(bytes32,uint256)`.
theorem stairstepDecodeABIValues_bytes32_uint256_legacy_none_short {bytes : List UInt8}
    (hshort : bytes.length < 64) :
    decodeABIValues? [abiBytes32, abiUInt256] bytes 0 0 64 64 DecodeMode.legacySolc05 =
      none := by
  simp only [decodeABIValues?, abiBytes32, abiBytes32Width, abiUInt256, isDynamicABIType,
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

theorem stairstepDecodeCalldata_legacyBytes32_uint256_ok {cd : ByteArray}
    {x y : Solm.Ident} (hsz68 : 68 ≤ cd.size) :
    decodeCalldataWithMode DecodeMode.legacySolc05 [x, y] [abiBytes32, abiUInt256] cd =
      some (((∅ : Solm.Store).insert x
        (.fixedBytes abiBytes32Width ((cd.toList.drop 4).take 32))).insert y
        (.int (Int.ofNat (calldataWord cd 36).toNat))) := by
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
  rw [if_neg (by simp [abiBytes32, abiUInt256, isDynamicABIType])]
  simp only [decodeCalldata.decodeArgs]
  rw [show abiTupleHeadSize? [abiBytes32, abiUInt256] = some 64 by decide +native]
  simp only [bind, Option.bind]
  rw [stairstepDecodeABIValues_bytes32_uint256_legacy_ok (bytes := cd.toList.drop 4)
    (by simpa using htake4)
    (by simpa [List.drop_drop, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using htake36)]
  rw [if_neg (by rw [List.length_drop, htlen]; omega :
    ¬ (cd.toList.drop 4).length < 64)]
  simp [decodeCalldata.insertValues]
  rw [hword36]

theorem stairstepDecodeCalldata_legacyBytes32_uint256_none_short {cd : ByteArray}
    {x y : Solm.Ident} (hsz4 : 4 ≤ cd.size) (hshort : cd.size < 68) :
    decodeCalldataWithMode DecodeMode.legacySolc05 [x, y] [abiBytes32, abiUInt256] cd =
      none := by
  have htlen : cd.toList.length = cd.size := by
    rw [byteArray_toList_eq, Array.length_toList]
    rfl
  unfold decodeCalldataWithMode decodeCalldata
  rw [if_neg (by rw [htlen]; omega : ¬ cd.toList.length < 4)]
  rw [if_neg (by simp [abiBytes32, abiUInt256, isDynamicABIType])]
  simp only [decodeCalldata.decodeArgs]
  rw [show abiTupleHeadSize? [abiBytes32, abiUInt256] = some 64 by decide +native]
  simp only [bind, Option.bind]
  by_cases hbytes : (cd.toList.drop 4).length < 64
  · rw [if_pos hbytes]
  · rw [if_neg hbytes]
    rw [stairstepDecodeABIValues_bytes32_uint256_legacy_none_short
      (bytes := cd.toList.drop 4) (by
        rw [List.length_drop, htlen]
        omega)]

theorem stairstepDecode_file_ok {I : ExecutionEnv} (hsz68 : 68 ≤ I.calldata.size) :
    decodeCalldataWithMode config.abiDecodeMode (fileTransition.params.map Param.name)
      (transitionSignature fileTransition).paramTypes I.calldata =
        some (fileLocals I) := by
  simpa [config, fileTransition, bytes32, bytes32Width, uint256, uint256Int,
    fileLocals, fileWhat, fileData, abiBytes32, abiBytes32Width, abiUInt256] using
    (stairstepDecodeCalldata_legacyBytes32_uint256_ok (cd := I.calldata) (x := "what")
      (y := "data") hsz68)

theorem stairstepDecode_file_none_short {I : ExecutionEnv}
    (hsz4 : 4 ≤ I.calldata.size) (hshort : I.calldata.size < 68) :
    decodeCalldataWithMode config.abiDecodeMode (fileTransition.params.map Param.name)
      (transitionSignature fileTransition).paramTypes I.calldata = none := by
  simpa [config, fileTransition, bytes32, bytes32Width, uint256, uint256Int, abiBytes32,
    abiBytes32Width, abiUInt256] using
    (stairstepDecodeCalldata_legacyBytes32_uint256_none_short (cd := I.calldata)
      (x := "what") (y := "data") hsz4 hshort)

theorem fileLocals_get_what (I : ExecutionEnv) :
    (fileLocals I).get? "what" =
      some (.fixedBytes bytes32Width (fileWhat I)) := by
  rw [fileLocals, store_get_ne _ _ (by decide), store_get_self]

theorem fileLocals_get_data (I : ExecutionEnv) :
    (fileLocals I).get? "data" =
      some (.int (Int.ofNat (fileData I).toNat)) := by
  rw [fileLocals, store_get_self]

theorem fileLocals_get_wards (I : ExecutionEnv) :
    (fileLocals I).get? "wards" = none := by
  rw [fileLocals, store_get_ne _ _ (by decide), store_get_ne _ _ (by decide)]
  simp

theorem fileLocals_get_tau (I : ExecutionEnv) :
    (fileLocals I).get? "tau" = none := by
  rw [fileLocals, store_get_ne _ _ (by decide), store_get_ne _ _ (by decide)]
  simp

theorem evalExpr_fileData {evm : EVM.State} {I : ExecutionEnv} {locals : Store}
    (h : locals.get? "data" = some (.int (Int.ofNat (fileData I).toNat))) :
    evalExpr? config { contract := contract, locals := locals } evm (.var "data") =
      .ok (.int (Int.ofNat (fileData I).toNat)) := by
  rw [evalExpr?]
  change EvalResult.ofOption EvalError.unboundVariable (locals.get? "data") =
    .ok (.int (Int.ofNat (fileData I).toNat))
  rw [h]
  rfl

theorem evalExpr_fileWhatEq_true {evm : EVM.State} {I : ExecutionEnv} {locals : Store}
    {bs : List UInt8}
    (hget : locals.get? "what" = some (.fixedBytes bytes32Width (fileWhat I)))
    (hwhat : fileWhat I = bs) :
    evalExpr? config { contract := contract, locals := locals } evm
      (.binary .eq (.var "what") (.fixedBytesLit bytes32Width bs)) = .ok (.bool true) := by
  have hvar :
      evalExpr? config { contract := contract, locals := locals } evm (.var "what") =
        .ok (.fixedBytes bytes32Width (fileWhat I)) := by
    rw [evalExpr?]
    change EvalResult.ofOption EvalError.unboundVariable (locals.get? "what") =
      .ok (.fixedBytes bytes32Width (fileWhat I))
    rw [hget]
    rfl
  rw [evalExpr?]
  simp only [hvar, EvalResult.bind, bind]
  simp [evalExpr?, evalBinaryOp?, hwhat]
  all_goals decide

theorem evalExpr_fileWhatEq_false {evm : EVM.State} {I : ExecutionEnv} {locals : Store}
    {bs : List UInt8}
    (hget : locals.get? "what" = some (.fixedBytes bytes32Width (fileWhat I)))
    (hwhat : fileWhat I ≠ bs) :
    evalExpr? config { contract := contract, locals := locals } evm
      (.binary .eq (.var "what") (.fixedBytesLit bytes32Width bs)) = .ok (.bool false) := by
  have hvar :
      evalExpr? config { contract := contract, locals := locals } evm (.var "what") =
        .ok (.fixedBytes bytes32Width (fileWhat I)) := by
    rw [evalExpr?]
    change EvalResult.ofOption EvalError.unboundVariable (locals.get? "what") =
      .ok (.fixedBytes bytes32Width (fileWhat I))
    rw [hget]
    rfl
  rw [evalExpr?]
  simp only [hvar, EvalResult.bind, bind]
  simp [evalExpr?, evalBinaryOp?, hwhat]
  all_goals decide

theorem evalStorageRef_file_auth (evm : EVM.State) (I : ExecutionEnv)
    (hsrc : evm.executionEnv.source = I.source) :
    evalStorageRef config { contract := contract, locals := fileLocals I } evm
      (wardsRef sender) = .ok (relyAuthEvaledRef I) := by
  simp [evalStorageRef, evalStorageRefStep, wardsRef, sender, envValue, relyAuthEvaledRef,
    relyAuthKey, hsrc, valueToKey?, EvalResult.bind, EvalResult.ofOption, bind, pure,
    evalExpr?]

theorem evalExpr_file_auth_true (evm : EVM.State) (I : ExecutionEnv)
    (hsrc : evm.executionEnv.source = I.source)
    (hload :
      Solm.EVM.storageLoad evm evm.executionEnv.codeOwner (relyAuthStorageSlot I) = ⟨1⟩) :
    evalExpr? config { contract := contract, locals := fileLocals I } evm
      (.binary .eq (.storage (wardsRef sender)) (.intLit 1)) = .ok (.bool true) := by
  have hstorage :
      evalExpr? config { contract := contract, locals := fileLocals I } evm
        (.storage (wardsRef sender)) = .ok (.int 1) := by
    rw [evalExpr_storage_scalar_value
      (cfg := config)
      (solm := { contract := contract, locals := fileLocals I })
      (slot := wardsRef sender)
      (er := relyAuthEvaledRef I)
      (t := .int uint256Int)
      (loc := wordLoc (relyAuthStorageSlot I))
      (value := .int 1)
      (hbase := by simp [fileLocals, wardsRef])
      (her := evalStorageRef_file_auth evm I hsrc)
      (hty := by simp [storageTypeAt?, storageTypeStep?, contract, storageDecls, uint256St])
      (hloc := by rfl)
      (hload := by
        simpa [hload] using stairstepStorageLocLoad_uint256 evm (relyAuthStorageSlot I))]
  simp only [evalExpr?, hstorage, EvalResult.bind, bind, pure]
  rfl

theorem evalExpr_file_auth_false (evm : EVM.State) (I : ExecutionEnv)
    (hsrc : evm.executionEnv.source = I.source)
    (hload :
      Solm.EVM.storageLoad evm evm.executionEnv.codeOwner (relyAuthStorageSlot I) ≠ ⟨1⟩) :
    evalExpr? config { contract := contract, locals := fileLocals I } evm
      (.binary .eq (.storage (wardsRef sender)) (.intLit 1)) = .ok (.bool false) := by
  have hstorage :
      evalExpr? config { contract := contract, locals := fileLocals I } evm
        (.storage (wardsRef sender)) =
          .ok (.int (Int.ofNat
            (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner
              (relyAuthStorageSlot I)).toNat)) := by
    exact evalExpr_storage_scalar_value
      (cfg := config)
      (solm := { contract := contract, locals := fileLocals I })
      (slot := wardsRef sender)
      (er := relyAuthEvaledRef I)
      (t := .int uint256Int)
      (loc := wordLoc (relyAuthStorageSlot I))
      (hbase := by simp [fileLocals, wardsRef])
      (her := evalStorageRef_file_auth evm I hsrc)
      (hty := by simp [storageTypeAt?, storageTypeStep?, contract, storageDecls, uint256St])
      (hloc := by rfl)
      (hload := by exact stairstepStorageLocLoad_uint256 evm (relyAuthStorageSlot I))
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

def fileTauPostState (evm : EVM.State) (I : ExecutionEnv) : EVM.State :=
  Solm.EVM.storageStore evm evm.executionEnv.codeOwner ⟨1⟩ (fileData I)

theorem assign_fileTauStorage (evm : EVM.State) (I : ExecutionEnv) :
    assignStorageRef? config { contract := contract, locals := fileLocals I } evm
      .storage tauRef (.int (Int.ofNat (fileData I).toNat)) =
        .ok ({ contract := contract, locals := fileLocals I }, fileTauPostState evm I) := by
  apply assignStorageRef_storage_scalar
      (ty := uint256St)
      (er := ({ base := "tau", steps := [] } : EvaledStorageRef))
      (loc := wordLoc ⟨1⟩)
      (hbase := fileLocals_get_tau I)
      (her := by simp [tauRef, evalStorageRef, evalStorageRefSteps, EvalResult.bind, pure, bind])
      (hty := by simp [storageTypeAt?, contract, storageDecls, uint256St])
      (hloc := by rfl)
  simpa [fileTauPostState] using stairstepStorageLocStore_uint256 evm ⟨1⟩ (fileData I)

theorem stairstepFileSourceBodyTauOk {cA gh bl σ σ₀ A I} {g : UInt256}
    (hwv : I.weiValue = ⟨0⟩)
    (hauth : relyAuthWord σ I = ⟨1⟩)
    (hwhat : fileWhat I = fileTauBytes) :
    let locals := fileLocals I
    let evm0 := initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I
    let evm1 := fileTauPostState evm0 I
    ExecTransitionBody config contract evm0 locals fileTransition.body
      (.returned { contract := contract, locals := locals } evm1 none) := by
  intro locals evm0 evm1
  have hguard :
      evalExpr? config { contract := contract, locals := locals } evm0
        (.binary .eq (.storage (wardsRef sender)) (.intLit 1)) = .ok (.bool true) := by
    simpa [locals, evm0, relyAuthWord, stairstepSlotWord, initState, Solm.EVM.storageLoad,
      State.lookupAccount] using
      evalExpr_file_auth_true evm0 I (by simp [evm0, initState]) hauth
  have hcond :
      evalExpr? config { contract := contract, locals := locals } evm0
        (.binary .eq (.var "what") tauParamLit) = .ok (.bool true) := by
    simpa [tauParamLit, fileTauBytes, zeroPad29, locals] using
      (evalExpr_fileWhatEq_true (evm := evm0) (I := I) (locals := locals)
        (bs := fileTauBytes) (by simpa [locals] using fileLocals_get_what I) hwhat)
  have hdata :
      evalExpr? config { contract := contract, locals := locals } evm0 (.var "data") =
        .ok (.int (Int.ofNat (fileData I).toNat)) := by
    simpa [locals] using
      evalExpr_fileData (evm := evm0) (I := I) (locals := locals)
        (by simpa [locals] using fileLocals_get_data I)
  have hassign :
      assignStorageRef? config { contract := contract, locals := locals } evm0
        .storage tauRef (.int (Int.ofNat (fileData I).toNat)) =
          .ok ({ contract := contract, locals := locals }, evm1) := by
    simpa [locals, evm1] using assign_fileTauStorage evm0 I
  have hthen :
      ExecBlock config { contract := contract, locals := locals } evm0
        [.assign .storage tauRef (.var "data")]
        (.ok { contract := contract, locals := locals } evm1) := by
    exact ExecBlock.consNormal (ExecStmt.assign hdata hassign) ExecBlock.nil
  have hblock :
      ExecBlock config { contract := contract, locals := locals } evm0 fileTransition.body
        (.ok { contract := contract, locals := locals } evm1) := by
    refine ExecBlock.consNormal (ExecStmt.requireTrue ?_) ?_
    · exact evalCallvalueEq_true (by simp [evm0, initState]; exact hwv)
    refine ExecBlock.consNormal (ExecStmt.requireTrue hguard) ?_
    exact ExecBlock.consNormal (ExecStmt.iteTrue hcond hthen) ExecBlock.nil
  simpa [ExecTransitionBody, locals, evm0, evm1] using ExecFuncBody.execBlockOK hblock

theorem stairstepFileSourceBodyAuthReverts {cA gh bl σ σ₀ A I} {g : UInt256}
    (hwv : I.weiValue = ⟨0⟩)
    (hauth : relyAuthWord σ I ≠ ⟨1⟩) :
    let locals := fileLocals I
    let evm0 := initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I
    ExecTransitionBody config contract evm0 locals fileTransition.body .reverted := by
  intro locals evm0
  have hguard :
      evalExpr? config { contract := contract, locals := locals } evm0
        (.binary .eq (.storage (wardsRef sender)) (.intLit 1)) = .ok (.bool false) := by
    simpa [locals, evm0, relyAuthWord, stairstepSlotWord, initState, Solm.EVM.storageLoad,
      State.lookupAccount] using
      evalExpr_file_auth_false evm0 I (by simp [evm0, initState]) hauth
  refine ExecFuncBody.execBlockRevert ?_
  simpa [fileTransition, nonpayable, auth] using
    nonpayableSecondRequireReverts
      (cfg := config)
      (solm := { contract := contract, locals := locals })
      (evm := evm0)
      (guard := .binary .eq (.storage (wardsRef sender)) (.intLit 1))
      (rest := ([
        Stmt.ite (.binary .eq (.var "what") tauParamLit)
          [Stmt.assign .storage tauRef (.var "data")]
          [Stmt.require (.boolLit false)]
      ] : List Stmt))
      (by simp [evm0, initState]; exact hwv)
      hguard

theorem stairstepFileSourceBodyUnrecognizedReverts {cA gh bl σ σ₀ A I} {g : UInt256}
    (hwv : I.weiValue = ⟨0⟩)
    (hauth : relyAuthWord σ I = ⟨1⟩)
    (hnotTau : fileWhat I ≠ fileTauBytes) :
    let locals := fileLocals I
    let evm0 := initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I
    ExecTransitionBody config contract evm0 locals fileTransition.body .reverted := by
  intro locals evm0
  have hguard :
      evalExpr? config { contract := contract, locals := locals } evm0
        (.binary .eq (.storage (wardsRef sender)) (.intLit 1)) = .ok (.bool true) := by
    simpa [locals, evm0, relyAuthWord, stairstepSlotWord, initState, Solm.EVM.storageLoad,
      State.lookupAccount] using
      evalExpr_file_auth_true evm0 I (by simp [evm0, initState]) hauth
  have htau :
      evalExpr? config { contract := contract, locals := locals } evm0
        (.binary .eq (.var "what") tauParamLit) = .ok (.bool false) := by
    simpa [tauParamLit, fileTauBytes, zeroPad29, locals] using
      (evalExpr_fileWhatEq_false (evm := evm0) (I := I) (locals := locals)
        (bs := fileTauBytes) (by simpa [locals] using fileLocals_get_what I) hnotTau)
  have hreqFalse :
      evalExpr? config { contract := contract, locals := locals } evm0 (.boolLit false) =
        .ok (.bool false) := by
    simp [evalExpr?, pure]
  have hunrec :
      ExecBlock config { contract := contract, locals := locals } evm0
        [.require (.boolLit false)] .reverted := by
    exact ExecBlock.consRevert (ExecStmt.requireFalse hreqFalse)
  have hblock :
      ExecBlock config { contract := contract, locals := locals } evm0 fileTransition.body
        .reverted := by
    refine ExecBlock.consNormal (ExecStmt.requireTrue ?_) ?_
    · exact evalCallvalueEq_true (by simp [evm0, initState]; exact hwv)
    refine ExecBlock.consNormal (ExecStmt.requireTrue hguard) ?_
    exact ExecBlock.consRevert (ExecStmt.iteFalse htau hunrec)
  simpa [ExecTransitionBody, locals, evm0] using ExecFuncBody.execBlockRevert hblock

/-! ## EVM/refinement assembly -/

noncomputable def fileLogDataMem (I : ExecutionEnv) : ByteArray :=
  (UInt256.toByteArray (fileData I)).write 0 (relyAuthHashMem I) 128 32

theorem fileLogDataMem_size (I : ExecutionEnv) :
    (fileLogDataMem I).size = 160 := by
  unfold fileLogDataMem
  exact toByteArray_write32_size_of_ge (relyAuthHashMem I) (fileData I) 128 96 160
    (relyAuthHashMem_size I) (by omega)
    (by simpa using lt_usize 32 (by norm_num))
    (by omega)

theorem fileLogDataMem_read64 (I : ExecutionEnv) :
    (fileLogDataMem I).readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩ := by
  unfold fileLogDataMem
  rw [toByteArray_write_read_below_of_gap (fileData I) (relyAuthHashMem I) 128 64
    (by rw [relyAuthHashMem_size I]) (by omega)
    (by rw [relyAuthHashMem_size I]; exact lt_usize _ (by norm_num))]
  exact relyAuthHashMem_read64 I

theorem stairstepReachFileBody {cA gh bl σ σ₀ A I} {g : Sat256}
    (hcode : I.code = linearDecreaseBytecode) (hwv : I.weiValue = ⟨0⟩)
    (hsz : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hsel : selIs I (stairstepSelBytes 1)) :
    ∃ k C, RD linearDecreaseBytecode I g
        (initState cA gh bl σ σ₀ g A I)
        stairstepFileEntryPc [stairstepSelWord I] solcFreePtrMem (UInt256.ofNat 3)
        ByteArray.empty (cA, σ) k C := by
  have hword : stairstepSelWord I = ⟨0x29ae8114⟩ :=
    stairstepSelWord_eq_of_beq I hsz 0x29 0xae 0x81 0x14 ⟨0x29ae8114⟩
      (by decide +native) (by simpa [stairstepSelBytes] using hsel)
  have heq0 : ∀ j, j < 0 →
      UInt256.eq
        (armSelNat linearDecreaseBytecode
          (nthArmPc linearDecreaseBytecode stairstepFirstArmPc j))
        (stairstepSelWord I) = ⟨0⟩ := by
    intro j hj
    omega
  have htake :
      UInt256.eq
        (armSelNat linearDecreaseBytecode
          (nthArmPc linearDecreaseBytecode stairstepFirstArmPc 0))
        (stairstepSelWord I) ≠ ⟨0⟩ := by
    rw [hword]
    decide +native
  exact stairstepReachBody 0 (by omega) stairstepFileEntryPc hcode hwv hsz hsize
    heq0 htake (by jump_dest) (by decide +native)

theorem RD.stairstepFileDecodeToRoutine {cA σ I} {g : Sat256} {s0 : State}
    {k C : ℕ} {sel de : UInt256}
    (h : RD linearDecreaseBytecode I g s0 ⟨125⟩
      (de :: ⟨4⟩ :: ⟨138⟩ :: [sel])
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    ∃ k' C', RD linearDecreaseBytecode I g s0 ⟨315⟩
      [fileData I, calldataWord I.calldata 4, ⟨138⟩, sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k' C' := by
  have rd350 := evm_run h with [
    raw jumpdest (by decide +native) (by evm_ov),
    raw pop (by decide +native) (by evm_ov),
    raw dup1 (by decide +native) (by evm_ov),
    raw calldataload (by decide +native) (by evm_ov),
    raw swap1 (by decide +native) (by evm_ov),
    raw push1 ⟨32⟩ (by decide +native) (by evm_ov),
    raw add (by decide +native) (by evm_ov),
    raw calldataload (by decide +native) (by evm_ov),
    raw push2 ⟨315⟩ (by decide +native) (by evm_ov),
    raw jump (by decide +native) (by jump_dest) (by evm_ov)]
  exact ⟨_, _, by simpa [fileData, calldataWord] using rd350⟩

theorem stairstepFileX_decoded {cA gh bl σ σ₀ A I} {g : Sat256} {sel : UInt256}
    (hsz68 : 68 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hreach : ∃ k C, RD linearDecreaseBytecode I g
      (initState cA gh bl σ σ₀ g A I) stairstepFileEntryPc [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    ∃ k C, RD linearDecreaseBytecode I g
        (initState cA gh bl σ σ₀ g A I) ⟨315⟩
        [fileData I, calldataWord I.calldata 4, ⟨138⟩, sel]
        solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
  obtain ⟨_, _, hdecoded⟩ := RD.solcTwoAddressExternalLenOk
    (code := linearDecreaseBytecode) (sel := sel)
    (entry := stairstepFileEntryPc) (ret := ⟨138⟩) (decoded := ⟨125⟩) hreach
    (by decide +native) (by decide +native) (by decide +native) (by decide +native)
    (by decide +native) (by decide +native) (by decide +native) (by decide +native)
    (by decide +native) (by decide +native) (by decide +native) (by decide +native)
    (by jump_dest) hsz68 hsize
  exact RD.stairstepFileDecodeToRoutine hdecoded

theorem stairstepFileX_shortarg {cA gh bl σ σ₀ A I} {g : Sat256} {sel : UInt256}
    (hsz4 : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hshort : I.calldata.size < 68)
    (hreach : ∃ k C, RD linearDecreaseBytecode I g
      (initState cA gh bl σ σ₀ g A I) stairstepFileEntryPc [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    RDrev linearDecreaseBytecode g (initState cA gh bl σ σ₀ g A I) := by
  have hlt :
      UInt256.lt (UInt256.sub (UInt256.ofNat I.calldata.size) ⟨4⟩) ⟨64⟩ = ⟨1⟩ := by
    apply ult_one
    rw [usub_ofNat_word_toNat (by simpa using hsz4) hsize]
    change I.calldata.size - 4 < 64
    omega
  exact RD.solcExternalStaticArgsShortReverts
    (code := linearDecreaseBytecode) (sel := sel)
    (entry := stairstepFileEntryPc) (ret := ⟨138⟩) (decoded := ⟨125⟩)
    (need := ⟨64⟩) hreach
    (by decide +native) (by decide +native) (by decide +native) (by decide +native)
    (by decide +native) (by decide +native) (by decide +native) (by decide +native)
    (by decide +native) (by decide +native) (by decide +native) (by decide +native)
    (by decide +native) (by decide +native) (by decide +native) hlt

set_option maxHeartbeats 1000000 in
theorem stairstepFileX_authorized {cA σ I} {g : Sat256} {s0 : State} {k C : ℕ}
    {sel : UInt256} (hauth : relyAuthWord σ I = ⟨1⟩)
    (h : RD linearDecreaseBytecode I g s0 ⟨315⟩
      [fileData I, calldataWord I.calldata 4, ⟨138⟩, sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    ∃ k' C', RD linearDecreaseBytecode I g s0 ⟨415⟩
      [fileData I, calldataWord I.calldata 4, ⟨138⟩, sel]
      (relyAuthHashMem I) (UInt256.ofNat 3) ByteArray.empty (cA, σ) k' C' := by
  have hauthSlot :
      UInt256.ofNat (fromByteArrayBigEndian
          (ffi.KEC ((relyAuthHashMem I).readWithPadding 0 64))) =
        mapSlot (relySourceWord I) ⟨0⟩ := by
    simpa [relyAuthHashMem, mapSlot, solcMappingSlot] using
      twoWordHashMem_solcMappingSlot (⟨0⟩ : UInt256) (relySourceWord I)
        solcFreePtrMem_size
  have rd356pre := evm_run h with [
    raw jumpdest (by decide +native) (by evm_ov),
    raw caller (by decide +native) (by evm_ov),
    raw push1 ⟨0⟩ (by decide +native) (by evm_ov),
    raw swap1 (by decide +native) (by evm_ov),
    raw dup2 (by decide +native) (by evm_ov)]
  have rd357 := rd356pre.mstore 0 (wordAt0Mem (relySourceWord I) solcFreePtrMem)
    (UInt256.ofNat 3) (by decide +native) mem_cost (by rfl) (by decide +native)
    (by evm_ov)
  have rd361pre := evm_run rd357 with [
    raw push1 ⟨32⟩ (by decide +native) (by evm_ov),
    raw dup2 (by decide +native) (by evm_ov),
    raw swap1 (by decide +native) (by evm_ov)]
  have rd362 := rd361pre.mstore 0 (relyAuthHashMem I)
    (UInt256.ofNat 3) (by decide +native) mem_cost (by rfl) (by decide +native)
    (by evm_ov)
  have rd365pre := evm_run rd362 with [
    raw push1 ⟨64⟩ (by decide +native) (by evm_ov),
    raw swap1 (by decide +native) (by evm_ov)]
  have rd366 := rd365pre.keccak256 0 (mapSlot (relySourceWord I) ⟨0⟩)
    (UInt256.ofNat 3) (by decide +native) mem_cost hauthSlot (by decide +native)
    (by evm_ov)
  obtain ⟨k367, C367, rd367raw⟩ := rd366.sload (by decide +native) (by evm_ov)
  have rd367 : RD linearDecreaseBytecode I g s0 ⟨332⟩
      (relyAuthWord σ I :: fileData I :: calldataWord I.calldata 4 :: ⟨138⟩ :: [sel])
      (relyAuthHashMem I) (UInt256.ofNat 3) ByteArray.empty (cA, σ) k367 C367 := by
    simpa [relyAuthWord, stairstepSlotWord, relyAuthStorageSlot_eq_mapSlot_source I]
      using rd367raw
  have rd370pre := evm_run rd367 with [
    raw push1 ⟨1⟩ (by decide +native) (by evm_ov),
    raw eq (by decide +native) (by evm_ov)]
  rw [hauth, u256_eq_refl] at rd370pre
  have rd373 := rd370pre.pushConst (⟨415⟩ : UInt256)
    (width := 2) (op := .PUSH2) (by decide) (by decide +native) (by evm_ov)
  exact ⟨_, _, rd373.jumpiT (by decide +native) one_ne_zero_uint
    (by jump_dest) (by evm_ov)⟩

set_option maxHeartbeats 1000000 in
theorem stairstepFileX_unauthorized {cA σ I} {g : Sat256} {s0 : State} {k C : ℕ}
    {sel : UInt256} (hauth : relyAuthWord σ I ≠ ⟨1⟩)
    (h : RD linearDecreaseBytecode I g s0 ⟨315⟩
      [fileData I, calldataWord I.calldata 4, ⟨138⟩, sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    RDrev linearDecreaseBytecode g s0 := by
  have hauthSlot :
      UInt256.ofNat (fromByteArrayBigEndian
          (ffi.KEC ((relyAuthHashMem I).readWithPadding 0 64))) =
        mapSlot (relySourceWord I) ⟨0⟩ := by
    simpa [relyAuthHashMem, mapSlot, solcMappingSlot] using
      twoWordHashMem_solcMappingSlot (⟨0⟩ : UInt256) (relySourceWord I)
        solcFreePtrMem_size
  have rd356pre := evm_run h with [
    raw jumpdest (by decide +native) (by evm_ov),
    raw caller (by decide +native) (by evm_ov),
    raw push1 ⟨0⟩ (by decide +native) (by evm_ov),
    raw swap1 (by decide +native) (by evm_ov),
    raw dup2 (by decide +native) (by evm_ov)]
  have rd357 := rd356pre.mstore 0 (wordAt0Mem (relySourceWord I) solcFreePtrMem)
    (UInt256.ofNat 3) (by decide +native) mem_cost (by rfl) (by decide +native)
    (by evm_ov)
  have rd361pre := evm_run rd357 with [
    raw push1 ⟨32⟩ (by decide +native) (by evm_ov),
    raw dup2 (by decide +native) (by evm_ov),
    raw swap1 (by decide +native) (by evm_ov)]
  have rd362 := rd361pre.mstore 0 (relyAuthHashMem I)
    (UInt256.ofNat 3) (by decide +native) mem_cost (by rfl) (by decide +native)
    (by evm_ov)
  have rd365pre := evm_run rd362 with [
    raw push1 ⟨64⟩ (by decide +native) (by evm_ov),
    raw swap1 (by decide +native) (by evm_ov)]
  have rd366 := rd365pre.keccak256 0 (mapSlot (relySourceWord I) ⟨0⟩)
    (UInt256.ofNat 3) (by decide +native) mem_cost hauthSlot (by decide +native)
    (by evm_ov)
  obtain ⟨k367, C367, rd367raw⟩ := rd366.sload (by decide +native) (by evm_ov)
  have rd367 : RD linearDecreaseBytecode I g s0 ⟨332⟩
      (relyAuthWord σ I :: fileData I :: calldataWord I.calldata 4 :: ⟨138⟩ :: [sel])
      (relyAuthHashMem I) (UInt256.ofNat 3) ByteArray.empty (cA, σ) k367 C367 := by
    simpa [relyAuthWord, stairstepSlotWord, relyAuthStorageSlot_eq_mapSlot_source I]
      using rd367raw
  have rd370pre := evm_run rd367 with [
    raw push1 ⟨1⟩ (by decide +native) (by evm_ov),
    raw eq (by decide +native) (by evm_ov)]
  have heq : UInt256.eq (⟨1⟩ : UInt256) (relyAuthWord σ I) = ⟨0⟩ := by
    exact u256_eq_of_ne (by intro hbad; exact hauth hbad.symm)
  rw [heq] at rd370pre
  have rd373 := rd370pre.pushConst (⟨415⟩ : UInt256)
    (width := 2) (op := .PUSH2) (by decide) (by decide +native) (by evm_ov)
  have rd374 := rd373.jumpiNT (by decide +native) rfl (by evm_ov)
  exact RD.stairstepInlineErrorStringRevertTail
    (pc := ⟨339⟩) (len := ⟨29⟩)
    (word := ⟨0x4c696e65617244656372656173652f6e6f742d617574686f72697a6564000000⟩)
    rd374
    (by
      unfold stairstepInlineErrorStringRevertTailWf
      repeat' first | apply And.intro | decide +native)
    (relyAuthHashMem_size I)
    (relyAuthHashMem_read64 I)
    (by simp only [List.length_cons, List.length_nil]; omega)

set_option maxHeartbeats 2000000 in
theorem stairstepFileX_logReturn {I} {g : Sat256} {s0 : State} {k C : ℕ}
    {what sel : UInt256} {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    (hperm : I.perm = true)
    (h : RD linearDecreaseBytecode I g s0 ⟨494⟩
      [fileData I, what, ⟨138⟩, sel]
      (relyAuthHashMem I) (UInt256.ofNat 3) ByteArray.empty acc k C) :
    RDret linearDecreaseBytecode g s0 acc ByteArray.empty := by
  have rd612pre := evm_run h with [
    raw jumpdest (by decide +native) (by evm_ov),
    raw push1 ⟨64⟩ (by decide +native) (by evm_ov),
    raw dup1 (by decide +native) (by evm_ov),
    raw mload 0 ⟨128⟩ (UInt256.ofNat 3) (by decide +native)
      mem_cost
      (mloadFreePtrValue (by rw [relyAuthHashMem_size I]; decide) (by decide)
        (relyAuthHashMem_read64 I))
      (by decide +native) (by evm_ov),
    raw dup3 (by decide +native) (by evm_ov),
    raw dup2 (by decide +native) (by evm_ov)]
  have rd615 := rd612pre.mstore 6 (fileLogDataMem I)
    (UInt256.ofNat 5) (by decide +native) mem_cost (by rfl) (by decide +native)
    (by evm_ov)
  have rd619pre := evm_run rd615 with [
    raw swap1 (by decide +native) (by evm_ov),
    raw mload 0 ⟨128⟩ (UInt256.ofNat 5) (by decide +native)
      mem_cost
      (mloadFreePtrValue (by rw [fileLogDataMem_size I]; decide) (by decide)
        (fileLogDataMem_read64 I))
      (by decide +native) (by evm_ov),
    raw dup4 (by decide +native) (by evm_ov),
    raw swap2 (by decide +native) (by evm_ov)]
  have rd652 := rd619pre.pushConst
    (⟨0xe986e40cc8c151830d4f61050f4fb2e4add8567caad2d5f5496f9158e91fe4c7⟩ :
      UInt256)
    (width := 32) (op := .PUSH32) (by decide) (by decide +native) (by evm_ov)
  have rd661pre := evm_run rd652 with [
    raw swap2 (by decide +native) (by evm_ov),
    raw swap1 (by decide +native) (by evm_ov),
    raw dup2 (by decide +native) (by evm_ov),
    raw swap1 (by decide +native) (by evm_ov),
    raw sub (by decide +native) (by evm_ov),
    raw push1 ⟨32⟩ (by decide +native) (by evm_ov),
    raw add (by decide +native) (by evm_ov),
    raw swap1 (by decide +native) (by evm_ov)]
  have rd662 := RD.log2
    (a := ⟨128⟩) (b := ⟨32⟩)
    (c := ⟨0xe986e40cc8c151830d4f61050f4fb2e4add8567caad2d5f5496f9158e91fe4c7⟩)
    (d := what)
    (t := [fileData I, what, ⟨138⟩, sel])
    0
    (UInt256.ofNat
      (MachineState.M (UInt256.ofNat 5).toNat (⟨128⟩ : UInt256).toNat
        (⟨32⟩ : UInt256).toNat))
    rd661pre (by decide +native) hperm mem_cost (by decide +native)
    (by simp only [List.length_cons, List.length_nil]; omega)
  have rd663 := RD.pop (a := fileData I) (t := [what, ⟨138⟩, sel])
    rd662 (by decide +native) (by evm_ov)
  have rd664 := RD.pop (a := what) (t := [⟨138⟩, sel])
    rd663 (by decide +native) (by evm_ov)
  have rd165 := RD.jump (a := ⟨138⟩) (t := [sel]) rd664
    (by decide +native) (by jump_dest) (by evm_ov)
  have rd166 := RD.jumpdest (pc := ⟨138⟩) (stk := [sel]) rd165
    (by decide +native) (by evm_ov)
  exact RD.stop rd166 (by decide +native) (by evm_ov)

set_option maxHeartbeats 3000000 in
theorem stairstepFileX_tau_ok {cA σ I} {g : Sat256} {s0 : State} {k C : ℕ}
    {sel : UInt256} (hperm : I.perm = true)
    (hwhatWord : calldataWord I.calldata 4 = ABI.bytesToWord fileTauBytes)
    (h : RD linearDecreaseBytecode I g s0 ⟨415⟩
      [fileData I, calldataWord I.calldata 4, ⟨138⟩, sel]
      (relyAuthHashMem I) (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    RDret linearDecreaseBytecode g s0
      (cA, sstoreAccountMap I.codeOwner σ ⟨1⟩ (fileData I)) ByteArray.empty := by
  have rd424pre := evm_run h with [
    raw jumpdest (by decide +native) (by evm_ov),
    raw dup2 (by decide +native) (by evm_ov)]
  have rd421 := rd424pre.pushConst (⟨0x746175⟩ : UInt256)
    (width := 3) (op := .PUSH3) (by decide) (by decide +native) (by evm_ov)
  have rd424pre := evm_run rd421 with [
    raw push1 ⟨232⟩ (by decide +native) (by evm_ov),
    raw shl (by decide +native) (by evm_ov),
    raw eq (by decide +native) (by evm_ov)]
  rw [hwhatWord, fileTauBytes_word, u256_eq_refl] at rd424pre
  have rd430pre := evm_run rd424pre with [
    raw iszero (by decide +native) (by evm_ov),
    raw push2 ⟨439⟩ (by decide +native) (by evm_ov),
    raw jumpiNT (by decide +native) rfl (by evm_ov)]
  have rd434pre := evm_run rd430pre with [
    raw push1 ⟨1⟩ (by decide +native) (by evm_ov),
    raw dup2 (by decide +native) (by evm_ov),
    raw swap1 (by decide +native) (by evm_ov)]
  obtain ⟨k435, C435, rd435raw⟩ := rd434pre.sstore hperm (by decide +native)
    (by simp only [List.length_cons, List.length_nil]; omega)
  have rd435 : RD linearDecreaseBytecode I g s0 ⟨435⟩
      [fileData I, UInt256.shiftLeft (⟨0x746175⟩ : UInt256) ⟨232⟩, ⟨138⟩, sel]
      (relyAuthHashMem I) (UInt256.ofNat 3) ByteArray.empty
      (cA, sstoreAccountMap I.codeOwner σ ⟨1⟩ (fileData I)) k435 C435 := by
    simpa using rd435raw
  have rd494 := evm_run rd435 with [
    raw push2 ⟨494⟩ (by decide +native) (by evm_ov),
    raw jump (by decide +native) (by jump_dest) (by evm_ov)]
  exact stairstepFileX_logReturn hperm rd494

set_option maxHeartbeats 3000000 in
theorem stairstepFileX_unrecognized {cA σ I} {g : Sat256} {s0 : State} {k C : ℕ}
    {sel : UInt256}
    (hnotTauWord : calldataWord I.calldata 4 ≠ ABI.bytesToWord fileTauBytes)
    (h : RD linearDecreaseBytecode I g s0 ⟨415⟩
      [fileData I, calldataWord I.calldata 4, ⟨138⟩, sel]
      (relyAuthHashMem I) (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    RDrev linearDecreaseBytecode g s0 := by
  have rd424pre := evm_run h with [
    raw jumpdest (by decide +native) (by evm_ov),
    raw dup2 (by decide +native) (by evm_ov)]
  have rd421 := rd424pre.pushConst (⟨0x746175⟩ : UInt256)
    (width := 3) (op := .PUSH3) (by decide) (by decide +native) (by evm_ov)
  have rd424pre := evm_run rd421 with [
    raw push1 ⟨232⟩ (by decide +native) (by evm_ov),
    raw shl (by decide +native) (by evm_ov),
    raw eq (by decide +native) (by evm_ov)]
  have htauEq :
      UInt256.eq
          (UInt256.shiftLeft (⟨0x746175⟩ : UInt256) ⟨232⟩)
          (calldataWord I.calldata 4) = ⟨0⟩ := by
    rw [← fileTauBytes_word]
    exact u256_eq_of_ne (by intro hbad; exact hnotTauWord hbad.symm)
  rw [htauEq] at rd424pre
  have rd439 := evm_run rd424pre with [
    raw iszero (by decide +native) (by evm_ov),
    raw push2 ⟨439⟩ (by decide +native) (by evm_ov),
    raw jumpiT (by decide +native) one_ne_zero_uint (by jump_dest) (by evm_ov)]
  have rd439 := RD.jumpdest (pc := ⟨439⟩)
    (stk := [fileData I, calldataWord I.calldata 4, ⟨138⟩, sel]) rd439
    (by decide +native) (by evm_ov)
  exact RD.stairstepCodecopyRevertTail
    (offset := ⟨1078⟩) (len := ⟨38⟩) rd439
    (by
      unfold stairstepCodecopyRevertTailWf
      repeat' first | apply And.intro | decide +native)
    (relyAuthHashMem_size I)
    (relyAuthHashMem_read64 I)
    (by decide)
    (by decide +native)
    (by decide +native)
    (by decide +native)
    (by simp only [List.length_cons, List.length_nil]; omega)

theorem stairstepFileBody {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256}
    (hcode : I.code = linearDecreaseBytecode)
    (hsize : I.calldata.size < UInt256.size)
    (hperm : I.perm = true)
    (hwv : I.weiValue = ⟨0⟩)
    (hsel : selIs I (stairstepSelBytes 1))
    (hAccounts : accountMapEquiv σ_evm σ_solm) :
    runtimeEquivalenceFor config contract cA gh bl σ_evm σ_solm σ₀ g A I := by
  have hsz4 : 4 ≤ I.calldata.size :=
    calldata_size_ge_of_selIs I (stairstepSelBytes 1) rfl hsel
  have hdispatch : dispatchMsg contract I.calldata = some fileTransition :=
    stairstepDispatchFile hsel
  have hreach := stairstepReachFileBody (cA := cA) (gh := gh) (bl := bl)
    (σ := σ_evm) (σ₀ := σ₀) (A := A) (I := I) (g := Sat256.ofUInt256 g)
    hcode hwv hsz4 hsize hsel
  by_cases hsz68 : 68 ≤ I.calldata.size
  · have hdecode := stairstepDecode_file_ok (I := I) hsz68
    obtain ⟨_, _, rd350⟩ :=
      stairstepFileX_decoded (g := Sat256.ofUInt256 g) hsz68 hsize hreach
    let evmSolm := initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I
    have hauthCouple : relyAuthWord σ_evm I = relyAuthWord σ_solm I :=
      accountMapEquiv_storage_findD hAccounts I.codeOwner (relyAuthStorageSlot I) ⟨0⟩
    by_cases hauth : relyAuthWord σ_evm I = ⟨1⟩
    · have hauthSolm : relyAuthWord σ_solm I = ⟨1⟩ := by
        rw [← hauthCouple]
        exact hauth
      obtain ⟨_, _, rd428⟩ := stairstepFileX_authorized (I := I) hauth rd350
      have hsz36 : 36 ≤ I.calldata.size := by omega
      by_cases htau : fileWhat I = fileTauBytes
      · have htauWord :
            calldataWord I.calldata 4 = ABI.bytesToWord fileTauBytes := by
          rw [← fileWhatWord_eq (I := I) hsz36, htau]
        have hbody :
            ExecTransitionBody config contract evmSolm (fileLocals I) fileTransition.body
              (.returned { contract := contract, locals := fileLocals I }
                (fileTauPostState evmSolm I) none) := by
          simpa [evmSolm] using
            stairstepFileSourceBodyTauOk (cA := cA) (gh := gh) (bl := bl)
              (σ := σ_solm) (σ₀ := σ₀) (A := A) (I := I) (g := g)
              hwv hauthSolm htau
        exact (stairstepFileX_tau_ok hperm htauWord rd428)
          |>.reEquivExecutionGenAccountMapEquiv hcode hdispatch hdecode hbody
            (by simp [fileTauPostState, evmSolm, initState, storageStore_createdAccounts])
            (by
              simpa [fileTauPostState, evmSolm, initState, storageStore_accountMap] using
                accountMapEquiv_sstoreAccountMap I.codeOwner ⟨1⟩ (fileData I)
                  hAccounts)
            (by
              simpa [fileTransition] using
                (returnEquiv.fallthrough (o := ByteArray.empty) (r := none) (t := [])
                  (dvs := []) rfl (by decide +native) (by decide +native)))
      · have hnotTauWord :
            calldataWord I.calldata 4 ≠ ABI.bytesToWord fileTauBytes :=
          fileWhatWord_ne_of_bytes_ne hsz36 htau fileTauBytes_length
        have hbody :
            ExecTransitionBody config contract evmSolm (fileLocals I)
              fileTransition.body .reverted := by
          simpa [evmSolm] using
            stairstepFileSourceBodyUnrecognizedReverts
              (cA := cA) (gh := gh) (bl := bl) (σ := σ_solm) (σ₀ := σ₀)
              (A := A) (I := I) (g := g) hwv hauthSolm htau
        exact (stairstepFileX_unrecognized hnotTauWord rd428)
          |>.reEquivExecutionRevert hcode hdispatch hdecode hbody
    · have hauthSolm : relyAuthWord σ_solm I ≠ ⟨1⟩ := by
        intro hbad
        exact hauth (by rw [hauthCouple, hbad])
      have hbody :
          ExecTransitionBody config contract evmSolm (fileLocals I)
            fileTransition.body .reverted := by
        simpa [evmSolm] using
          stairstepFileSourceBodyAuthReverts
            (cA := cA) (gh := gh) (bl := bl) (σ := σ_solm) (σ₀ := σ₀)
            (A := A) (I := I) (g := g) hwv hauthSolm
      exact (stairstepFileX_unauthorized (I := I) hauth rd350)
        |>.reEquivExecutionRevert hcode hdispatch hdecode hbody
  · exact (stairstepFileX_shortarg (g := Sat256.ofUInt256 g) hsz4 hsize (by omega) hreach)
      |>.reEquivDecodingFailed hcode hdispatch
        (stairstepDecode_file_none_short hsz4 (by omega))

end Benchmarks.Dss.LinearDecrease
