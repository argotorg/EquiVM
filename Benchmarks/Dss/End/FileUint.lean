import Benchmarks.Dss.End.Rely

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach Reasoning.Refinement

set_option maxRecDepth 2000000
set_option maxHeartbeats 0

namespace Benchmarks.Dss.End

/-! ## `file(bytes32,uint256)` -/

abbrev endFileUintConcreteSelector : ByteArray := selectorBytes 0x29 0xae 0x81 0x14

abbrev endFileUintWhat (I : ExecutionEnv) : List UInt8 :=
  (I.calldata.toList.drop 4).take 32

abbrev endFileUintData (I : ExecutionEnv) : UInt256 :=
  calldataWord I.calldata 36

abbrev endFileUintWaitBytes : List UInt8 :=
  [119, 97, 105, 116, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
   0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]

abbrev endFileUintLocals (I : ExecutionEnv) : Store :=
  ((∅ : Store).insert "what" (.fixedBytes bytes32Width (endFileUintWhat I))).insert
    "data" (.int (Int.ofNat (endFileUintData I).toNat))

theorem endFileUintWhat_length {I : ExecutionEnv} (hsz36 : 36 ≤ I.calldata.size) :
    (endFileUintWhat I).length = 32 := by
  simp [endFileUintWhat, List.length_take, List.length_drop, byteArray_toList_eq]
  omega

theorem endFileUintWaitBytes_length : endFileUintWaitBytes.length = 32 := by
  native_decide

theorem endFileUintWaitBytes_word :
    ABI.bytesToWord endFileUintWaitBytes =
      UInt256.shiftLeft (⟨0x1dd85a5d⟩ : UInt256) ⟨226⟩ := by
  native_decide

theorem endFileUintWhatWord_eq {I : ExecutionEnv} (hsz36 : 36 ≤ I.calldata.size) :
    ABI.bytesToWord (endFileUintWhat I) = calldataWord I.calldata 4 := by
  simpa [endFileUintWhat] using decode_word_at_eq I.calldata 4 (by omega) (by norm_num)

theorem endFileUintWhat_eq_of_word_eq {I : ExecutionEnv} {bs : List UInt8}
    (hsz36 : 36 ≤ I.calldata.size) (hword : calldataWord I.calldata 4 = ABI.bytesToWord bs)
    (hbsLen : bs.length = 32) :
    endFileUintWhat I = bs := by
  have hto := toBytesBE_bytesToWord_of_length (bs := endFileUintWhat I)
    (endFileUintWhat_length (I := I) hsz36)
  rw [endFileUintWhatWord_eq (I := I) hsz36, hword] at hto
  exact hto.symm.trans (toBytesBE_bytesToWord_of_length (bs := bs) hbsLen)

theorem endFileUintWhatWord_ne_of_bytes_ne {I : ExecutionEnv} {bs : List UInt8}
    (hsz36 : 36 ≤ I.calldata.size) (hneq : endFileUintWhat I ≠ bs)
    (hbsLen : bs.length = 32) :
    calldataWord I.calldata 4 ≠ ABI.bytesToWord bs := by
  intro hword
  exact hneq (endFileUintWhat_eq_of_word_eq hsz36 hword hbsLen)

theorem endDecodeCalldata_legacyBytes32_uint256_ok {cd : ByteArray} {x y : Solm.Ident}
    (hsz68 : 68 ≤ cd.size) :
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
  rw [show abiTupleHeadSize? [abiBytes32, abiUInt256] = some 64 by native_decide]
  simp only [bind, Option.bind]
  rw [endDecodeABIValues_bytes32_uint256_legacy_ok (bytes := cd.toList.drop 4)
    (by simpa using htake4)
    (by simpa [List.drop_drop, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using htake36)]
  rw [if_neg (by rw [List.length_drop, htlen]; omega :
    ¬ (cd.toList.drop 4).length < 64)]
  simp [decodeCalldata.insertValues]
  rw [hword36]

theorem endDecodeCalldata_legacyBytes32_uint256_none_short {cd : ByteArray}
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
  rw [show abiTupleHeadSize? [abiBytes32, abiUInt256] = some 64 by native_decide]
  simp only [bind, Option.bind]
  by_cases hbytes : (cd.toList.drop 4).length < 64
  · rw [if_pos hbytes]
  · rw [if_neg hbytes]
    rw [endDecodeABIValues_bytes32_uint256_legacy_none_short
      (bytes := cd.toList.drop 4) (by
        rw [List.length_drop, htlen]
        omega)]

theorem endDecode_fileUint_ok {I : ExecutionEnv} (hsz68 : 68 ≤ I.calldata.size) :
    decodeCalldataWithMode config.abiDecodeMode (fileUintTransition.params.map Param.name)
      (transitionSignature fileUintTransition).paramTypes I.calldata =
        some (endFileUintLocals I) := by
  simpa [config, fileUintTransition, bytes32, bytes32Width, uint256, uint256Int,
    endFileUintLocals, endFileUintWhat, endFileUintData, abiBytes32, abiBytes32Width,
    abiUInt256] using
    (endDecodeCalldata_legacyBytes32_uint256_ok (cd := I.calldata) (x := "what")
      (y := "data") hsz68)

theorem endDecode_fileUint_none_short {I : ExecutionEnv}
    (hsz4 : 4 ≤ I.calldata.size) (hshort : I.calldata.size < 68) :
    decodeCalldataWithMode config.abiDecodeMode (fileUintTransition.params.map Param.name)
      (transitionSignature fileUintTransition).paramTypes I.calldata = none := by
  simpa [config, fileUintTransition, bytes32, bytes32Width, uint256, uint256Int,
    abiBytes32, abiBytes32Width, abiUInt256] using
    (endDecodeCalldata_legacyBytes32_uint256_none_short (cd := I.calldata) (x := "what")
      (y := "data") hsz4 hshort)

theorem endFileUintLocals_get_what (I : ExecutionEnv) :
    (endFileUintLocals I).get? "what" =
      some (.fixedBytes bytes32Width (endFileUintWhat I)) := by
  rw [endFileUintLocals, store_get_ne _ _ (by decide), store_get_self]

theorem endFileUintLocals_get_data (I : ExecutionEnv) :
    (endFileUintLocals I).get? "data" =
      some (.int (Int.ofNat (endFileUintData I).toNat)) := by
  rw [endFileUintLocals, store_get_self]

theorem endFileUintLocals_get_wards (I : ExecutionEnv) :
    (endFileUintLocals I).get? "wards" = none := by
  rw [endFileUintLocals, store_get_ne _ _ (by decide), store_get_ne _ _ (by decide)]
  simp

theorem endFileUintLocals_get_live (I : ExecutionEnv) :
    (endFileUintLocals I).get? "live" = none := by
  rw [endFileUintLocals, store_get_ne _ _ (by decide), store_get_ne _ _ (by decide)]
  simp

theorem endFileUintLocals_get_wait (I : ExecutionEnv) :
    (endFileUintLocals I).get? "wait" = none := by
  rw [endFileUintLocals, store_get_ne _ _ (by decide), store_get_ne _ _ (by decide)]
  simp

theorem evalExpr_endFileUintData {evm : EVM.State} {I : ExecutionEnv} {locals : Store}
    (h : locals.get? "data" = some (.int (Int.ofNat (endFileUintData I).toNat))) :
    evalExpr? config { contract := contract, locals := locals } evm (.var "data") =
      .ok (.int (Int.ofNat (endFileUintData I).toNat)) := by
  rw [evalExpr?]
  change EvalResult.ofOption EvalError.unboundVariable (locals.get? "data") =
    .ok (.int (Int.ofNat (endFileUintData I).toNat))
  rw [h]
  rfl

theorem evalExpr_endFileUintWhatEq_true {evm : EVM.State} {I : ExecutionEnv}
    {locals : Store} {bs : List UInt8}
    (hget : locals.get? "what" = some (.fixedBytes bytes32Width (endFileUintWhat I)))
    (hwhat : endFileUintWhat I = bs) :
    evalExpr? config { contract := contract, locals := locals } evm
      (.binary .eq (.var "what") (.fixedBytesLit bytes32Width bs)) = .ok (.bool true) := by
  have hvar :
      evalExpr? config { contract := contract, locals := locals } evm (.var "what") =
        .ok (.fixedBytes bytes32Width (endFileUintWhat I)) := by
    rw [evalExpr?]
    change EvalResult.ofOption EvalError.unboundVariable (locals.get? "what") =
      .ok (.fixedBytes bytes32Width (endFileUintWhat I))
    rw [hget]
    rfl
  rw [evalExpr?]
  simp only [hvar, EvalResult.bind, bind]
  simp [evalExpr?, evalBinaryOp?, hwhat]
  all_goals decide

theorem evalExpr_endFileUintWhatEq_false {evm : EVM.State} {I : ExecutionEnv}
    {locals : Store} {bs : List UInt8}
    (hget : locals.get? "what" = some (.fixedBytes bytes32Width (endFileUintWhat I)))
    (hwhat : endFileUintWhat I ≠ bs) :
    evalExpr? config { contract := contract, locals := locals } evm
      (.binary .eq (.var "what") (.fixedBytesLit bytes32Width bs)) = .ok (.bool false) := by
  have hvar :
      evalExpr? config { contract := contract, locals := locals } evm (.var "what") =
        .ok (.fixedBytes bytes32Width (endFileUintWhat I)) := by
    rw [evalExpr?]
    change EvalResult.ofOption EvalError.unboundVariable (locals.get? "what") =
      .ok (.fixedBytes bytes32Width (endFileUintWhat I))
    rw [hget]
    rfl
  rw [evalExpr?]
  simp only [hvar, EvalResult.bind, bind]
  simp [evalExpr?, evalBinaryOp?, hwhat]
  all_goals decide

theorem evalStorageRef_endFileUint_auth (evm : EVM.State) (I : ExecutionEnv)
    (hsrc : evm.executionEnv.source = I.source) :
    evalStorageRef config { contract := contract, locals := endFileUintLocals I } evm
      (wardsRef sender) = .ok (endRelyAuthEvaledRef I) := by
  simp [evalStorageRef, evalStorageRefStep, wardsRef, sender, envValue,
    endRelyAuthEvaledRef, endRelyAuthKey, hsrc, valueToKey?, EvalResult.bind,
    EvalResult.ofOption, bind, pure, evalExpr?]

theorem evalExpr_endFileUint_auth_true (evm : EVM.State) (I : ExecutionEnv)
    (hsrc : evm.executionEnv.source = I.source)
    (hload :
      Solm.EVM.storageLoad evm evm.executionEnv.codeOwner (endRelyAuthStorageSlot I) =
        ⟨1⟩) :
    evalExpr? config { contract := contract, locals := endFileUintLocals I } evm
      (.binary .eq (.storage (wardsRef sender)) (.intLit 1)) = .ok (.bool true) := by
  have hstorage :
      evalExpr? config { contract := contract, locals := endFileUintLocals I } evm
        (.storage (wardsRef sender)) = .ok (.int 1) := by
    rw [evalExpr_storage_scalar_value
      (cfg := config)
      (solm := { contract := contract, locals := endFileUintLocals I })
      (slot := wardsRef sender)
      (er := endRelyAuthEvaledRef I)
      (t := .int uint256Int)
      (loc := wordLoc (endRelyAuthStorageSlot I))
      (value := .int 1)
      (hbase := by simp [endFileUintLocals, wardsRef])
      (her := evalStorageRef_endFileUint_auth evm I hsrc)
      (hty := by simp [storageTypeAt?, storageTypeStep?, contract, storageDecls, uint256St])
      (hloc := by rfl)
      (hload := by
        simpa [hload] using endStorageLocLoad_uint256 evm (endRelyAuthStorageSlot I))]
  simp only [evalExpr?, hstorage, EvalResult.bind, bind, pure]
  rfl

theorem evalExpr_endFileUint_auth_false (evm : EVM.State) (I : ExecutionEnv)
    (hsrc : evm.executionEnv.source = I.source)
    (hload :
      Solm.EVM.storageLoad evm evm.executionEnv.codeOwner (endRelyAuthStorageSlot I) ≠
        ⟨1⟩) :
    evalExpr? config { contract := contract, locals := endFileUintLocals I } evm
      (.binary .eq (.storage (wardsRef sender)) (.intLit 1)) = .ok (.bool false) := by
  have hstorage :
      evalExpr? config { contract := contract, locals := endFileUintLocals I } evm
        (.storage (wardsRef sender)) =
          .ok (.int (Int.ofNat
            (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner
              (endRelyAuthStorageSlot I)).toNat)) := by
    exact evalExpr_storage_scalar_value
      (cfg := config)
      (solm := { contract := contract, locals := endFileUintLocals I })
      (slot := wardsRef sender)
      (er := endRelyAuthEvaledRef I)
      (t := .int uint256Int)
      (loc := wordLoc (endRelyAuthStorageSlot I))
      (hbase := by simp [endFileUintLocals, wardsRef])
      (her := evalStorageRef_endFileUint_auth evm I hsrc)
      (hty := by simp [storageTypeAt?, storageTypeStep?, contract, storageDecls, uint256St])
      (hloc := by rfl)
      (hload := by exact endStorageLocLoad_uint256 evm (endRelyAuthStorageSlot I))
  have hne :
      Value.int (Int.ofNat
          (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner
            (endRelyAuthStorageSlot I)).toNat) ≠ Value.int 1 := by
    intro hbad
    rw [Value.int.injEq] at hbad
    apply hload
    exact endUInt256_toNat_eq_one (Int.ofNat.inj hbad)
  have hbeq :
      (Value.int (Int.ofNat
          (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner
            (endRelyAuthStorageSlot I)).toNat) == Value.int 1) = false := by
    exact beq_eq_false_iff_ne.mpr hne
  simp only [evalExpr?, hstorage, EvalResult.bind, bind, pure]
  change evalBinaryOp? BinaryOp.eq
      (Value.int (Int.ofNat
        (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner
          (endRelyAuthStorageSlot I)).toNat))
      (Value.int 1) = .ok (.bool false)
  simp only [evalBinaryOp?]
  rw [hbeq]

abbrev endLiveEvaledRef : EvaledStorageRef :=
  { base := "live", steps := [] }

theorem evalStorageRef_endFileUint_live (evm : EVM.State) (I : ExecutionEnv) :
    evalStorageRef config { contract := contract, locals := endFileUintLocals I } evm
      liveRef = .ok endLiveEvaledRef := by
  simp [endLiveEvaledRef, liveRef, evalStorageRef, evalStorageRefSteps, EvalResult.bind,
    pure, bind]

theorem evalExpr_endFileUint_live_true (evm : EVM.State) (I : ExecutionEnv)
    (hload : Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨8⟩ = ⟨1⟩) :
    evalExpr? config { contract := contract, locals := endFileUintLocals I } evm
      (.binary .eq (.storage liveRef) (.intLit 1)) = .ok (.bool true) := by
  have hstorage :
      evalExpr? config { contract := contract, locals := endFileUintLocals I } evm
        (.storage liveRef) = .ok (.int 1) := by
    rw [evalExpr_storage_scalar_value
      (cfg := config)
      (solm := { contract := contract, locals := endFileUintLocals I })
      (slot := liveRef)
      (er := endLiveEvaledRef)
      (t := .int uint256Int)
      (loc := wordLoc ⟨8⟩)
      (value := .int 1)
      (hbase := endFileUintLocals_get_live I)
      (her := evalStorageRef_endFileUint_live evm I)
      (hty := by simp [storageTypeAt?, contract, storageDecls, uint256St])
      (hloc := by rfl)
      (hload := by simpa [hload] using endStorageLocLoad_uint256 evm ⟨8⟩)]
  simp only [evalExpr?, hstorage, EvalResult.bind, bind, pure]
  rfl

theorem evalExpr_endFileUint_live_false (evm : EVM.State) (I : ExecutionEnv)
    (hload : Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨8⟩ ≠ ⟨1⟩) :
    evalExpr? config { contract := contract, locals := endFileUintLocals I } evm
      (.binary .eq (.storage liveRef) (.intLit 1)) = .ok (.bool false) := by
  have hstorage :
      evalExpr? config { contract := contract, locals := endFileUintLocals I } evm
        (.storage liveRef) =
          .ok (.int (Int.ofNat
            (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨8⟩).toNat)) := by
    exact evalExpr_storage_scalar_value
      (cfg := config)
      (solm := { contract := contract, locals := endFileUintLocals I })
      (slot := liveRef)
      (er := endLiveEvaledRef)
      (t := .int uint256Int)
      (loc := wordLoc ⟨8⟩)
      (hbase := endFileUintLocals_get_live I)
      (her := evalStorageRef_endFileUint_live evm I)
      (hty := by simp [storageTypeAt?, contract, storageDecls, uint256St])
      (hloc := by rfl)
      (hload := by exact endStorageLocLoad_uint256 evm ⟨8⟩)
  have hne :
      Value.int (Int.ofNat
          (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨8⟩).toNat) ≠
        Value.int 1 := by
    intro hbad
    rw [Value.int.injEq] at hbad
    apply hload
    exact endUInt256_toNat_eq_one (Int.ofNat.inj hbad)
  have hbeq :
      (Value.int (Int.ofNat
          (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨8⟩).toNat) ==
        Value.int 1) = false := by
    exact beq_eq_false_iff_ne.mpr hne
  simp only [evalExpr?, hstorage, EvalResult.bind, bind, pure]
  change evalBinaryOp? BinaryOp.eq
      (Value.int (Int.ofNat
        (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨8⟩).toNat))
      (Value.int 1) = .ok (.bool false)
  simp only [evalBinaryOp?]
  rw [hbeq]

def endFileUintPostState (evm : EVM.State) (I : ExecutionEnv) : EVM.State :=
  Solm.EVM.storageStore evm evm.executionEnv.codeOwner ⟨10⟩ (endFileUintData I)

theorem endFileUintAssignWait (evm : EVM.State) (I : ExecutionEnv) :
    assignStorageRef? config { contract := contract, locals := endFileUintLocals I } evm
      .storage waitRef (.int (Int.ofNat (endFileUintData I).toNat)) =
        .ok ({ contract := contract, locals := endFileUintLocals I },
          endFileUintPostState evm I) := by
  apply assignStorageRef_storage_scalar
      (ty := uint256St)
      (er := ({ base := "wait", steps := [] } : EvaledStorageRef))
      (loc := wordLoc ⟨10⟩)
      (hbase := endFileUintLocals_get_wait I)
      (her := by simp [waitRef, evalStorageRef, evalStorageRefSteps, EvalResult.bind,
        pure, bind])
      (hty := by simp [storageTypeAt?, contract, storageDecls, uint256St])
      (hloc := by rfl)
  simpa [endFileUintPostState] using endStorageLocStore_uint256 evm ⟨10⟩ (endFileUintData I)

theorem endFileUintSourceWaitOk {cA gh bl σ σ₀ A I} {g : UInt256}
    (hwv : I.weiValue = ⟨0⟩)
    (hauth : endRelyAuthWord σ I = ⟨1⟩)
    (hlive : endSlotWord ⟨8⟩ σ I = ⟨1⟩)
    (hwhat : endFileUintWhat I = endFileUintWaitBytes) :
    let locals := endFileUintLocals I
    let evm0 := initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I
    let evm1 := endFileUintPostState evm0 I
    ExecTransitionBody config contract evm0 locals fileUintTransition.body
      (.returned { contract := contract, locals := locals } evm1 none) := by
  intro locals evm0 evm1
  have hguardAuth :
      evalExpr? config { contract := contract, locals := locals } evm0
        (.binary .eq (.storage (wardsRef sender)) (.intLit 1)) = .ok (.bool true) := by
    simpa [locals, evm0, endRelyAuthWord, endSlotWord, initState, Solm.EVM.storageLoad,
      State.lookupAccount] using
      evalExpr_endFileUint_auth_true evm0 I (by simp [evm0, initState]) hauth
  have hguardLive :
      evalExpr? config { contract := contract, locals := locals } evm0
        (.binary .eq (.storage liveRef) (.intLit 1)) = .ok (.bool true) := by
    simpa [locals, evm0, endSlotWord, initState, Solm.EVM.storageLoad, State.lookupAccount]
      using evalExpr_endFileUint_live_true evm0 I hlive
  have hcond :
      evalExpr? config { contract := contract, locals := locals } evm0
        (.binary .eq (.var "what") waitLit) = .ok (.bool true) := by
    simpa [waitLit, endFileUintWaitBytes, locals] using
      (evalExpr_endFileUintWhatEq_true (evm := evm0) (I := I) (locals := locals)
        (bs := endFileUintWaitBytes) (by simpa [locals] using endFileUintLocals_get_what I)
        hwhat)
  have hdata :
      evalExpr? config { contract := contract, locals := locals } evm0 (.var "data") =
        .ok (.int (Int.ofNat (endFileUintData I).toNat)) := by
    simpa [locals] using
      evalExpr_endFileUintData (evm := evm0) (I := I) (locals := locals)
        (by simp [locals])
  have hassign :
      assignStorageRef? config { contract := contract, locals := locals } evm0
        .storage waitRef (.int (Int.ofNat (endFileUintData I).toNat)) =
          .ok ({ contract := contract, locals := locals }, evm1) := by
    simpa [locals, evm1] using endFileUintAssignWait evm0 I
  have hthen :
      ExecBlock config { contract := contract, locals := locals } evm0
        [.assign .storage waitRef (.var "data")]
        (.ok { contract := contract, locals := locals } evm1) := by
    exact ExecBlock.consNormal (ExecStmt.assign hdata hassign) ExecBlock.nil
  have hblock :
      ExecBlock config { contract := contract, locals := locals } evm0 fileUintTransition.body
        (.ok { contract := contract, locals := locals } evm1) := by
    refine ExecBlock.consNormal (ExecStmt.requireTrue ?_) ?_
    · exact evalCallvalueEq_true (by simp [evm0, initState]; exact hwv)
    refine ExecBlock.consNormal (ExecStmt.requireTrue hguardAuth) ?_
    refine ExecBlock.consNormal (ExecStmt.requireTrue hguardLive) ?_
    exact ExecBlock.consNormal (ExecStmt.iteTrue hcond hthen) ExecBlock.nil
  simpa [ExecTransitionBody, locals, evm0, evm1] using ExecFuncBody.execBlockOK hblock

theorem endFileUintSourceAuthReverts {cA gh bl σ σ₀ A I} {g : UInt256}
    (hwv : I.weiValue = ⟨0⟩)
    (hauth : endRelyAuthWord σ I ≠ ⟨1⟩) :
    let locals := endFileUintLocals I
    let evm0 := initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I
    ExecTransitionBody config contract evm0 locals fileUintTransition.body .reverted := by
  intro locals evm0
  have hguard :
      evalExpr? config { contract := contract, locals := locals } evm0
        (.binary .eq (.storage (wardsRef sender)) (.intLit 1)) = .ok (.bool false) := by
    simpa [locals, evm0, endRelyAuthWord, endSlotWord, initState, Solm.EVM.storageLoad,
      State.lookupAccount] using
      evalExpr_endFileUint_auth_false evm0 I (by simp [evm0, initState]) hauth
  refine ExecFuncBody.execBlockRevert ?_
  simpa [fileUintTransition, nonpayable, auth] using
    nonpayableSecondRequireReverts
      (cfg := config)
      (solm := { contract := contract, locals := locals })
      (evm := evm0)
      (guard := .binary .eq (.storage (wardsRef sender)) (.intLit 1))
      (rest := ([
        .require (.binary .eq (.storage liveRef) (.intLit 1)),
        .ite (.binary .eq (.var "what") waitLit)
          [ .assign .storage waitRef (.var "data") ]
          [ .require (.boolLit false) ]
      ] : List Stmt))
      (by simp [evm0, initState]; exact hwv)
      hguard

theorem endFileUintSourceLiveReverts {cA gh bl σ σ₀ A I} {g : UInt256}
    (hwv : I.weiValue = ⟨0⟩)
    (hauth : endRelyAuthWord σ I = ⟨1⟩)
    (hlive : endSlotWord ⟨8⟩ σ I ≠ ⟨1⟩) :
    let locals := endFileUintLocals I
    let evm0 := initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I
    ExecTransitionBody config contract evm0 locals fileUintTransition.body .reverted := by
  intro locals evm0
  have hguardAuth :
      evalExpr? config { contract := contract, locals := locals } evm0
        (.binary .eq (.storage (wardsRef sender)) (.intLit 1)) = .ok (.bool true) := by
    simpa [locals, evm0, endRelyAuthWord, endSlotWord, initState, Solm.EVM.storageLoad,
      State.lookupAccount] using
      evalExpr_endFileUint_auth_true evm0 I (by simp [evm0, initState]) hauth
  have hguardLive :
      evalExpr? config { contract := contract, locals := locals } evm0
        (.binary .eq (.storage liveRef) (.intLit 1)) = .ok (.bool false) := by
    simpa [locals, evm0, endSlotWord, initState, Solm.EVM.storageLoad, State.lookupAccount]
      using evalExpr_endFileUint_live_false evm0 I hlive
  have hblock :
      ExecBlock config { contract := contract, locals := locals } evm0 fileUintTransition.body
        .reverted := by
    refine ExecBlock.consNormal (ExecStmt.requireTrue ?_) ?_
    · exact evalCallvalueEq_true (by simp [evm0, initState]; exact hwv)
    refine ExecBlock.consNormal (ExecStmt.requireTrue hguardAuth) ?_
    exact ExecBlock.consRevert (ExecStmt.requireFalse hguardLive)
  simpa [ExecTransitionBody, fileUintTransition, nonpayable, auth, locals, evm0] using
    ExecFuncBody.execBlockRevert hblock

theorem endFileUintSourceUnrecognizedReverts {cA gh bl σ σ₀ A I} {g : UInt256}
    (hwv : I.weiValue = ⟨0⟩)
    (hauth : endRelyAuthWord σ I = ⟨1⟩)
    (hlive : endSlotWord ⟨8⟩ σ I = ⟨1⟩)
    (hnotWait : endFileUintWhat I ≠ endFileUintWaitBytes) :
    let locals := endFileUintLocals I
    let evm0 := initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I
    ExecTransitionBody config contract evm0 locals fileUintTransition.body .reverted := by
  intro locals evm0
  have hguardAuth :
      evalExpr? config { contract := contract, locals := locals } evm0
        (.binary .eq (.storage (wardsRef sender)) (.intLit 1)) = .ok (.bool true) := by
    simpa [locals, evm0, endRelyAuthWord, endSlotWord, initState, Solm.EVM.storageLoad,
      State.lookupAccount] using
      evalExpr_endFileUint_auth_true evm0 I (by simp [evm0, initState]) hauth
  have hguardLive :
      evalExpr? config { contract := contract, locals := locals } evm0
        (.binary .eq (.storage liveRef) (.intLit 1)) = .ok (.bool true) := by
    simpa [locals, evm0, endSlotWord, initState, Solm.EVM.storageLoad, State.lookupAccount]
      using evalExpr_endFileUint_live_true evm0 I hlive
  have hwait :
      evalExpr? config { contract := contract, locals := locals } evm0
        (.binary .eq (.var "what") waitLit) = .ok (.bool false) := by
    simpa [waitLit, endFileUintWaitBytes, locals] using
      (evalExpr_endFileUintWhatEq_false (evm := evm0) (I := I) (locals := locals)
        (bs := endFileUintWaitBytes) (by simpa [locals] using endFileUintLocals_get_what I)
        hnotWait)
  have hreqFalse :
      evalExpr? config { contract := contract, locals := locals } evm0 (.boolLit false) =
        .ok (.bool false) := by
    simp [evalExpr?, pure]
  have hunrec :
      ExecBlock config { contract := contract, locals := locals } evm0
        [.require (.boolLit false)] .reverted := by
    exact ExecBlock.consRevert (ExecStmt.requireFalse hreqFalse)
  have hblock :
      ExecBlock config { contract := contract, locals := locals } evm0 fileUintTransition.body
        .reverted := by
    refine ExecBlock.consNormal (ExecStmt.requireTrue ?_) ?_
    · exact evalCallvalueEq_true (by simp [evm0, initState]; exact hwv)
    refine ExecBlock.consNormal (ExecStmt.requireTrue hguardAuth) ?_
    refine ExecBlock.consNormal (ExecStmt.requireTrue hguardLive) ?_
    exact ExecBlock.consRevert (ExecStmt.iteFalse hwait hunrec)
  simpa [ExecTransitionBody, locals, evm0] using ExecFuncBody.execBlockRevert hblock

/-! ### Dispatch reachability -/

abbrev endFileUintEntryPc : UInt256 := ⟨527⟩
abbrev endFileUintDecodedPc : UInt256 := ⟨549⟩
abbrev endFileUintAuthPc : UInt256 := ⟨1315⟩
abbrev endFileUintLivePc : UInt256 := ⟨1404⟩
abbrev endFileUintSwitchPc : UInt256 := ⟨1474⟩
abbrev endFileUintUnrecognizedPc : UInt256 := ⟨1499⟩
abbrev endFileUintEventPc : UInt256 := ⟨1576⟩

set_option maxHeartbeats 1000000 in
theorem endFileUintArmsWellFormed :
    ∀ j, j ≤ 1 → armWellFormed endBytecode (nthArmPc endBytecode endDebtFirstArmPc j) := by
  intro j hj
  interval_cases j <;>
    (dsimp [armWellFormed]
     repeat' first | apply And.intro | native_decide)

theorem endReachFileUintBody {cA gh bl σ σ₀ A I} {g : Sat256}
    (hcode : I.code = endBytecode) (hwv : I.weiValue = ⟨0⟩)
    (hsz : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hsel : selIs I endFileUintConcreteSelector) :
    ∃ k C, RD endBytecode I g (initState cA gh bl σ σ₀ g A I)
        endFileUintEntryPc [endSelWord I] solcFreePtrMem (UInt256.ofNat 3)
        ByteArray.empty (cA, σ) k C := by
  have hword : endSelWord I = ⟨0x29ae8114⟩ :=
    endSelWord_eq_of_beq I hsz 0x29 0xae 0x81 0x14 ⟨0x29ae8114⟩
      (by native_decide) (by simpa [selIs, endFileUintConcreteSelector, selectorBytes] using hsel)
  obtain ⟨_, _, hfirst⟩ :=
    endReachDebtFirstArm (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀)
      (A := A) (I := I) (g := g) hcode hwv hsz hsize
      (by rw [hword]; native_decide)
      (by rw [hword]; native_decide)
      (by rw [hword]; native_decide)
  have heq0 : ∀ j, j < 1 →
      UInt256.eq (armSelNat endBytecode (nthArmPc endBytecode endDebtFirstArmPc j))
        (endSelWord I) = ⟨0⟩ := by
    intro j hj
    interval_cases j
    rw [hword]
    native_decide
  have htake :
      UInt256.eq (armSelNat endBytecode (nthArmPc endBytecode endDebtFirstArmPc 1))
        (endSelWord I) ≠ ⟨0⟩ := by
    rw [hword]
    native_decide
  exact RD.dispatchTo endFileUintEntryPc 1 hfirst
    (fun j hj => endFileUintArmsWellFormed j (le_trans hj (by omega)))
    heq0 htake (by jump_dest) (by native_decide) (by simp)

/-! ### Runtime trace -/

noncomputable def endFileUintLogDataMem (I : ExecutionEnv) : ByteArray :=
  (UInt256.toByteArray (endFileUintData I)).write 0 (endRelyAuthHashMem I) 128 32

theorem endFileUintLogDataMem_size (I : ExecutionEnv) :
    (endFileUintLogDataMem I).size = 160 := by
  unfold endFileUintLogDataMem
  exact toByteArray_write32_size_of_ge (endRelyAuthHashMem I) (endFileUintData I) 128 96 160
    (endRelyAuthHashMem_size I) (by omega)
    (by simpa using lt_usize 32 (by norm_num))
    (by omega)

theorem endFileUintLogDataMem_read64 (I : ExecutionEnv) :
    (endFileUintLogDataMem I).readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩ := by
  unfold endFileUintLogDataMem
  rw [toByteArray_write_read_below_of_gap (endFileUintData I) (endRelyAuthHashMem I) 128 64
    (by rw [endRelyAuthHashMem_size I]) (by omega)
    (by rw [endRelyAuthHashMem_size I]; exact lt_usize _ (by norm_num))]
  exact endRelyAuthHashMem_read64 I

@[reducible] def endLiveGuardTailPc (pc : UInt256) : UInt256 :=
  let p1 := pc + ⟨1⟩
  let p3 := p1 + UInt256.ofNat 2
  let p4 := p3 + ⟨1⟩
  let p6 := p4 + UInt256.ofNat 2
  let p7 := p6 + ⟨1⟩
  let p10 := p7 + UInt256.ofNat 3
  p10 + ⟨1⟩

@[reducible] def endLiveGuardWf (code : ByteArray) (pc okPc : UInt256) : Prop :=
  let p1 := pc + ⟨1⟩
  let p3 := p1 + UInt256.ofNat 2
  let p4 := p3 + ⟨1⟩
  let p6 := p4 + UInt256.ofNat 2
  let p7 := p6 + ⟨1⟩
  let p10 := p7 + UInt256.ofNat 3
  decode code pc = some (.JUMPDEST, .none)
  ∧ decode code p1 = some (.Push .PUSH1, some (⟨8⟩, 1))
  ∧ decode code p3 = some (.SLOAD, .none)
  ∧ decode code p4 = some (.Push .PUSH1, some (⟨1⟩, 1))
  ∧ decode code p6 = some (.EQ, .none)
  ∧ decode code p7 = some (.Push .PUSH2, some (okPc, 2))
  ∧ decode code p10 = some (.JUMPI, .none)

abbrev endNotLiveRawWord : UInt256 :=
  ⟨0x456e642f6e6f742d6c697665⟩

theorem RD.endLiveGuardOk {code : ByteArray} {g : Sat256} {s0 : State}
    {ee : ExecutionEnv} {k C : ℕ} {pc okPc key ret : UInt256} {R : List UInt256}
    {mem rdata : ByteArray} {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap}
    (h : RD code ee g s0 pc (key :: ret :: R) mem (UInt256.ofNat 3) rdata (cA, σ) k C)
    (hwf : endLiveGuardWf code pc okPc)
    (hlive : solcSlotWord σ ee ⟨8⟩ = ⟨1⟩)
    (hok : (D_J code 0).contains okPc = true)
    (hov : R.length + 6 ≤ 1024) :
    ∃ k' C', RD code ee g s0 okPc (key :: ret :: R) mem (UInt256.ofNat 3) rdata
      (cA, σ) k' C' := by
  rcases hwf with ⟨hd0, hd1, hd3, hd4, hd6, hd7, hd10⟩
  have rd3 := h.jumpdest hd0 (by evm_ov) |>.push1 ⟨8⟩ hd1 (by evm_ov)
  obtain ⟨_, _, rd4⟩ := rd3.sload hd3 (by evm_ov)
  have hliveRaw :
      (σ.find? ee.codeOwner |>.option ⟨0⟩
        (fun acc => acc.storage.findD ⟨8⟩ ⟨0⟩)) = ⟨1⟩ := by
    simpa [solcSlotWord] using hlive
  rw [hliveRaw] at rd4
  have rd6 := rd4.push1 ⟨1⟩ hd4 (by evm_ov)
  have rd7₀ := rd6.eq hd6 (by evm_ov)
  have rd7 := rd7₀
  rw [uInt256_eq_self] at rd7
  have rd10 := rd7.push2 okPc hd7 (by evm_ov)
  exact ⟨_, _, rd10.jumpiT hd10 one_ne_zero_uint hok (by evm_ov)⟩

theorem RD.endLiveGuardRevert {code : ByteArray} {g : Sat256} {s0 : State}
    {ee : ExecutionEnv} {k C : ℕ} {pc okPc key ret : UInt256} {R : List UInt256}
    {mem rdata : ByteArray} {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap}
    (h : RD code ee g s0 pc (key :: ret :: R) mem (UInt256.ofNat 3) rdata (cA, σ) k C)
    (hwf : endLiveGuardWf code pc okPc)
    (htail : solcErrorStringRevertTailWf code (endLiveGuardTailPc pc) ⟨12⟩
      endNotLiveRawWord ⟨160⟩ .PUSH12 12)
    (hlive : solcSlotWord σ ee ⟨8⟩ ≠ ⟨1⟩)
    (hmem : mem.size = 96)
    (hread64 : mem.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩)
    (hov : R.length + 7 ≤ 1024) :
    RDrev code g s0 := by
  rcases hwf with ⟨hd0, hd1, hd3, hd4, hd6, hd7, hd10⟩
  have rd3 := h.jumpdest hd0 (by evm_ov) |>.push1 ⟨8⟩ hd1 (by evm_ov)
  obtain ⟨_, _, rd4⟩ := rd3.sload hd3 (by evm_ov)
  have rd6 := rd4.push1 ⟨1⟩ hd4 (by evm_ov)
  have rd7₀ := rd6.eq hd6 (by evm_ov)
  have hliveRaw :
      (σ.find? ee.codeOwner |>.option ⟨0⟩
        (fun acc => acc.storage.findD ⟨8⟩ ⟨0⟩)) ≠ ⟨1⟩ := by
    simpa [solcSlotWord] using hlive
  have heq0 :
      UInt256.eq ⟨1⟩
        (σ.find? ee.codeOwner |>.option ⟨0⟩
          (fun acc => acc.storage.findD ⟨8⟩ ⟨0⟩)) = ⟨0⟩ := by
    exact u256_eq_of_ne (fun h1 => hliveRaw h1.symm)
  have rd7 := rd7₀
  rw [heq0] at rd7
  have rd10 := rd7.push2 okPc hd7 (by evm_ov)
  have rdTail₀ := rd10.jumpiNT hd10 (by decide : (⟨0⟩ : UInt256) = ⟨0⟩) (by evm_ov)
  exact RD.solcErrorStringRevertTail (by simpa [endLiveGuardTailPc] using rdTail₀) htail
    (by decide) (by rfl) hmem hread64 (by simpa only [List.length_cons] using hov)

theorem RD.endFileUintDecodeToRoutine {code : ByteArray} {g : Sat256} {s0 : State}
    {ee : ExecutionEnv} {k C : ℕ} {ret de sel : UInt256} {R : List UInt256}
    {mem rdata : ByteArray} {aw : UInt256}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    (h : RD code ee g s0 endFileUintDecodedPc (de :: ⟨4⟩ :: ret :: sel :: R)
        mem aw rdata acc k C)
    (hwf : code = endBytecode)
    (hroutine : (D_J code 0).contains endFileUintAuthPc = true)
    (hov : R.length + 8 ≤ 1024) :
    ∃ k' C', RD code ee g s0 endFileUintAuthPc
      (calldataWord ee.calldata 36 :: calldataWord ee.calldata 4 :: ret :: sel :: R)
      mem aw rdata acc k' C' := by
  subst hwf
  have rd550 := h.jumpdest (by native_decide) (by evm_ov)
  have rd551 := rd550.pop (by native_decide) (by evm_ov)
  have rd552 := rd551.dup1 (by native_decide) (by evm_ov)
  have rd553 := rd552.calldataload (by native_decide) (by evm_ov)
  have rd554 := rd553.swap1 (by native_decide) (by evm_ov)
  have rd556 := rd554.push1 ⟨32⟩ (by native_decide) (by evm_ov)
  have rd557 := rd556.add (by native_decide) (by evm_ov)
  have rd558 := rd557.calldataload (by native_decide) (by evm_ov)
  have rd561 := rd558.push2 endFileUintAuthPc (by native_decide) (by evm_ov)
  exact ⟨_, _, by
    simpa [endFileUintAuthPc, endFileUintDecodedPc, calldataWord,
      show (⟨4⟩ : UInt256).toNat = 4 from by decide,
      show (⟨36⟩ : UInt256).toNat = 36 from by decide]
      using rd561.jump (by native_decide) hroutine (by evm_ov)⟩

theorem endFileUintX_decoded {cA gh bl σ σ₀ A I} {g : Sat256} {sel : UInt256}
    (hsz68 : 68 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hreach : ∃ k C, RD endBytecode I g
      (initState cA gh bl σ σ₀ g A I) endFileUintEntryPc [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    ∃ k C, RD endBytecode I g
        (initState cA gh bl σ σ₀ g A I) endFileUintAuthPc
        [endFileUintData I, calldataWord I.calldata 4, endRelyReturnPc, sel]
        solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
  obtain ⟨_, _, hdecoded⟩ := RD.solcTwoAddressExternalLenOk
    (code := endBytecode) (sel := sel)
    (entry := endFileUintEntryPc) (ret := endRelyReturnPc)
    (decoded := endFileUintDecodedPc) hreach
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by jump_dest) hsz68 hsize
  obtain ⟨_, _, hroutine⟩ := RD.endFileUintDecodeToRoutine
    (code := endBytecode) (ret := endRelyReturnPc) (sel := sel) (R := [])
    hdecoded rfl (by jump_dest) (by simp)
  exact ⟨_, _, by simpa [endFileUintData] using hroutine⟩

theorem endFileUintX_shortarg {cA gh bl σ σ₀ A I} {g : Sat256} {sel : UInt256}
    (hsz4 : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hshort : I.calldata.size < 68)
    (hreach : ∃ k C, RD endBytecode I g
      (initState cA gh bl σ σ₀ g A I) endFileUintEntryPc [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    RDrev endBytecode g (initState cA gh bl σ σ₀ g A I) := by
  have hlt :
      UInt256.lt (UInt256.sub (UInt256.ofNat I.calldata.size) ⟨4⟩) ⟨64⟩ = ⟨1⟩ := by
    apply ult_one
    rw [usub_ofNat_word_toNat (by simpa using hsz4) hsize]
    change I.calldata.size - 4 < 64
    omega
  exact RD.solcExternalStaticArgsShortReverts
    (code := endBytecode) (sel := sel)
    (entry := endFileUintEntryPc) (ret := endRelyReturnPc)
    (decoded := endFileUintDecodedPc) (need := ⟨64⟩) hreach
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) hlt

theorem endFileUintX_authorized {cA σ I} {g : Sat256} {s0 : State} {k C : ℕ}
    {sel : UInt256} (hauth : endRelyAuthWord σ I = ⟨1⟩)
    (h : RD endBytecode I g s0 endFileUintAuthPc
      [endFileUintData I, calldataWord I.calldata 4, endRelyReturnPc, sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    ∃ k' C', RD endBytecode I g s0 endFileUintLivePc
      [endFileUintData I, calldataWord I.calldata 4, endRelyReturnPc, sel]
      (endRelyAuthHashMem I) (UInt256.ofNat 3) ByteArray.empty (cA, σ) k' C' := by
  have hauthSolc :
      solcSlotWord σ I (solcMappingSlot ⟨0⟩ (solcSourceWord I)) = ⟨1⟩ := by
    simpa [endRelyAuthWord, endSlotWord, endRelyAuthStorageSlot_eq_mapSlot_source I,
      mapSlot] using hauth
  simpa [endRelyAuthHashMem] using
    RD.endAuthCheckOk
      (code := endBytecode) (pc := endFileUintAuthPc) (okPc := endFileUintLivePc)
      (key := endFileUintData I) (ret := calldataWord I.calldata 4)
      (R := [endRelyReturnPc, sel])
      h
      (by
        unfold endAuthCheckWf
        repeat' first | apply And.intro | native_decide)
      hauthSolc (by jump_dest) (by simp)

theorem endFileUintX_unauthorized {cA σ I} {g : Sat256} {s0 : State} {k C : ℕ}
    {sel : UInt256} (hauth : endRelyAuthWord σ I ≠ ⟨1⟩)
    (h : RD endBytecode I g s0 endFileUintAuthPc
      [endFileUintData I, calldataWord I.calldata 4, endRelyReturnPc, sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    RDrev endBytecode g s0 := by
  have hauthSolc :
      solcSlotWord σ I (solcMappingSlot ⟨0⟩ (solcSourceWord I)) ≠ ⟨1⟩ := by
    simpa [endRelyAuthWord, endSlotWord, endRelyAuthStorageSlot_eq_mapSlot_source I,
      mapSlot] using hauth
  exact RD.endAuthCheckRevert
    (code := endBytecode) (pc := endFileUintAuthPc) (okPc := endFileUintLivePc)
    (key := endFileUintData I) (ret := calldataWord I.calldata 4)
    (R := [endRelyReturnPc, sel])
    h
    (by
      unfold endAuthCheckWf
      repeat' first | apply And.intro | native_decide)
    (by
      unfold solcErrorStringRevertTailWf endAuthTailPc endNotAuthorizedRawWord
      repeat' first | apply And.intro | native_decide)
    hauthSolc (by simp)

theorem endFileUintX_live {cA σ I} {g : Sat256} {s0 : State} {k C : ℕ}
    {sel : UInt256} (hlive : endSlotWord ⟨8⟩ σ I = ⟨1⟩)
    (h : RD endBytecode I g s0 endFileUintLivePc
      [endFileUintData I, calldataWord I.calldata 4, endRelyReturnPc, sel]
      (endRelyAuthHashMem I) (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    ∃ k' C', RD endBytecode I g s0 endFileUintSwitchPc
      [endFileUintData I, calldataWord I.calldata 4, endRelyReturnPc, sel]
      (endRelyAuthHashMem I) (UInt256.ofNat 3) ByteArray.empty (cA, σ) k' C' := by
  have hliveSolc : solcSlotWord σ I ⟨8⟩ = ⟨1⟩ := by
    simpa [endSlotWord] using hlive
  exact RD.endLiveGuardOk
    (code := endBytecode) (pc := endFileUintLivePc) (okPc := endFileUintSwitchPc)
    (key := endFileUintData I) (ret := calldataWord I.calldata 4)
    (R := [endRelyReturnPc, sel])
    h
    (by
      unfold endLiveGuardWf
      repeat' first | apply And.intro | native_decide)
    hliveSolc (by jump_dest) (by simp)

theorem endFileUintX_notLive {cA σ I} {g : Sat256} {s0 : State} {k C : ℕ}
    {sel : UInt256} (hlive : endSlotWord ⟨8⟩ σ I ≠ ⟨1⟩)
    (h : RD endBytecode I g s0 endFileUintLivePc
      [endFileUintData I, calldataWord I.calldata 4, endRelyReturnPc, sel]
      (endRelyAuthHashMem I) (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    RDrev endBytecode g s0 := by
  have hliveSolc : solcSlotWord σ I ⟨8⟩ ≠ ⟨1⟩ := by
    simpa [endSlotWord] using hlive
  exact RD.endLiveGuardRevert
    (code := endBytecode) (pc := endFileUintLivePc) (okPc := endFileUintSwitchPc)
    (key := endFileUintData I) (ret := calldataWord I.calldata 4)
    (R := [endRelyReturnPc, sel])
    h
    (by
      unfold endLiveGuardWf
      repeat' first | apply And.intro | native_decide)
    (by
      unfold solcErrorStringRevertTailWf endLiveGuardTailPc endNotLiveRawWord
      repeat' first | apply And.intro | native_decide)
    hliveSolc (endRelyAuthHashMem_size I) (endRelyAuthHashMem_read64 I) (by simp)

set_option maxHeartbeats 2000000 in
theorem endFileUintX_logReturn {I} {g : Sat256} {s0 : State} {k C : ℕ}
    {what sel : UInt256} {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    (hperm : I.perm = true)
    (h : RD endBytecode I g s0 endFileUintEventPc
      [endFileUintData I, what, endRelyReturnPc, sel]
      (endRelyAuthHashMem I) (UInt256.ofNat 3) ByteArray.empty acc k C) :
    RDret endBytecode g s0 acc ByteArray.empty := by
  have rd1581pre := evm_run h with [
    raw jumpdest (by native_decide) (by evm_ov),
    raw push1 ⟨64⟩ (by native_decide) (by evm_ov),
    raw dup1 (by native_decide) (by evm_ov),
    raw mload 0 ⟨128⟩ (UInt256.ofNat 3) (by native_decide)
      mem_cost
      (mloadFreePtrValue (by rw [endRelyAuthHashMem_size I]; decide) (by decide)
        (endRelyAuthHashMem_read64 I))
      (by native_decide) (by evm_ov),
    raw dup3 (by native_decide) (by evm_ov),
    raw dup2 (by native_decide) (by evm_ov)]
  have rd1583 := rd1581pre.mstore 6 (endFileUintLogDataMem I)
    (UInt256.ofNat 5) (by native_decide) mem_cost (by rfl) (by native_decide)
    (by evm_ov)
  have rd1587pre := evm_run rd1583 with [
    raw swap1 (by native_decide) (by evm_ov),
    raw mload 0 ⟨128⟩ (UInt256.ofNat 5) (by native_decide)
      mem_cost
      (mloadFreePtrValue (by rw [endFileUintLogDataMem_size I]; decide) (by decide)
        (endFileUintLogDataMem_read64 I))
      (by native_decide) (by evm_ov),
    raw dup4 (by native_decide) (by evm_ov),
    raw swap2 (by native_decide) (by evm_ov)]
  have rd1621 := rd1587pre.pushConst
    (⟨0xe986e40cc8c151830d4f61050f4fb2e4add8567caad2d5f5496f9158e91fe4c7⟩ :
      UInt256)
    (width := 32) (op := .PUSH32) (by decide) (by native_decide) (by evm_ov)
  have rd1630pre := evm_run rd1621 with [
    raw swap2 (by native_decide) (by evm_ov),
    raw swap1 (by native_decide) (by evm_ov),
    raw dup2 (by native_decide) (by evm_ov),
    raw swap1 (by native_decide) (by evm_ov),
    raw sub (by native_decide) (by evm_ov),
    raw push1 ⟨32⟩ (by native_decide) (by evm_ov),
    raw add (by native_decide) (by evm_ov),
    raw swap1 (by native_decide) (by evm_ov)]
  have rd1631 := RD.log2
    (a := ⟨128⟩) (b := ⟨32⟩)
    (c := ⟨0xe986e40cc8c151830d4f61050f4fb2e4add8567caad2d5f5496f9158e91fe4c7⟩)
    (d := what)
    (t := [endFileUintData I, what, endRelyReturnPc, sel])
    0
    (UInt256.ofNat
      (MachineState.M (UInt256.ofNat 5).toNat (⟨128⟩ : UInt256).toNat
        (⟨32⟩ : UInt256).toNat))
    rd1630pre (by native_decide) hperm mem_cost (by native_decide)
    (by simp only [List.length_cons, List.length_nil]; omega)
  have rd1632 := RD.pop (a := endFileUintData I) (t := [what, endRelyReturnPc, sel])
    rd1631 (by native_decide) (by evm_ov)
  have rd1633 := RD.pop (a := what) (t := [endRelyReturnPc, sel])
    rd1632 (by native_decide) (by evm_ov)
  have rd562 := RD.jump (a := endRelyReturnPc) (t := [sel]) rd1633
    (by native_decide) (by jump_dest) (by evm_ov)
  have rd563 := RD.jumpdest (pc := endRelyReturnPc) (stk := [sel]) rd562
    (by native_decide) (by evm_ov)
  exact RD.stop rd563 (by native_decide) (by evm_ov)

set_option maxHeartbeats 3000000 in
theorem endFileUintX_wait_ok {cA σ I} {g : Sat256} {s0 : State} {k C : ℕ}
    {sel : UInt256} (hperm : I.perm = true)
    (hwhatWord : calldataWord I.calldata 4 = ABI.bytesToWord endFileUintWaitBytes)
    (h : RD endBytecode I g s0 endFileUintSwitchPc
      [endFileUintData I, calldataWord I.calldata 4, endRelyReturnPc, sel]
      (endRelyAuthHashMem I) (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    RDret endBytecode g s0
      (cA, sstoreAccountMap I.codeOwner σ ⟨10⟩ (endFileUintData I)) ByteArray.empty := by
  have rd1476pre := evm_run h with [
    raw jumpdest (by native_decide) (by evm_ov),
    raw dup2 (by native_decide) (by evm_ov)]
  have rd1481 := rd1476pre.pushConst (⟨0x1dd85a5d⟩ : UInt256)
    (width := 4) (op := .PUSH4) (by decide) (by native_decide) (by evm_ov)
  have rd1484pre := evm_run rd1481 with [
    raw push1 ⟨226⟩ (by native_decide) (by evm_ov),
    raw shl (by native_decide) (by evm_ov),
    raw eq (by native_decide) (by evm_ov)]
  rw [hwhatWord, endFileUintWaitBytes_word, u256_eq_refl] at rd1484pre
  have rd1490pre := evm_run rd1484pre with [
    raw iszero (by native_decide) (by evm_ov),
    raw push2 endFileUintUnrecognizedPc (by native_decide) (by evm_ov),
    raw jumpiNT (by native_decide) rfl (by evm_ov)]
  have rd1494pre := evm_run rd1490pre with [
    raw push1 ⟨10⟩ (by native_decide) (by evm_ov),
    raw dup2 (by native_decide) (by evm_ov),
    raw swap1 (by native_decide) (by evm_ov)]
  obtain ⟨k1495, C1495, rd1495raw⟩ := rd1494pre.sstore hperm (by native_decide)
    (by simp only [List.length_cons, List.length_nil]; omega)
  have rd1495 : RD endBytecode I g s0 ⟨1495⟩
      [endFileUintData I,
        UInt256.shiftLeft (⟨0x1dd85a5d⟩ : UInt256) ⟨226⟩, endRelyReturnPc, sel]
      (endRelyAuthHashMem I) (UInt256.ofNat 3) ByteArray.empty
      (cA, sstoreAccountMap I.codeOwner σ ⟨10⟩ (endFileUintData I)) k1495 C1495 := by
    simpa using rd1495raw
  have rd1576 := evm_run rd1495 with [
    raw push2 endFileUintEventPc (by native_decide) (by evm_ov),
    raw jump (by native_decide) (by jump_dest) (by evm_ov)]
  exact endFileUintX_logReturn hperm rd1576

abbrev endFileUintUnrecognizedRawWord : UInt256 :=
  ⟨0x456e642f66696c652d756e7265636f676e697a65642d706172616d0000000000⟩

theorem RD.endFileUintUnrecognizedRevert {g : Sat256} {s0 : State} {ee : ExecutionEnv}
    {k C : ℕ} {stk : List UInt256} {mem rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    (h : RD endBytecode ee g s0 endFileUintUnrecognizedPc stk mem (UInt256.ofNat 3) rdata
      acc k C)
    (hmem : mem.size = 96)
    (hread64 : mem.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩)
    (hov : stk.length + 5 ≤ 1024) :
    RDrev endBytecode g s0 := by
  have rdMload := evm_run h with [
    raw jumpdest (by native_decide) (by evm_ov),
    raw push1 ⟨64⟩ (by native_decide) (by evm_ov),
    raw dup1 (by native_decide) (by evm_ov),
    raw mload 0 ⟨128⟩ (UInt256.ofNat 3) (by native_decide)
      mem_cost
      (mloadFreePtrValue (by rw [hmem]; decide) (by decide) hread64)
      (by decide) (by evm_ov)]
  have rdSelectorRaw := rdMload.pushConst (⟨4594637⟩ : UInt256)
    (width := 3) (op := .PUSH3) (by decide) (by native_decide)
    (by simp only [List.length_cons]; omega)
  have rdPrefix := evm_run rdSelectorRaw with [
    raw push1 ⟨229⟩ (by native_decide) (by evm_ov),
    raw shl (by native_decide) (by evm_ov),
    raw dup2 (by native_decide) (by evm_ov),
    raw mstore 6 (solcErrorStringMem0 mem) (UInt256.ofNat 5)
      (by native_decide) mem_cost (by rfl) (by decide) (by evm_ov),
    raw push1 ⟨32⟩ (by native_decide) (by evm_ov),
    raw push1 ⟨4⟩ (by native_decide) (by evm_ov),
    raw dup3 (by native_decide) (by evm_ov),
    raw add (by native_decide) (by evm_ov),
    raw mstore 3 (solcErrorStringMem1 mem) (UInt256.ofNat 6)
      (by native_decide) mem_cost (by rfl) (by decide) (by evm_ov),
    raw push1 ⟨27⟩ (by native_decide) (by evm_ov),
    raw push1 ⟨36⟩ (by native_decide) (by evm_ov),
    raw dup3 (by native_decide) (by evm_ov),
    raw add (by native_decide) (by evm_ov),
    raw mstore 3 (solcErrorStringMem2 ⟨27⟩ mem)
      (UInt256.ofNat 7) (by native_decide) mem_cost (by rfl) (by decide) (by evm_ov)]
  have rdRaw := rdPrefix.pushConst endFileUintUnrecognizedRawWord
    (width := 32) (op := .PUSH32) (by decide) (by native_decide)
    (by simp only [List.length_cons]; omega)
  exact evm_run rdRaw with [
    raw push1 ⟨68⟩ (by native_decide) (by evm_ov),
    raw dup3 (by native_decide) (by evm_ov),
    raw add (by native_decide) (by evm_ov),
    raw mstore 3 (solcErrorStringMem3 ⟨27⟩ endFileUintUnrecognizedRawWord mem)
      (UInt256.ofNat 8) (by native_decide) mem_cost (by rfl) (by decide) (by evm_ov),
    raw swap1 (by native_decide) (by evm_ov),
    raw mload 0 ⟨128⟩ (UInt256.ofNat 8) (by native_decide)
      mem_cost
      (solcErrorStringMem3_mload64 ⟨27⟩ endFileUintUnrecognizedRawWord hmem hread64)
      (by decide) (by evm_ov),
    raw swap1 (by native_decide) (by evm_ov),
    raw dup2 (by native_decide) (by evm_ov),
    raw swap1 (by native_decide) (by evm_ov),
    raw sub (by native_decide) (by evm_ov),
    raw push1 ⟨100⟩ (by native_decide) (by evm_ov),
    raw add (by native_decide) (by evm_ov),
    raw swap1 (by native_decide) (by evm_ov),
    raw rev 0 (by native_decide) mem_cost (by evm_ov)]

set_option maxHeartbeats 3000000 in
theorem endFileUintX_unrecognized {cA σ I} {g : Sat256} {s0 : State} {k C : ℕ}
    {sel : UInt256}
    (hnotWaitWord : calldataWord I.calldata 4 ≠ ABI.bytesToWord endFileUintWaitBytes)
    (h : RD endBytecode I g s0 endFileUintSwitchPc
      [endFileUintData I, calldataWord I.calldata 4, endRelyReturnPc, sel]
      (endRelyAuthHashMem I) (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    RDrev endBytecode g s0 := by
  have rd1476pre := evm_run h with [
    raw jumpdest (by native_decide) (by evm_ov),
    raw dup2 (by native_decide) (by evm_ov)]
  have rd1481 := rd1476pre.pushConst (⟨0x1dd85a5d⟩ : UInt256)
    (width := 4) (op := .PUSH4) (by decide) (by native_decide) (by evm_ov)
  have rd1484pre := evm_run rd1481 with [
    raw push1 ⟨226⟩ (by native_decide) (by evm_ov),
    raw shl (by native_decide) (by evm_ov),
    raw eq (by native_decide) (by evm_ov)]
  have hwaitEq :
      UInt256.eq
          (UInt256.shiftLeft (⟨0x1dd85a5d⟩ : UInt256) ⟨226⟩)
          (calldataWord I.calldata 4) = ⟨0⟩ := by
    rw [← endFileUintWaitBytes_word]
    exact u256_eq_of_ne (by intro hbad; exact hnotWaitWord hbad.symm)
  rw [hwaitEq] at rd1484pre
  have rd1499 := evm_run rd1484pre with [
    raw iszero (by native_decide) (by evm_ov),
    raw push2 endFileUintUnrecognizedPc (by native_decide) (by evm_ov),
    raw jumpiT (by native_decide) one_ne_zero_uint (by jump_dest) (by evm_ov)]
  exact RD.endFileUintUnrecognizedRevert rd1499
    (endRelyAuthHashMem_size I) (endRelyAuthHashMem_read64 I)
    (by simp only [List.length_cons, List.length_nil]; omega)

theorem endFileUintBody {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256}
    (hcode : I.code = endBytecode) (hsize : I.calldata.size < UInt256.size)
    (hperm : I.perm = true) (hwv : I.weiValue = ⟨0⟩)
    (hsel : selIs I (selectorOf fileUintTransition))
    (hAccounts : accountMapEquiv σ_evm σ_solm) :
    runtimeEquivalenceFor config contract cA gh bl σ_evm σ_solm σ₀ g A I := by
  have hsel' : selIs I endFileUintConcreteSelector := by
    simpa [endFileUintSelectorBytes, endFileUintConcreteSelector] using hsel
  have hsz4 : 4 ≤ I.calldata.size :=
    calldata_size_ge_of_selIs I endFileUintConcreteSelector (by rfl) hsel'
  have hdispatch : dispatchMsg contract I.calldata = some fileUintTransition :=
    endDispatchFileUint hsel
  have hreach := endReachFileUintBody (cA := cA) (gh := gh) (bl := bl)
    (σ := σ_evm) (σ₀ := σ₀) (A := A) (I := I) (g := Sat256.ofUInt256 g)
    hcode hwv hsz4 hsize hsel'
  by_cases hsz68 : 68 ≤ I.calldata.size
  · have hdecode := endDecode_fileUint_ok (I := I) hsz68
    obtain ⟨_, _, hdecoded⟩ :=
      endFileUintX_decoded (g := Sat256.ofUInt256 g) hsz68 hsize hreach
    let evmSolm := initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I
    have hauthCouple : endRelyAuthWord σ_evm I = endRelyAuthWord σ_solm I :=
      accountMapEquiv_storage_findD hAccounts I.codeOwner (endRelyAuthStorageSlot I) ⟨0⟩
    by_cases hauth : endRelyAuthWord σ_evm I = ⟨1⟩
    · have hauthSolm : endRelyAuthWord σ_solm I = ⟨1⟩ := by
        rw [← hauthCouple]
        exact hauth
      obtain ⟨_, _, hauthPc⟩ := endFileUintX_authorized (I := I) hauth hdecoded
      have hliveCouple : endSlotWord ⟨8⟩ σ_evm I = endSlotWord ⟨8⟩ σ_solm I :=
        accountMapEquiv_storage_findD hAccounts I.codeOwner ⟨8⟩ ⟨0⟩
      by_cases hlive : endSlotWord ⟨8⟩ σ_evm I = ⟨1⟩
      · have hliveSolm : endSlotWord ⟨8⟩ σ_solm I = ⟨1⟩ := by
          rw [← hliveCouple]
          exact hlive
        obtain ⟨_, _, hswitch⟩ := endFileUintX_live (I := I) hlive hauthPc
        have hsz36 : 36 ≤ I.calldata.size := by omega
        by_cases hwait : endFileUintWhat I = endFileUintWaitBytes
        · have hwaitWord :
              calldataWord I.calldata 4 = ABI.bytesToWord endFileUintWaitBytes := by
            rw [← endFileUintWhatWord_eq (I := I) hsz36, hwait]
          have hbody :
              ExecTransitionBody config contract evmSolm (endFileUintLocals I)
                fileUintTransition.body
                (.returned { contract := contract, locals := endFileUintLocals I }
                  (endFileUintPostState evmSolm I) none) := by
            simpa [evmSolm] using
              endFileUintSourceWaitOk (cA := cA) (gh := gh) (bl := bl)
                (σ := σ_solm) (σ₀ := σ₀) (A := A) (I := I) (g := g)
                hwv hauthSolm hliveSolm hwait
          exact (endFileUintX_wait_ok hperm hwaitWord hswitch)
            |>.reEquivExecutionGenAccountMapEquiv hcode hdispatch hdecode hbody
              (by simp [endFileUintPostState, evmSolm, initState, storageStore_createdAccounts])
              (by
                simpa [endFileUintPostState, evmSolm, initState, storageStore_accountMap] using
                  accountMapEquiv_sstoreAccountMap I.codeOwner ⟨10⟩ (endFileUintData I)
                    hAccounts)
              (by
                simpa [fileUintTransition] using
                  (returnEquiv.fallthrough (o := ByteArray.empty) (r := none) (t := [])
                    (dvs := []) rfl (by native_decide) (by native_decide)))
        · have hnotWaitWord :
              calldataWord I.calldata 4 ≠ ABI.bytesToWord endFileUintWaitBytes :=
            endFileUintWhatWord_ne_of_bytes_ne hsz36 hwait endFileUintWaitBytes_length
          have hbody :
              ExecTransitionBody config contract evmSolm (endFileUintLocals I)
                fileUintTransition.body .reverted := by
            simpa [evmSolm] using
              endFileUintSourceUnrecognizedReverts
                (cA := cA) (gh := gh) (bl := bl) (σ := σ_solm) (σ₀ := σ₀)
                (A := A) (I := I) (g := g) hwv hauthSolm hliveSolm hwait
          exact (endFileUintX_unrecognized hnotWaitWord hswitch)
            |>.reEquivExecutionRevert hcode hdispatch hdecode hbody
      · have hliveSolm : endSlotWord ⟨8⟩ σ_solm I ≠ ⟨1⟩ := by
          intro hbad
          exact hlive (by rw [hliveCouple, hbad])
        have hbody :
            ExecTransitionBody config contract evmSolm (endFileUintLocals I)
              fileUintTransition.body .reverted := by
          simpa [evmSolm] using
            endFileUintSourceLiveReverts
              (cA := cA) (gh := gh) (bl := bl) (σ := σ_solm) (σ₀ := σ₀)
              (A := A) (I := I) (g := g) hwv hauthSolm hliveSolm
        exact (endFileUintX_notLive (I := I) hlive hauthPc)
          |>.reEquivExecutionRevert hcode hdispatch hdecode hbody
    · have hauthSolm : endRelyAuthWord σ_solm I ≠ ⟨1⟩ := by
        intro hbad
        exact hauth (by rw [hauthCouple, hbad])
      have hbody :
          ExecTransitionBody config contract evmSolm (endFileUintLocals I)
            fileUintTransition.body .reverted := by
        simpa [evmSolm] using
          endFileUintSourceAuthReverts
            (cA := cA) (gh := gh) (bl := bl) (σ := σ_solm) (σ₀ := σ₀)
            (A := A) (I := I) (g := g) hwv hauthSolm
      exact (endFileUintX_unauthorized (I := I) hauth hdecoded)
        |>.reEquivExecutionRevert hcode hdispatch hdecode hbody
  · exact (endFileUintX_shortarg (g := Sat256.ofUInt256 g) hsz4 hsize (by omega) hreach)
      |>.reEquivDecodingFailed hcode hdispatch
        (endDecode_fileUint_none_short hsz4 (by omega))

end Benchmarks.Dss.End
