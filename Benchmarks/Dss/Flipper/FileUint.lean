import Benchmarks.Dss.Flipper.Dispatch

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

set_option maxRecDepth 2000000
set_option maxHeartbeats 0

namespace Benchmarks.Dss.Flipper

/-! ## `file(bytes32,uint256)` -/

abbrev fileUintWhat (I : ExecutionEnv) : List UInt8 :=
  (I.calldata.toList.drop 4).take 32

abbrev fileUintData (I : ExecutionEnv) : UInt256 :=
  calldataWord I.calldata 36

abbrev fileUintData48 (I : ExecutionEnv) : UInt256 :=
  UInt256.land (fileUintData I) uint48Mask

abbrev fileUintBegBytes : List UInt8 := [98, 101, 103] ++ zeroPad29
abbrev fileUintTtlBytes : List UInt8 := [116, 116, 108] ++ zeroPad29
abbrev fileUintTauBytes : List UInt8 := [116, 97, 117] ++ zeroPad29

abbrev fileUintLocals (I : ExecutionEnv) : Store :=
  ((∅ : Store).insert "what" (.fixedBytes bytes32Width (fileUintWhat I))).insert
    "data" (.int (Int.ofNat (fileUintData I).toNat))

theorem fileUintWhat_length {I : ExecutionEnv} (hsz36 : 36 ≤ I.calldata.size) :
    (fileUintWhat I).length = 32 := by
  simp [fileUintWhat, List.length_take, List.length_drop, byteArray_toList_eq]
  omega

theorem fileUintBegBytes_length : fileUintBegBytes.length = 32 := by
  native_decide

theorem fileUintTtlBytes_length : fileUintTtlBytes.length = 32 := by
  native_decide

theorem fileUintTauBytes_length : fileUintTauBytes.length = 32 := by
  native_decide

theorem fileUintBegBytes_word :
    ABI.bytesToWord fileUintBegBytes =
      UInt256.shiftLeft (⟨6448487⟩ : UInt256) ⟨232⟩ := by
  native_decide

theorem fileUintTtlBytes_word :
    ABI.bytesToWord fileUintTtlBytes =
      UInt256.shiftLeft (⟨1907995⟩ : UInt256) ⟨234⟩ := by
  native_decide

theorem fileUintTauBytes_word :
    ABI.bytesToWord fileUintTauBytes =
      UInt256.shiftLeft (⟨7627125⟩ : UInt256) ⟨232⟩ := by
  native_decide

theorem fileUintWhatWord_eq {I : ExecutionEnv} (hsz36 : 36 ≤ I.calldata.size) :
    ABI.bytesToWord (fileUintWhat I) = calldataWord I.calldata 4 := by
  simpa [fileUintWhat] using decode_word_at_eq I.calldata 4 (by omega) (by norm_num)

theorem fileUintWhatWord_eq_of_bytes_eq {I : ExecutionEnv} {bs : List UInt8}
    (hsz36 : 36 ≤ I.calldata.size) (hbs : fileUintWhat I = bs) :
    calldataWord I.calldata 4 = ABI.bytesToWord bs := by
  rw [← hbs]
  exact (fileUintWhatWord_eq (I := I) hsz36).symm

theorem fileUintWhat_eq_of_word_eq {I : ExecutionEnv} {bs : List UInt8}
    (hsz36 : 36 ≤ I.calldata.size) (hword : calldataWord I.calldata 4 = ABI.bytesToWord bs)
    (hbsLen : bs.length = 32) :
    fileUintWhat I = bs := by
  have hto := toBytesBE_bytesToWord_of_length (bs := fileUintWhat I)
    (fileUintWhat_length (I := I) hsz36)
  rw [fileUintWhatWord_eq (I := I) hsz36, hword] at hto
  exact hto.symm.trans (toBytesBE_bytesToWord_of_length (bs := bs) hbsLen)

theorem fileUintWhatWord_ne_of_bytes_ne {I : ExecutionEnv} {bs : List UInt8}
    (hsz36 : 36 ≤ I.calldata.size) (hneq : fileUintWhat I ≠ bs)
    (hbsLen : bs.length = 32) :
    calldataWord I.calldata 4 ≠ ABI.bytesToWord bs := by
  intro hword
  exact hneq (fileUintWhat_eq_of_word_eq hsz36 hword hbsLen)

theorem decodeABIValues_bytes32_uint256_legacy_ok {bytes : List UInt8}
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

theorem decodeABIValues_bytes32_uint256_legacy_none_short {bytes : List UInt8}
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

theorem decodeCalldata_legacyBytes32_uint256_ok {cd : ByteArray} {x y : Solm.Ident}
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
  rw [decodeABIValues_bytes32_uint256_legacy_ok (bytes := cd.toList.drop 4)
    (by simpa using htake4)
    (by simpa [List.drop_drop, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using htake36)]
  rw [if_neg (by rw [List.length_drop, htlen]; omega : ¬ (cd.toList.drop 4).length < 64)]
  simp [decodeCalldata.insertValues]
  rw [hword36]

theorem decodeCalldata_legacyBytes32_uint256_none_short {cd : ByteArray}
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
    rw [decodeABIValues_bytes32_uint256_legacy_none_short (bytes := cd.toList.drop 4) (by
      rw [List.length_drop, htlen]
      omega)]

theorem flipperDecode_fileUint_ok {I : ExecutionEnv} (hsz68 : 68 ≤ I.calldata.size) :
    decodeCalldataWithMode config.abiDecodeMode (fileUintTransition.params.map Param.name)
      (transitionSignature fileUintTransition).paramTypes I.calldata =
        some (fileUintLocals I) := by
  simpa [config, fileUintTransition, bytes32, bytes32Width, uint256, uint256Int,
    fileUintLocals, fileUintWhat, fileUintData, abiBytes32, abiBytes32Width, abiUInt256] using
    (decodeCalldata_legacyBytes32_uint256_ok (cd := I.calldata) (x := "what")
      (y := "data") hsz68)

theorem flipperDecode_fileUint_none_short {I : ExecutionEnv}
    (hsz4 : 4 ≤ I.calldata.size) (hshort : I.calldata.size < 68) :
    decodeCalldataWithMode config.abiDecodeMode (fileUintTransition.params.map Param.name)
      (transitionSignature fileUintTransition).paramTypes I.calldata = none := by
  simpa [config, fileUintTransition, bytes32, bytes32Width, uint256, uint256Int, abiBytes32,
    abiBytes32Width, abiUInt256] using
    (decodeCalldata_legacyBytes32_uint256_none_short (cd := I.calldata) (x := "what")
      (y := "data") hsz4 hshort)

theorem fileUintLocals_get_what (I : ExecutionEnv) :
    (fileUintLocals I).get? "what" =
      some (.fixedBytes bytes32Width (fileUintWhat I)) := by
  rw [fileUintLocals, store_get_ne _ _ (by decide), store_get_self]

theorem fileUintLocals_get_data (I : ExecutionEnv) :
    (fileUintLocals I).get? "data" =
      some (.int (Int.ofNat (fileUintData I).toNat)) := by
  rw [fileUintLocals, store_get_self]

theorem fileUintLocals_get_wards (I : ExecutionEnv) :
    (fileUintLocals I).get? "wards" = none := by
  rw [fileUintLocals, store_get_ne _ _ (by decide), store_get_ne _ _ (by decide)]
  simp

theorem fileUintLocals_get_beg (I : ExecutionEnv) :
    (fileUintLocals I).get? "beg" = none := by
  rw [fileUintLocals, store_get_ne _ _ (by decide), store_get_ne _ _ (by decide)]
  simp

theorem fileUintLocals_get_ttl (I : ExecutionEnv) :
    (fileUintLocals I).get? "ttl" = none := by
  rw [fileUintLocals, store_get_ne _ _ (by decide), store_get_ne _ _ (by decide)]
  simp

theorem fileUintLocals_get_tau (I : ExecutionEnv) :
    (fileUintLocals I).get? "tau" = none := by
  rw [fileUintLocals, store_get_ne _ _ (by decide), store_get_ne _ _ (by decide)]
  simp

theorem evalExpr_fileUintData {evm : EVM.State} {I : ExecutionEnv} {locals : Store}
    (h : locals.get? "data" = some (.int (Int.ofNat (fileUintData I).toNat))) :
    evalExpr? config { contract := contract, locals := locals } evm (.var "data") =
      .ok (.int (Int.ofNat (fileUintData I).toNat)) := by
  rw [evalExpr?]
  change EvalResult.ofOption EvalError.unboundVariable (locals.get? "data") =
    .ok (.int (Int.ofNat (fileUintData I).toNat))
  rw [h]
  rfl

theorem evalExpr_fileUintDataWrap48 {evm : EVM.State} {I : ExecutionEnv} {locals : Store}
    (h : locals.get? "data" = some (.int (Int.ofNat (fileUintData I).toNat))) :
    evalExpr? config { contract := contract, locals := locals } evm (wrap48 (.var "data")) =
      .ok (.int (Int.ofNat (fileUintData48 I).toNat)) := by
  have hdata := evalExpr_fileUintData (evm := evm) (I := I) (locals := locals) h
  rw [wrap48, evalExpr?]
  simp only [hdata, EvalResult.bind, bind]
  rw [show evalExpr? config { contract := contract, locals := locals } evm
      (.intLit uint48Modulus) = .ok (.int uint48Modulus) by simp [evalExpr?, pure]]
  change evalBinaryOp? BinaryOp.mod (Value.int (Int.ofNat (fileUintData I).toNat))
      (Value.int uint48Modulus) = .ok (Value.int (Int.ofNat (fileUintData48 I).toNat))
  have hmod :
      (Int.ofNat (fileUintData I).toNat) % uint48Modulus =
        Int.ofNat (fileUintData48 I).toNat := by
    calc
      (Int.ofNat (fileUintData I).toNat) % uint48Modulus =
          Int.ofNat ((fileUintData I).toNat % 2 ^ 48) := by
          rw [uint48Modulus]
          exact (Int.natCast_mod (fileUintData I).toNat (2 ^ 48)).symm
      _ = Int.ofNat (fileUintData48 I).toNat := by
          rw [← uint48Mask_toNat_mod (fileUintData I)]
  change (if uint48Modulus = 0 then EvalResult.revert else
      .ok (Value.int ((Int.ofNat (fileUintData I).toNat) % uint48Modulus))) =
    .ok (Value.int (Int.ofNat (fileUintData48 I).toNat))
  rw [if_neg (by norm_num [uint48Modulus]), hmod]
  all_goals decide

theorem evalExpr_fileUintWhatEq_true {evm : EVM.State} {I : ExecutionEnv} {locals : Store}
    {bs : List UInt8}
    (hget : locals.get? "what" = some (.fixedBytes bytes32Width (fileUintWhat I)))
    (hwhat : fileUintWhat I = bs) :
    evalExpr? config { contract := contract, locals := locals } evm
      (.binary .eq (.var "what") (.fixedBytesLit bytes32Width bs)) = .ok (.bool true) := by
  have hvar :
      evalExpr? config { contract := contract, locals := locals } evm (.var "what") =
        .ok (.fixedBytes bytes32Width (fileUintWhat I)) := by
    rw [evalExpr?]
    change EvalResult.ofOption EvalError.unboundVariable (locals.get? "what") =
      .ok (.fixedBytes bytes32Width (fileUintWhat I))
    rw [hget]
    rfl
  rw [evalExpr?]
  simp only [hvar, EvalResult.bind, bind]
  simp [evalExpr?, evalBinaryOp?, hwhat]
  all_goals decide

theorem evalExpr_fileUintWhatEq_false {evm : EVM.State} {I : ExecutionEnv} {locals : Store}
    {bs : List UInt8}
    (hget : locals.get? "what" = some (.fixedBytes bytes32Width (fileUintWhat I)))
    (hwhat : fileUintWhat I ≠ bs) :
    evalExpr? config { contract := contract, locals := locals } evm
      (.binary .eq (.var "what") (.fixedBytesLit bytes32Width bs)) = .ok (.bool false) := by
  have hvar :
      evalExpr? config { contract := contract, locals := locals } evm (.var "what") =
        .ok (.fixedBytes bytes32Width (fileUintWhat I)) := by
    rw [evalExpr?]
    change EvalResult.ofOption EvalError.unboundVariable (locals.get? "what") =
      .ok (.fixedBytes bytes32Width (fileUintWhat I))
    rw [hget]
    rfl
  rw [evalExpr?]
  simp only [hvar, EvalResult.bind, bind]
  simp [evalExpr?, evalBinaryOp?, hwhat]
  all_goals decide

theorem assign_fileUintBegStorage (evm : EVM.State) (I : ExecutionEnv) :
    let evm' := Solm.EVM.storageStore evm evm.executionEnv.codeOwner ⟨4⟩ (fileUintData I)
    assignStorageRef? config { contract := contract, locals := fileUintLocals I } evm
      .storage begRef (.int (Int.ofNat (fileUintData I).toNat)) =
        .ok ({ contract := contract, locals := fileUintLocals I }, evm') := by
  intro evm'
  apply assignStorageRef_storage_scalar
      (ty := uint256St)
      (er := ({ base := "beg", steps := [] } : EvaledStorageRef))
      (loc := wordLoc ⟨4⟩)
      (hbase := fileUintLocals_get_beg I)
      (her := by simp [begRef, evalStorageRef, evalStorageRefSteps, EvalResult.bind, pure, bind])
      (hty := by simp [storageTypeAt?, contract, storageDecls, uint256St])
      (hloc := by rfl)
  simpa [evm'] using flipperStorageLocStore_uint256 evm ⟨4⟩ (fileUintData I)

theorem assign_fileUintTtlStorage (evm : EVM.State) (I : ExecutionEnv) :
    let evm' := Solm.EVM.storageStore evm evm.executionEnv.codeOwner ⟨5⟩
      (setUint48Offset0Word (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨5⟩)
        (fileUintData48 I))
    assignStorageRef? config { contract := contract, locals := fileUintLocals I } evm
      .storage ttlRef (.int (Int.ofNat (fileUintData48 I).toNat)) =
        .ok ({ contract := contract, locals := fileUintLocals I }, evm') := by
  intro evm'
  apply assignStorageRef_storage_scalar
      (ty := uint48St)
      (er := ({ base := "ttl", steps := [] } : EvaledStorageRef))
      (loc := uint48Loc ⟨5⟩ ⟨0, by decide⟩ (by decide))
      (hbase := fileUintLocals_get_ttl I)
      (her := by simp [ttlRef, evalStorageRef, evalStorageRefSteps, EvalResult.bind, pure, bind])
      (hty := by simp [storageTypeAt?, contract, storageDecls, uint48St])
      (hloc := by rfl)
  simpa [evm', fileUintData48] using
    flipperStorageLocStore_uint48_offset0 evm ⟨5⟩ (fileUintData48 I)
      (uint48Mask_bound (fileUintData I))

theorem assign_fileUintTauStorage (evm : EVM.State) (I : ExecutionEnv) :
    let evm' := Solm.EVM.storageStore evm evm.executionEnv.codeOwner ⟨5⟩
      (setUint48Offset6Word (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨5⟩)
        (fileUintData48 I))
    assignStorageRef? config { contract := contract, locals := fileUintLocals I } evm
      .storage tauRef (.int (Int.ofNat (fileUintData48 I).toNat)) =
        .ok ({ contract := contract, locals := fileUintLocals I }, evm') := by
  intro evm'
  apply assignStorageRef_storage_scalar
      (ty := uint48St)
      (er := ({ base := "tau", steps := [] } : EvaledStorageRef))
      (loc := uint48Loc ⟨5⟩ ⟨6, by decide⟩ (by decide))
      (hbase := fileUintLocals_get_tau I)
      (her := by simp [tauRef, evalStorageRef, evalStorageRefSteps, EvalResult.bind, pure, bind])
      (hty := by simp [storageTypeAt?, contract, storageDecls, uint48St])
      (hloc := by rfl)
  simpa [evm', fileUintData48] using
    flipperStorageLocStore_uint48_offset6 evm ⟨5⟩ (fileUintData48 I)
      (uint48Mask_bound (fileUintData I))

theorem flipperFileUintSourceBodyBeg {cA gh bl σ σ₀ A I} {g : UInt256}
    (hwv : I.weiValue = ⟨0⟩)
    (hauth : flipperSlotWord (flipperCallerWardsSlot I) σ I = ⟨1⟩)
    (hwhat : fileUintWhat I = fileUintBegBytes) :
    let locals := fileUintLocals I
    let evm0 := initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I
    let evm1 := Solm.EVM.storageStore evm0 I.codeOwner ⟨4⟩ (fileUintData I)
    ExecTransitionBody config contract evm0 locals fileUintTransition.body
      (.returned { contract := contract, locals := locals } evm1 none) := by
  intro locals evm0 evm1
  have hguard :
      evalExpr? config { contract := contract, locals := locals } evm0
        (.binary .eq (.storage (wardsRef sender)) (.intLit 1)) = .ok (.bool true) := by
    simpa [locals, evm0] using
      flipperAuthGuardEval_true (cA := cA) (gh := gh) (bl := bl) (σ := σ)
        (σ₀ := σ₀) (A := A) (I := I) (g := Sat256.ofUInt256 g) (locals := locals)
        (by simp [locals]) hauth
  have hbeg :
      evalExpr? config { contract := contract, locals := locals } evm0
        (.binary .eq (.var "what") begParamLit) = .ok (.bool true) := by
    simpa [begParamLit, fileUintBegBytes] using
      (evalExpr_fileUintWhatEq_true (evm := evm0) (I := I) (locals := locals)
        (bs := fileUintBegBytes) (by simpa [locals] using fileUintLocals_get_what I)
        hwhat)
  have hdata :
      evalExpr? config { contract := contract, locals := locals } evm0 (.var "data") =
        .ok (.int (Int.ofNat (fileUintData I).toNat)) := by
    simpa [locals] using
      evalExpr_fileUintData (evm := evm0) (I := I) (locals := locals)
        (by simpa [locals] using fileUintLocals_get_data I)
  have hassign :
      assignStorageRef? config { contract := contract, locals := locals } evm0
        .storage begRef (.int (Int.ofNat (fileUintData I).toNat)) =
          .ok ({ contract := contract, locals := locals }, evm1) := by
    simpa [locals, evm1, evm0, initState] using assign_fileUintBegStorage evm0 I
  have hthen :
      ExecBlock config { contract := contract, locals := locals } evm0
        [.assign .storage begRef (.var "data")]
        (.ok { contract := contract, locals := locals } evm1) := by
    exact ExecBlock.consNormal (ExecStmt.assign hdata hassign) ExecBlock.nil
  have hblock :
      ExecBlock config { contract := contract, locals := locals } evm0
        fileUintTransition.body (.ok { contract := contract, locals := locals } evm1) := by
    refine ExecBlock.consNormal (ExecStmt.requireTrue ?_) ?_
    · exact evalCallvalueEq_true (by simp [evm0, initState]; exact hwv)
    refine ExecBlock.consNormal (ExecStmt.requireTrue hguard) ?_
    exact ExecBlock.consNormal (ExecStmt.iteTrue hbeg hthen) ExecBlock.nil
  simpa [ExecTransitionBody, locals, evm0, evm1] using ExecFuncBody.execBlockOK hblock

theorem flipperFileUintSourceBodyTtl {cA gh bl σ σ₀ A I} {g : UInt256}
    (hwv : I.weiValue = ⟨0⟩)
    (hauth : flipperSlotWord (flipperCallerWardsSlot I) σ I = ⟨1⟩)
    (hnotBeg : fileUintWhat I ≠ fileUintBegBytes)
    (hwhat : fileUintWhat I = fileUintTtlBytes) :
    let locals := fileUintLocals I
    let evm0 := initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I
    let evm1 := Solm.EVM.storageStore evm0 I.codeOwner ⟨5⟩
      (setUint48Offset0Word (Solm.EVM.storageLoad evm0 I.codeOwner ⟨5⟩)
        (fileUintData48 I))
    ExecTransitionBody config contract evm0 locals fileUintTransition.body
      (.returned { contract := contract, locals := locals } evm1 none) := by
  intro locals evm0 evm1
  have hguard :
      evalExpr? config { contract := contract, locals := locals } evm0
        (.binary .eq (.storage (wardsRef sender)) (.intLit 1)) = .ok (.bool true) := by
    simpa [locals, evm0] using
      flipperAuthGuardEval_true (cA := cA) (gh := gh) (bl := bl) (σ := σ)
        (σ₀ := σ₀) (A := A) (I := I) (g := Sat256.ofUInt256 g) (locals := locals)
        (by simp [locals]) hauth
  have hbeg :
      evalExpr? config { contract := contract, locals := locals } evm0
        (.binary .eq (.var "what") begParamLit) = .ok (.bool false) := by
    simpa [begParamLit, fileUintBegBytes] using
      (evalExpr_fileUintWhatEq_false (evm := evm0) (I := I) (locals := locals)
        (bs := fileUintBegBytes) (by simpa [locals] using fileUintLocals_get_what I)
        hnotBeg)
  have httl :
      evalExpr? config { contract := contract, locals := locals } evm0
        (.binary .eq (.var "what") ttlParamLit) = .ok (.bool true) := by
    simpa [ttlParamLit, fileUintTtlBytes] using
      (evalExpr_fileUintWhatEq_true (evm := evm0) (I := I) (locals := locals)
        (bs := fileUintTtlBytes) (by simpa [locals] using fileUintLocals_get_what I)
        hwhat)
  have hdata :
      evalExpr? config { contract := contract, locals := locals } evm0 (wrap48 (.var "data")) =
        .ok (.int (Int.ofNat (fileUintData48 I).toNat)) := by
    simpa [locals] using
      evalExpr_fileUintDataWrap48 (evm := evm0) (I := I) (locals := locals)
        (by simpa [locals] using fileUintLocals_get_data I)
  have hassign :
      assignStorageRef? config { contract := contract, locals := locals } evm0
        .storage ttlRef (.int (Int.ofNat (fileUintData48 I).toNat)) =
          .ok ({ contract := contract, locals := locals }, evm1) := by
    simpa [locals, evm1, evm0, initState, Solm.EVM.storageLoad] using
      assign_fileUintTtlStorage evm0 I
  have hthen :
      ExecBlock config { contract := contract, locals := locals } evm0
        [.assign .storage ttlRef (wrap48 (.var "data"))]
        (.ok { contract := contract, locals := locals } evm1) := by
    exact ExecBlock.consNormal (ExecStmt.assign hdata hassign) ExecBlock.nil
  have helse :
      ExecBlock config { contract := contract, locals := locals } evm0
        [.ite (.binary .eq (.var "what") ttlParamLit)
          [.assign .storage ttlRef (wrap48 (.var "data"))]
          [.ite (.binary .eq (.var "what") tauParamLit)
            [.assign .storage tauRef (wrap48 (.var "data"))]
            [.require (.boolLit false)]]]
        (.ok { contract := contract, locals := locals } evm1) := by
    exact ExecBlock.consNormal (ExecStmt.iteTrue httl hthen) ExecBlock.nil
  have hblock :
      ExecBlock config { contract := contract, locals := locals } evm0
        fileUintTransition.body (.ok { contract := contract, locals := locals } evm1) := by
    refine ExecBlock.consNormal (ExecStmt.requireTrue ?_) ?_
    · exact evalCallvalueEq_true (by simp [evm0, initState]; exact hwv)
    refine ExecBlock.consNormal (ExecStmt.requireTrue hguard) ?_
    exact ExecBlock.consNormal (ExecStmt.iteFalse hbeg helse) ExecBlock.nil
  simpa [ExecTransitionBody, locals, evm0, evm1] using ExecFuncBody.execBlockOK hblock

theorem flipperFileUintSourceBodyTau {cA gh bl σ σ₀ A I} {g : UInt256}
    (hwv : I.weiValue = ⟨0⟩)
    (hauth : flipperSlotWord (flipperCallerWardsSlot I) σ I = ⟨1⟩)
    (hnotBeg : fileUintWhat I ≠ fileUintBegBytes)
    (hnotTtl : fileUintWhat I ≠ fileUintTtlBytes)
    (hwhat : fileUintWhat I = fileUintTauBytes) :
    let locals := fileUintLocals I
    let evm0 := initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I
    let evm1 := Solm.EVM.storageStore evm0 I.codeOwner ⟨5⟩
      (setUint48Offset6Word (Solm.EVM.storageLoad evm0 I.codeOwner ⟨5⟩)
        (fileUintData48 I))
    ExecTransitionBody config contract evm0 locals fileUintTransition.body
      (.returned { contract := contract, locals := locals } evm1 none) := by
  intro locals evm0 evm1
  have hguard :
      evalExpr? config { contract := contract, locals := locals } evm0
        (.binary .eq (.storage (wardsRef sender)) (.intLit 1)) = .ok (.bool true) := by
    simpa [locals, evm0] using
      flipperAuthGuardEval_true (cA := cA) (gh := gh) (bl := bl) (σ := σ)
        (σ₀ := σ₀) (A := A) (I := I) (g := Sat256.ofUInt256 g) (locals := locals)
        (by simp [locals]) hauth
  have hbeg :
      evalExpr? config { contract := contract, locals := locals } evm0
        (.binary .eq (.var "what") begParamLit) = .ok (.bool false) := by
    simpa [begParamLit, fileUintBegBytes] using
      (evalExpr_fileUintWhatEq_false (evm := evm0) (I := I) (locals := locals)
        (bs := fileUintBegBytes) (by simpa [locals] using fileUintLocals_get_what I)
        hnotBeg)
  have httl :
      evalExpr? config { contract := contract, locals := locals } evm0
        (.binary .eq (.var "what") ttlParamLit) = .ok (.bool false) := by
    simpa [ttlParamLit, fileUintTtlBytes] using
      (evalExpr_fileUintWhatEq_false (evm := evm0) (I := I) (locals := locals)
        (bs := fileUintTtlBytes) (by simpa [locals] using fileUintLocals_get_what I)
        hnotTtl)
  have htau :
      evalExpr? config { contract := contract, locals := locals } evm0
        (.binary .eq (.var "what") tauParamLit) = .ok (.bool true) := by
    simpa [tauParamLit, fileUintTauBytes] using
      (evalExpr_fileUintWhatEq_true (evm := evm0) (I := I) (locals := locals)
        (bs := fileUintTauBytes) (by simpa [locals] using fileUintLocals_get_what I)
        hwhat)
  have hdata :
      evalExpr? config { contract := contract, locals := locals } evm0 (wrap48 (.var "data")) =
        .ok (.int (Int.ofNat (fileUintData48 I).toNat)) := by
    simpa [locals] using
      evalExpr_fileUintDataWrap48 (evm := evm0) (I := I) (locals := locals)
        (by simpa [locals] using fileUintLocals_get_data I)
  have hassign :
      assignStorageRef? config { contract := contract, locals := locals } evm0
        .storage tauRef (.int (Int.ofNat (fileUintData48 I).toNat)) =
          .ok ({ contract := contract, locals := locals }, evm1) := by
    simpa [locals, evm1, evm0, initState, Solm.EVM.storageLoad] using
      assign_fileUintTauStorage evm0 I
  have hthen :
      ExecBlock config { contract := contract, locals := locals } evm0
        [.assign .storage tauRef (wrap48 (.var "data"))]
        (.ok { contract := contract, locals := locals } evm1) := by
    exact ExecBlock.consNormal (ExecStmt.assign hdata hassign) ExecBlock.nil
  have htauElse :
      ExecBlock config { contract := contract, locals := locals } evm0
        [.ite (.binary .eq (.var "what") tauParamLit)
          [.assign .storage tauRef (wrap48 (.var "data"))]
          [.require (.boolLit false)]]
        (.ok { contract := contract, locals := locals } evm1) := by
    exact ExecBlock.consNormal (ExecStmt.iteTrue htau hthen) ExecBlock.nil
  have httlElse :
      ExecBlock config { contract := contract, locals := locals } evm0
        [.ite (.binary .eq (.var "what") ttlParamLit)
          [.assign .storage ttlRef (wrap48 (.var "data"))]
          [.ite (.binary .eq (.var "what") tauParamLit)
            [.assign .storage tauRef (wrap48 (.var "data"))]
            [.require (.boolLit false)]]]
        (.ok { contract := contract, locals := locals } evm1) := by
    exact ExecBlock.consNormal (ExecStmt.iteFalse httl htauElse) ExecBlock.nil
  have hblock :
      ExecBlock config { contract := contract, locals := locals } evm0
        fileUintTransition.body (.ok { contract := contract, locals := locals } evm1) := by
    refine ExecBlock.consNormal (ExecStmt.requireTrue ?_) ?_
    · exact evalCallvalueEq_true (by simp [evm0, initState]; exact hwv)
    refine ExecBlock.consNormal (ExecStmt.requireTrue hguard) ?_
    exact ExecBlock.consNormal (ExecStmt.iteFalse hbeg httlElse) ExecBlock.nil
  simpa [ExecTransitionBody, locals, evm0, evm1] using ExecFuncBody.execBlockOK hblock

theorem flipperFileUintSourceBodyAuthReverts {cA gh bl σ σ₀ A I} {g : UInt256}
    (hwv : I.weiValue = ⟨0⟩)
    (hauth : flipperSlotWord (flipperCallerWardsSlot I) σ I ≠ ⟨1⟩) :
    let locals := fileUintLocals I
    let evm0 := initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I
    ExecTransitionBody config contract evm0 locals fileUintTransition.body .reverted := by
  intro locals evm0
  have hguard :
      evalExpr? config { contract := contract, locals := locals } evm0
        (.binary .eq (.storage (wardsRef sender)) (.intLit 1)) = .ok (.bool false) := by
    simpa [locals, evm0] using
      flipperAuthGuardEval_false (cA := cA) (gh := gh) (bl := bl) (σ := σ)
        (σ₀ := σ₀) (A := A) (I := I) (g := Sat256.ofUInt256 g) (locals := locals)
        (by simp [locals]) hauth
  refine ExecFuncBody.execBlockRevert ?_
  simpa [fileUintTransition, nonpayable, auth] using
    nonpayableSecondRequireReverts
      (cfg := config)
      (solm := { contract := contract, locals := locals })
      (evm := evm0)
      (guard := .binary .eq (.storage (wardsRef sender)) (.intLit 1))
      (rest := [
        Stmt.ite (.binary .eq (.var "what") begParamLit)
          [Stmt.assign .storage begRef (.var "data")]
          [Stmt.ite (.binary .eq (.var "what") ttlParamLit)
            [Stmt.assign .storage ttlRef (wrap48 (.var "data"))]
            [Stmt.ite (.binary .eq (.var "what") tauParamLit)
              [Stmt.assign .storage tauRef (wrap48 (.var "data"))]
              [Stmt.require (.boolLit false)]]]])
      (by simp [evm0, initState]; exact hwv)
      hguard

theorem flipperFileUintSourceBodyUnrecognized {cA gh bl σ σ₀ A I} {g : UInt256}
    (hwv : I.weiValue = ⟨0⟩)
    (hauth : flipperSlotWord (flipperCallerWardsSlot I) σ I = ⟨1⟩)
    (hnotBeg : fileUintWhat I ≠ fileUintBegBytes)
    (hnotTtl : fileUintWhat I ≠ fileUintTtlBytes)
    (hnotTau : fileUintWhat I ≠ fileUintTauBytes) :
    let locals := fileUintLocals I
    let evm0 := initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I
    ExecTransitionBody config contract evm0 locals fileUintTransition.body .reverted := by
  intro locals evm0
  have hguard :
      evalExpr? config { contract := contract, locals := locals } evm0
        (.binary .eq (.storage (wardsRef sender)) (.intLit 1)) = .ok (.bool true) := by
    simpa [locals, evm0] using
      flipperAuthGuardEval_true (cA := cA) (gh := gh) (bl := bl) (σ := σ)
        (σ₀ := σ₀) (A := A) (I := I) (g := Sat256.ofUInt256 g) (locals := locals)
        (by simp [locals]) hauth
  have hbeg :
      evalExpr? config { contract := contract, locals := locals } evm0
        (.binary .eq (.var "what") begParamLit) = .ok (.bool false) := by
    simpa [begParamLit, fileUintBegBytes] using
      (evalExpr_fileUintWhatEq_false (evm := evm0) (I := I) (locals := locals)
        (bs := fileUintBegBytes) (by simpa [locals] using fileUintLocals_get_what I)
        hnotBeg)
  have httl :
      evalExpr? config { contract := contract, locals := locals } evm0
        (.binary .eq (.var "what") ttlParamLit) = .ok (.bool false) := by
    simpa [ttlParamLit, fileUintTtlBytes] using
      (evalExpr_fileUintWhatEq_false (evm := evm0) (I := I) (locals := locals)
        (bs := fileUintTtlBytes) (by simpa [locals] using fileUintLocals_get_what I)
        hnotTtl)
  have htau :
      evalExpr? config { contract := contract, locals := locals } evm0
        (.binary .eq (.var "what") tauParamLit) = .ok (.bool false) := by
    simpa [tauParamLit, fileUintTauBytes] using
      (evalExpr_fileUintWhatEq_false (evm := evm0) (I := I) (locals := locals)
        (bs := fileUintTauBytes) (by simpa [locals] using fileUintLocals_get_what I)
        hnotTau)
  have hreqFalse :
      evalExpr? config { contract := contract, locals := locals } evm0 (.boolLit false) =
        .ok (.bool false) := by
    simp [evalExpr?, pure]
  have hreq :
      ExecBlock config { contract := contract, locals := locals } evm0
        [.require (.boolLit false)] .reverted := by
    exact ExecBlock.consRevert (ExecStmt.requireFalse hreqFalse)
  have htauElse :
      ExecBlock config { contract := contract, locals := locals } evm0
        [.ite (.binary .eq (.var "what") tauParamLit)
          [.assign .storage tauRef (wrap48 (.var "data"))]
          [.require (.boolLit false)]]
        .reverted := by
    exact ExecBlock.consRevert (ExecStmt.iteFalse htau hreq)
  have httlElse :
      ExecBlock config { contract := contract, locals := locals } evm0
        [.ite (.binary .eq (.var "what") ttlParamLit)
          [.assign .storage ttlRef (wrap48 (.var "data"))]
          [.ite (.binary .eq (.var "what") tauParamLit)
            [.assign .storage tauRef (wrap48 (.var "data"))]
            [.require (.boolLit false)]]]
        .reverted := by
    exact ExecBlock.consRevert (ExecStmt.iteFalse httl htauElse)
  have hblock :
      ExecBlock config { contract := contract, locals := locals } evm0
        fileUintTransition.body .reverted := by
    refine ExecBlock.consNormal (ExecStmt.requireTrue ?_) ?_
    · exact evalCallvalueEq_true (by simp [evm0, initState]; exact hwv)
    refine ExecBlock.consNormal (ExecStmt.requireTrue hguard) ?_
    exact ExecBlock.consRevert (ExecStmt.iteFalse hbeg httlElse)
  simpa [ExecTransitionBody, locals, evm0] using ExecFuncBody.execBlockRevert hblock

theorem flipperReachFileUintBody {cA gh bl σ σ₀ A I} {g : Sat256}
    (hcode : I.code = flipperBytecode) (hwv : I.weiValue = ⟨0⟩)
    (hsz : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hsel : selIs I (flipperSelBytes 7)) :
    ∃ k C, RD flipperBytecode I g (initState cA gh bl σ σ₀ g A I)
        ⟨325⟩ [flipperSelWord I] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty
        (cA, σ) k C := by
  have hword : flipperSelWord I = ⟨0x29ae8114⟩ :=
    flipperSelWord_eq_of_beq I hsz 0x29 0xae 0x81 0x14 ⟨0x29ae8114⟩
      (by native_decide) (by simpa [flipperSelBytes] using hsel)
  have hroot : UInt256.gt (armSelNat flipperBytecode flipperRootSplitPc)
      (flipperSelWord I) ≠ ⟨0⟩ := by
    rw [hword]
    native_decide
  have hhigh : UInt256.gt (armSelNat flipperBytecode flipperHighSplitPc)
      (flipperSelWord I) ≠ ⟨0⟩ := by
    rw [hword]
    native_decide
  have heq0 : ∀ j, j < 1 →
      UInt256.eq (armSelNat flipperBytecode
        (nthArmPc flipperBytecode flipperHighLowFirstArmPc j))
        (flipperSelWord I) = ⟨0⟩ := by
    intro j hj
    interval_cases j <;> rw [hword] <;> native_decide
  have htake :
      UInt256.eq (armSelNat flipperBytecode
        (nthArmPc flipperBytecode flipperHighLowFirstArmPc 1))
        (flipperSelWord I) ≠ ⟨0⟩ := by
    rw [hword]
    native_decide
  exact flipperReachHighLowBody 1 (by omega) ⟨325⟩ hcode hwv hsz hsize hroot hhigh
    heq0 htake (by jump_dest) (by native_decide)

theorem RD.flipperFileUintDecodeToRoutine {code : ByteArray} {g : Sat256}
    {s0 : State} {ee : ExecutionEnv} {k C : ℕ} {ret de sel : UInt256}
    {R : List UInt256} {mem rdata : ByteArray} {aw : UInt256}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    (h : RD code ee g s0 ⟨347⟩ (de :: ⟨4⟩ :: ret :: sel :: R) mem aw rdata acc k C)
    (hwf : code = flipperBytecode)
    (hroutine : (D_J code 0).contains ⟨1705⟩ = true)
    (hov : R.length + 10 ≤ 1024) :
    ∃ k' C', RD code ee g s0 ⟨1705⟩
      (calldataWord ee.calldata 36 :: calldataWord ee.calldata 4 :: ret :: sel :: R)
      mem aw rdata acc k' C' := by
  subst hwf
  have rd359 := evm_run h with [
    raw jumpdest (by native_decide) (by evm_ov),
    raw pop (by native_decide) (by evm_ov),
    raw dup1 (by native_decide) (by evm_ov),
    raw calldataload (by native_decide) (by evm_ov),
    raw swap1 (by native_decide) (by evm_ov),
    raw push1 ⟨32⟩ (by native_decide) (by evm_ov),
    raw add (by native_decide) (by evm_ov),
    raw calldataload (by native_decide) (by evm_ov),
    raw push2 ⟨1705⟩ (by native_decide) (by evm_ov),
    raw jump (by native_decide) hroutine (by evm_ov)]
  exact ⟨_, _, by simpa [calldataWord] using rd359⟩

theorem flipperFileUintX_decoded {cA gh bl σ σ₀ A I} {g : Sat256} {sel : UInt256}
    (hsz68 : 68 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hreach : ∃ k C, RD flipperBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨325⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    ∃ k C, RD flipperBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨1705⟩
        [fileUintData I, calldataWord I.calldata 4, ⟨323⟩, sel]
        solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
  obtain ⟨_, _, hdecoded⟩ := RD.solcExternalStaticArgsLenOk
    (code := flipperBytecode) (sel := sel) (entry := ⟨325⟩) (ret := ⟨323⟩)
    (decoded := ⟨347⟩) (need := ⟨64⟩) hreach
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by jump_dest)
    (by
      exact solcDecodeLenCheckOkUnsigned (by simpa using hsz68) hsize)
  obtain ⟨_, _, hroutine⟩ := RD.flipperFileUintDecodeToRoutine
    (code := flipperBytecode) (ret := ⟨323⟩) (sel := sel) (R := [])
    hdecoded rfl (by jump_dest) (by simp)
  exact ⟨_, _, by simpa [fileUintData] using hroutine⟩

theorem flipperFileUintX_authorized {cA σ I} {g : Sat256} {s0 : State}
    {k C : ℕ} {sel : UInt256}
    (hauth : flipperSlotWord (flipperCallerWardsSlot I) σ I = ⟨1⟩)
    (h : RD flipperBytecode I g s0 ⟨1705⟩
      [fileUintData I, calldataWord I.calldata 4, ⟨323⟩, sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    ∃ k' C', RD flipperBytecode I g s0 ⟨1787⟩
      [fileUintData I, calldataWord I.calldata 4, ⟨323⟩, sel]
      (twoWordHashMem (solcSourceWord I) ⟨0⟩ solcFreePtrMem)
      (UInt256.ofNat 3) ByteArray.empty (cA, σ) k' C' := by
  have hauthSolc :
      solcSlotWord σ I (solcMappingSlot ⟨0⟩ (solcSourceWord I)) = ⟨1⟩ := by
    simpa [flipperCallerWardsSlot, flipperSlotWord] using hauth
  exact RD.flipperAuthCheckOk
    (code := flipperBytecode) (pc := ⟨1705⟩) (okPc := ⟨1787⟩)
    (key := fileUintData I) (ret := calldataWord I.calldata 4) (R := [⟨323⟩, sel])
    h
    (by
      unfold flipperAuthCheckWf
      repeat' first | apply And.intro | native_decide)
    hauthSolc (by jump_dest) (by simp)

theorem flipperFileUintX_unauthorized {cA σ I} {g : Sat256} {s0 : State}
    {k C : ℕ} {sel : UInt256}
    (hauth : flipperSlotWord (flipperCallerWardsSlot I) σ I ≠ ⟨1⟩)
    (h : RD flipperBytecode I g s0 ⟨1705⟩
      [fileUintData I, calldataWord I.calldata 4, ⟨323⟩, sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    RDrev flipperBytecode g s0 := by
  have hauthSolc :
      solcSlotWord σ I (solcMappingSlot ⟨0⟩ (solcSourceWord I)) ≠ ⟨1⟩ := by
    simpa [flipperCallerWardsSlot, flipperSlotWord] using hauth
  exact RD.flipperAuthCheckRevert
    (pc := ⟨1705⟩) (okPc := ⟨1787⟩) (key := fileUintData I)
    (ret := calldataWord I.calldata 4) (R := [⟨323⟩, sel])
    h
    (by
      unfold flipperAuthCheckWf
      repeat' first | apply And.intro | native_decide)
    (by
      unfold flipperAuthCodecopyRevertTailWf flipperAuthTailPc
      repeat' first | apply And.intro | native_decide)
    hauthSolc (by simp)

abbrev uint48MaskOffset6 : UInt256 :=
  ⟨79228162514264056118567239680⟩

theorem uint48MaskOffset6_eq :
    uint48MaskOffset6 = UInt256.shiftLeft uint48Mask ⟨48⟩ := by
  native_decide

theorem uint48Divisor_shift_eq :
    UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨48⟩ = uint48Divisor := by
  native_decide

theorem flipperFileUintDecodePushBeg1789 :
    decode flipperBytecode (⟨1789⟩ : UInt256) =
      some (.Push .PUSH3, some ((⟨6448487⟩ : UInt256), 3)) := by
  native_decide

theorem flipperFileUintDecodePushTtl1813 :
    decode flipperBytecode (⟨1813⟩ : UInt256) =
      some (.Push .PUSH3, some ((⟨1907995⟩ : UInt256), 3)) := by
  native_decide

theorem flipperFileUintDecodePushMask1830 :
    decode flipperBytecode (⟨1830⟩ : UInt256) =
      some (.Push .PUSH6, some (uint48Mask, 6)) := by
  native_decide

theorem flipperFileUintDecodePushMask1839 :
    decode flipperBytecode (⟨1839⟩ : UInt256) =
      some (.Push .PUSH6, some (uint48Mask, 6)) := by
  native_decide

theorem flipperFileUintDecodePushTau1857 :
    decode flipperBytecode (⟨1857⟩ : UInt256) =
      some (.Push .PUSH3, some ((⟨7627125⟩ : UInt256), 3)) := by
  native_decide

theorem flipperFileUintDecodePushMask1874 :
    decode flipperBytecode (⟨1874⟩ : UInt256) =
      some (.Push .PUSH12, some (uint48MaskOffset6, 12)) := by
  native_decide

theorem flipperFileUintDecodePushMask1894 :
    decode flipperBytecode (⟨1894⟩ : UInt256) =
      some (.Push .PUSH6, some (uint48Mask, 6)) := by
  native_decide

theorem uint48MulDivisor_eq_shiftLeft (w : UInt256) :
    UInt256.mul w uint48Divisor = UInt256.shiftLeft w ⟨48⟩ := by
  apply u256_inj
  rw [u256_mul_toNat]
  unfold UInt256.shiftLeft
  rw [if_neg (by decide : ¬ ((⟨48⟩ : UInt256).val ≥ 256))]
  change w.toNat * uint48Divisor.toNat % UInt256.size = (w.toNat <<< 48) % UInt256.size
  rw [show uint48Divisor.toNat = 2 ^ 48 by native_decide]
  rw [Nat.shiftLeft_eq]

theorem fileUintOffset6RuntimeWord (old data : UInt256) :
    UInt256.lor (UInt256.mul (UInt256.land data uint48Mask) uint48Divisor)
        (UInt256.land (UInt256.lnot (UInt256.shiftLeft uint48Mask ⟨48⟩)) old) =
      setUint48Offset6Word old (UInt256.land data uint48Mask) := by
  have hlow :
      UInt256.land (UInt256.land data uint48Mask) uint48Mask =
        UInt256.land data uint48Mask := by
    exact uint48Mask_clean (uint48Mask_bound data)
  have hshift :
      UInt256.mul (UInt256.land data uint48Mask) uint48Divisor =
        UInt256.shiftLeft (UInt256.land data uint48Mask) ⟨48⟩ := by
    exact uint48MulDivisor_eq_shiftLeft (UInt256.land data uint48Mask)
  calc
    UInt256.lor (UInt256.mul (UInt256.land data uint48Mask) uint48Divisor)
        (UInt256.land (UInt256.lnot (UInt256.shiftLeft uint48Mask ⟨48⟩)) old) =
        UInt256.lor (UInt256.mul (UInt256.land data uint48Mask) uint48Divisor)
          (UInt256.land old (UInt256.lnot (UInt256.shiftLeft uint48Mask ⟨48⟩))) := by
          rw [u256_land_comm (UInt256.lnot (UInt256.shiftLeft uint48Mask ⟨48⟩)) old]
    _ = UInt256.lor (UInt256.shiftLeft (UInt256.land data uint48Mask) ⟨48⟩)
          (UInt256.land old (UInt256.lnot (UInt256.shiftLeft uint48Mask ⟨48⟩))) := by
          rw [hshift]
    _ = UInt256.lor
          (UInt256.land old (UInt256.lnot (UInt256.shiftLeft uint48Mask ⟨48⟩)))
          (UInt256.shiftLeft (UInt256.land data uint48Mask) ⟨48⟩) := by
          exact u256_lor_comm _ _
    _ = setUint48Offset6Word old (UInt256.land data uint48Mask) := by
          unfold setUint48Offset6Word
          rw [hlow]

theorem flipperFileUintX_skipBegTtl {cA σ I} {g : Sat256} {s0 : State}
    {k C : ℕ} {sel : UInt256}
    (hnotBeg : calldataWord I.calldata 4 ≠ ABI.bytesToWord fileUintBegBytes)
    (hnotTtl : calldataWord I.calldata 4 ≠ ABI.bytesToWord fileUintTtlBytes)
    (h : RD flipperBytecode I g s0 ⟨1787⟩
      [fileUintData I, calldataWord I.calldata 4, ⟨323⟩, sel]
      (twoWordHashMem (solcSourceWord I) ⟨0⟩ solcFreePtrMem)
      (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    ∃ k' C', RD flipperBytecode I g s0 ⟨1855⟩
      [fileUintData I, calldataWord I.calldata 4, ⟨323⟩, sel]
      (twoWordHashMem (solcSourceWord I) ⟨0⟩ solcFreePtrMem)
      (UInt256.ofNat 3) ByteArray.empty (cA, σ) k' C' := by
  have rd1788 := h.jumpdest (by native_decide) (by evm_ov)
  have rd1789 := rd1788.dup2 (by native_decide) (by evm_ov)
  have rd1793 := rd1789.pushConst (⟨6448487⟩ : UInt256)
    (width := 3) (op := .PUSH3) (by decide) flipperFileUintDecodePushBeg1789
    (by evm_ov)
  have rd1795 := rd1793.push1 ⟨232⟩ (by native_decide) (by evm_ov)
  have rd1796 := rd1795.shl (by native_decide) (by evm_ov)
  have rd1797 := rd1796.eq (by native_decide) (by evm_ov)
  have hbegEq :
      UInt256.eq (UInt256.shiftLeft (⟨6448487⟩ : UInt256) ⟨232⟩)
          (calldataWord I.calldata 4) = ⟨0⟩ := by
    rw [← fileUintBegBytes_word]
    exact u256_eq_of_ne (by intro hbad; exact hnotBeg hbad.symm)
  rw [hbegEq] at rd1797
  have rd1798 := rd1797.iszero (by native_decide) (by evm_ov)
  have rd1801 := rd1798.push2 ⟨1811⟩ (by native_decide) (by evm_ov)
  have rd1811 := rd1801.jumpiT (by native_decide) one_ne_zero_uint (by jump_dest)
    (by evm_ov)
  have rd1812 := rd1811.jumpdest (by native_decide) (by evm_ov)
  have rd1813 := rd1812.dup2 (by native_decide) (by evm_ov)
  have rd1817 := rd1813.pushConst (⟨1907995⟩ : UInt256)
    (width := 3) (op := .PUSH3) (by decide) flipperFileUintDecodePushTtl1813
    (by evm_ov)
  have rd1819 := rd1817.push1 ⟨234⟩ (by native_decide) (by evm_ov)
  have rd1820 := rd1819.shl (by native_decide) (by evm_ov)
  have rd1821 := rd1820.eq (by native_decide) (by evm_ov)
  have httlEq :
      UInt256.eq (UInt256.shiftLeft (⟨1907995⟩ : UInt256) ⟨234⟩)
          (calldataWord I.calldata 4) = ⟨0⟩ := by
    rw [← fileUintTtlBytes_word]
    exact u256_eq_of_ne (by intro hbad; exact hnotTtl hbad.symm)
  rw [httlEq] at rd1821
  have rd1822 := rd1821.iszero (by native_decide) (by evm_ov)
  have rd1825 := rd1822.push2 ⟨1855⟩ (by native_decide) (by evm_ov)
  have rd1855 := rd1825.jumpiT (by native_decide) one_ne_zero_uint (by jump_dest)
    (by evm_ov)
  exact ⟨_, _, rd1855⟩

theorem flipperFileUintX_storeBeg {cA σ I} {g : Sat256} {s0 : State}
    {k C : ℕ} {sel : UInt256} (hperm : I.perm = true)
    (hmatch : calldataWord I.calldata 4 = ABI.bytesToWord fileUintBegBytes)
    (h : RD flipperBytecode I g s0 ⟨1787⟩
      [fileUintData I, calldataWord I.calldata 4, ⟨323⟩, sel]
      (twoWordHashMem (solcSourceWord I) ⟨0⟩ solcFreePtrMem)
      (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    RDret flipperBytecode g s0
      (cA, sstoreAccountMap I.codeOwner σ ⟨4⟩ (fileUintData I)) ByteArray.empty := by
  have rd1796 := evm_run h with [
    raw jumpdest (by native_decide) (by evm_ov),
    raw dup2 (by native_decide) (by evm_ov),
    raw pushConst (⟨6448487⟩ : UInt256)
      (show Operation.POp.PUSH3 ≠ Operation.POp.PUSH0 by native_decide)
      flipperFileUintDecodePushBeg1789
      (by evm_ov),
    raw push1 ⟨232⟩ (by native_decide) (by evm_ov),
    raw shl (by native_decide) (by evm_ov)]
  rw [hmatch, fileUintBegBytes_word] at rd1796
  have rd1810 := evm_run rd1796 with [
    raw eq (by native_decide) (by evm_ov),
    raw iszero (by native_decide) (by evm_ov),
    raw push2 ⟨1811⟩ (by native_decide) (by evm_ov),
    raw jumpiNT (by native_decide) (by decide) (by evm_ov),
    raw push1 ⟨4⟩ (by native_decide) (by evm_ov),
    raw dup2 (by native_decide) (by evm_ov),
    raw swap1 (by native_decide) (by evm_ov)]
  obtain ⟨_, _, rd1807⟩ := rd1810.sstore hperm (by native_decide) (by evm_ov)
  have rd1988 := rd1807.push2 ⟨1988⟩ (by native_decide) (by evm_ov)
  have rd1989 := rd1988.jump (by native_decide) (by jump_dest) (by evm_ov)
    |>.jumpdest (by native_decide) (by evm_ov)
  have rd1990 := rd1989.pop (by native_decide) (by evm_ov)
  have rd1991 := rd1990.pop (by native_decide) (by evm_ov)
  have rd323 := rd1991.jump (by native_decide) (by jump_dest) (by evm_ov)
  have rd324 := rd323.jumpdest (by native_decide) (by evm_ov)
  simpa [solcSlotWord] using RD.stop rd324 (by native_decide) (by evm_ov)

theorem flipperFileUintX_storeTtl {cA σ I} {g : Sat256} {s0 : State}
    {k C : ℕ} {sel : UInt256} (hperm : I.perm = true)
    (hnotBeg : calldataWord I.calldata 4 ≠ ABI.bytesToWord fileUintBegBytes)
    (hmatch : calldataWord I.calldata 4 = ABI.bytesToWord fileUintTtlBytes)
    (h : RD flipperBytecode I g s0 ⟨1787⟩
      [fileUintData I, calldataWord I.calldata 4, ⟨323⟩, sel]
      (twoWordHashMem (solcSourceWord I) ⟨0⟩ solcFreePtrMem)
      (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    RDret flipperBytecode g s0
      (cA, sstoreAccountMap I.codeOwner σ ⟨5⟩
        (setUint48Offset0Word (solcSlotWord σ I ⟨5⟩) (fileUintData48 I)))
      ByteArray.empty := by
  have rd1797 := evm_run h with [
    raw jumpdest (by native_decide) (by evm_ov),
    raw dup2 (by native_decide) (by evm_ov),
    raw pushConst (⟨6448487⟩ : UInt256)
      (show Operation.POp.PUSH3 ≠ Operation.POp.PUSH0 by native_decide)
      flipperFileUintDecodePushBeg1789
      (by evm_ov),
    raw push1 ⟨232⟩ (by native_decide) (by evm_ov),
    raw shl (by native_decide) (by evm_ov),
    raw eq (by native_decide) (by evm_ov)]
  have hbegEq :
      UInt256.eq (UInt256.shiftLeft (⟨6448487⟩ : UInt256) ⟨232⟩)
          (calldataWord I.calldata 4) = ⟨0⟩ := by
    rw [← fileUintBegBytes_word]
    exact u256_eq_of_ne (by intro hbad; exact hnotBeg hbad.symm)
  rw [hbegEq] at rd1797
  have rd1811 := evm_run rd1797 with [
    raw iszero (by native_decide) (by evm_ov),
    raw push2 ⟨1811⟩ (by native_decide) (by evm_ov),
    raw jumpiT (by native_decide) one_ne_zero_uint (by jump_dest) (by evm_ov)]
  have rd1820 := evm_run rd1811 with [
    raw jumpdest (by native_decide) (by evm_ov),
    raw dup2 (by native_decide) (by evm_ov),
    raw pushConst (⟨1907995⟩ : UInt256)
      (show Operation.POp.PUSH3 ≠ Operation.POp.PUSH0 by native_decide)
      flipperFileUintDecodePushTtl1813
      (by evm_ov),
    raw push1 ⟨234⟩ (by native_decide) (by evm_ov),
    raw shl (by native_decide) (by evm_ov)]
  rw [hmatch, fileUintTtlBytes_word] at rd1820
  have rd1826 := evm_run rd1820 with [
    raw eq (by native_decide) (by evm_ov),
    raw iszero (by native_decide) (by evm_ov),
    raw push2 ⟨1855⟩ (by native_decide) (by evm_ov),
    raw jumpiNT (by native_decide) (by decide) (by evm_ov),
    raw push1 ⟨5⟩ (by native_decide) (by evm_ov),
    raw dup1 (by native_decide) (by evm_ov)]
  obtain ⟨_, _, rd1830⟩ := rd1826.sload (by native_decide) (by evm_ov)
  have rd1850 := evm_run rd1830 with [
    raw pushConst uint48Mask
      (show Operation.POp.PUSH6 ≠ Operation.POp.PUSH0 by native_decide)
      flipperFileUintDecodePushMask1830
      (by evm_ov),
    raw not (by native_decide) (by evm_ov),
    raw and (by native_decide) (by evm_ov),
    raw pushConst uint48Mask
      (show Operation.POp.PUSH6 ≠ Operation.POp.PUSH0 by native_decide)
      flipperFileUintDecodePushMask1839
      (by evm_ov),
    raw dup4 (by native_decide) (by evm_ov),
    raw and (by native_decide) (by evm_ov),
    raw or (by native_decide) (by evm_ov),
    raw swap1 (by native_decide) (by evm_ov)]
  obtain ⟨_, _, rd1851⟩ := rd1850.sstore hperm (by native_decide) (by evm_ov)
  have rd1988 := rd1851.push2 ⟨1988⟩ (by native_decide) (by evm_ov)
  have rd1989 := rd1988.jump (by native_decide) (by jump_dest) (by evm_ov)
    |>.jumpdest (by native_decide) (by evm_ov)
  have rd1990 := rd1989.pop (by native_decide) (by evm_ov)
  have rd1991 := rd1990.pop (by native_decide) (by evm_ov)
  have hword :
      UInt256.lor (UInt256.land (fileUintData I) uint48Mask)
          (UInt256.land (UInt256.lnot uint48Mask) (solcSlotWord σ I ⟨5⟩)) =
        setUint48Offset0Word (solcSlotWord σ I ⟨5⟩) (fileUintData48 I) := by
    have hlow : UInt256.land (fileUintData48 I) uint48Mask = fileUintData48 I := by
      exact uint48Mask_clean (uint48Mask_bound (fileUintData I))
    calc
      UInt256.lor (UInt256.land (fileUintData I) uint48Mask)
          (UInt256.land (UInt256.lnot uint48Mask) (solcSlotWord σ I ⟨5⟩)) =
          UInt256.lor (fileUintData48 I)
            (UInt256.land (solcSlotWord σ I ⟨5⟩) (UInt256.lnot uint48Mask)) := by
            rw [fileUintData48, u256_land_comm (UInt256.lnot uint48Mask)
              (solcSlotWord σ I ⟨5⟩)]
      _ = UInt256.lor (UInt256.land (solcSlotWord σ I ⟨5⟩) (UInt256.lnot uint48Mask))
            (fileUintData48 I) := by
            exact u256_lor_comm _ _
      _ = setUint48Offset0Word (solcSlotWord σ I ⟨5⟩) (fileUintData48 I) := by
            unfold setUint48Offset0Word
            rw [hlow]
  have rd323 := rd1991.jump (by native_decide) (by jump_dest) (by evm_ov)
  have rd324 := rd323.jumpdest (by native_decide) (by evm_ov)
  simpa [solcSlotWord, setUint48Offset0Word, fileUintData48, hword] using
    RD.stop rd324 (by native_decide) (by evm_ov)

theorem flipperFileUintX_matchTauToSload {cA σ I} {g : Sat256} {s0 : State}
    {k C : ℕ} {sel : UInt256}
    (hmatch : calldataWord I.calldata 4 = ABI.bytesToWord fileUintTauBytes)
    (h : RD flipperBytecode I g s0 ⟨1855⟩
      [fileUintData I, calldataWord I.calldata 4, ⟨323⟩, sel]
      (twoWordHashMem (solcSourceWord I) ⟨0⟩ solcFreePtrMem)
      (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    ∃ k' C', RD flipperBytecode I g s0 ⟨1874⟩
      [solcSlotWord σ I ⟨5⟩, ⟨5⟩, fileUintData I, calldataWord I.calldata 4, ⟨323⟩, sel]
      (twoWordHashMem (solcSourceWord I) ⟨0⟩ solcFreePtrMem)
      (UInt256.ofNat 3) ByteArray.empty (cA, σ) k' C' := by
  have rd1856 := h.jumpdest (by native_decide) (by evm_ov)
  have rd1857 := rd1856.dup2 (by native_decide) (by evm_ov)
  have rd1861 := rd1857.pushConst (⟨7627125⟩ : UInt256)
    (width := 3) (op := .PUSH3) (by decide) flipperFileUintDecodePushTau1857
    (by evm_ov)
  have rd1863 := rd1861.push1 ⟨232⟩ (by native_decide) (by evm_ov)
  have rd1864 := rd1863.shl (by native_decide) (by evm_ov)
  have rd1865 := rd1864.eq (by native_decide) (by evm_ov)
  have htauEq :
      UInt256.eq (UInt256.shiftLeft (⟨7627125⟩ : UInt256) ⟨232⟩)
          (calldataWord I.calldata 4) = ⟨1⟩ := by
    rw [hmatch, fileUintTauBytes_word]
    exact uInt256_eq_self _
  rw [htauEq] at rd1865
  have rd1866 := rd1865.iszero (by native_decide) (by evm_ov)
  rw [show UInt256.isZero (⟨1⟩ : UInt256) = ⟨0⟩ from by decide] at rd1866
  have rd1869 := rd1866.push2 ⟨1911⟩ (by native_decide) (by evm_ov)
  have rd1870 := rd1869.jumpiNT (by native_decide)
    (by decide : (⟨0⟩ : UInt256) = ⟨0⟩) (by evm_ov)
  have rd1872 := rd1870.push1 ⟨5⟩ (by native_decide) (by evm_ov)
  have rd1873 := rd1872.dup1 (by native_decide) (by evm_ov)
  obtain ⟨k1874, C1874, rd1874raw⟩ := rd1873.sload (by native_decide) (by evm_ov)
  have rd1874 : RD flipperBytecode I g s0 ⟨1874⟩
      [solcSlotWord σ I ⟨5⟩, ⟨5⟩, fileUintData I, calldataWord I.calldata 4, ⟨323⟩, sel]
      (twoWordHashMem (solcSourceWord I) ⟨0⟩ solcFreePtrMem)
      (UInt256.ofNat 3) ByteArray.empty (cA, σ) k1874 C1874 := by
    simpa [solcSlotWord] using rd1874raw
  exact ⟨_, _, rd1874⟩

theorem flipperFileUintX_storeTauTail {cA σ I} {g : Sat256} {s0 : State}
    {k C : ℕ} {sel : UInt256} (hperm : I.perm = true)
    (h : RD flipperBytecode I g s0 ⟨1874⟩
      [solcSlotWord σ I ⟨5⟩, ⟨5⟩, fileUintData I, calldataWord I.calldata 4, ⟨323⟩, sel]
      (twoWordHashMem (solcSourceWord I) ⟨0⟩ solcFreePtrMem)
      (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    RDret flipperBytecode g s0
      (cA, sstoreAccountMap I.codeOwner σ ⟨5⟩
        (setUint48Offset6Word (solcSlotWord σ I ⟨5⟩) (fileUintData48 I)))
      ByteArray.empty := by
  have rd1887 := h.pushConst uint48MaskOffset6
    (width := 12) (op := .PUSH12) (by decide) flipperFileUintDecodePushMask1874
    (by evm_ov)
  rw [uint48MaskOffset6_eq] at rd1887
  have rd1888 := rd1887.not (by native_decide) (by evm_ov)
  have rd1889 := rd1888.and (by native_decide) (by evm_ov)
  have rd1891 := rd1889.push1 ⟨1⟩ (by native_decide) (by evm_ov)
  have rd1893 := rd1891.push1 ⟨48⟩ (by native_decide) (by evm_ov)
  have rd1894 := rd1893.shl (by native_decide) (by evm_ov)
  rw [uint48Divisor_shift_eq] at rd1894
  have rd1901 := rd1894.pushConst uint48Mask
    (width := 6) (op := .PUSH6) (by decide) flipperFileUintDecodePushMask1894
    (by evm_ov)
  have rd1902 := rd1901.dup5 (by native_decide) (by evm_ov)
  have rd1903 := rd1902.and (by native_decide) (by evm_ov)
  have rd1904 := rd1903.mul (by native_decide) (by evm_ov)
  have rd1905 := rd1904.or (by native_decide) (by evm_ov)
  have rd1906 := rd1905.swap1 (by native_decide) (by evm_ov)
  let slot5New :=
    UInt256.lor (UInt256.mul (UInt256.land (fileUintData I) uint48Mask) uint48Divisor)
      (UInt256.land
        (UInt256.lnot (UInt256.shiftLeft uint48Mask ⟨48⟩)) (solcSlotWord σ I ⟨5⟩))
  obtain ⟨k1907, C1907, rd1907raw⟩ := rd1906.sstore hperm (by native_decide) (by evm_ov)
  let σTau := sstoreAccountMap I.codeOwner σ ⟨5⟩ slot5New
  have rd1907 : RD flipperBytecode I g s0 ⟨1907⟩
      [fileUintData I, calldataWord I.calldata 4, ⟨323⟩, sel]
      (twoWordHashMem (solcSourceWord I) ⟨0⟩ solcFreePtrMem)
      (UInt256.ofNat 3) ByteArray.empty (cA, σTau) k1907 C1907 := by
    simpa [slot5New, σTau, solcSlotWord] using rd1907raw
  have rd1988 := rd1907.push2 ⟨1988⟩ (by native_decide) (by evm_ov)
  have rd1989 := rd1988.jump (by native_decide) (by jump_dest) (by evm_ov)
    |>.jumpdest (by native_decide) (by evm_ov)
  have rd1990 := rd1989.pop (by native_decide) (by evm_ov)
  have rd1991 := rd1990.pop (by native_decide) (by evm_ov)
  have hword :
      slot5New =
        setUint48Offset6Word (solcSlotWord σ I ⟨5⟩) (fileUintData48 I) := by
    simpa [slot5New, fileUintData48] using
      fileUintOffset6RuntimeWord (solcSlotWord σ I ⟨5⟩) (fileUintData I)
  have rd323 := rd1991.jump (by native_decide) (by jump_dest) (by evm_ov)
  have rd324 := rd323.jumpdest (by native_decide) (by evm_ov)
  have hstop : RDret flipperBytecode g s0 (cA, σTau) ByteArray.empty :=
    RD.stop rd324 (by native_decide) (by evm_ov)
  simpa [σTau, hword] using hstop

theorem flipperFileUintX_storeTau {cA σ I} {g : Sat256} {s0 : State}
    {k C : ℕ} {sel : UInt256} (hperm : I.perm = true)
    (hnotBeg : calldataWord I.calldata 4 ≠ ABI.bytesToWord fileUintBegBytes)
    (hnotTtl : calldataWord I.calldata 4 ≠ ABI.bytesToWord fileUintTtlBytes)
    (hmatch : calldataWord I.calldata 4 = ABI.bytesToWord fileUintTauBytes)
    (h : RD flipperBytecode I g s0 ⟨1787⟩
      [fileUintData I, calldataWord I.calldata 4, ⟨323⟩, sel]
      (twoWordHashMem (solcSourceWord I) ⟨0⟩ solcFreePtrMem)
      (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    RDret flipperBytecode g s0
      (cA, sstoreAccountMap I.codeOwner σ ⟨5⟩
        (setUint48Offset6Word (solcSlotWord σ I ⟨5⟩) (fileUintData48 I)))
      ByteArray.empty := by
  obtain ⟨_, _, rd1855⟩ := flipperFileUintX_skipBegTtl hnotBeg hnotTtl h
  obtain ⟨_, _, rd1874⟩ := flipperFileUintX_matchTauToSload hmatch rd1855
  exact flipperFileUintX_storeTauTail hperm rd1874

theorem flipperFileUintX_unrecognizedTau {cA σ I} {g : Sat256} {s0 : State}
    {k C : ℕ} {sel : UInt256}
    (hnotTau : calldataWord I.calldata 4 ≠ ABI.bytesToWord fileUintTauBytes)
    (h : RD flipperBytecode I g s0 ⟨1855⟩
      [fileUintData I, calldataWord I.calldata 4, ⟨323⟩, sel]
      (twoWordHashMem (solcSourceWord I) ⟨0⟩ solcFreePtrMem)
      (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    RDrev flipperBytecode g s0 := by
  have rd1856 := h.jumpdest (by native_decide) (by evm_ov)
  have rd1857 := rd1856.dup2 (by native_decide) (by evm_ov)
  have rd1861 := rd1857.pushConst (⟨7627125⟩ : UInt256)
    (width := 3) (op := .PUSH3) (by decide) flipperFileUintDecodePushTau1857
    (by evm_ov)
  have rd1863 := rd1861.push1 ⟨232⟩ (by native_decide) (by evm_ov)
  have rd1864 := rd1863.shl (by native_decide) (by evm_ov)
  have rd1865 := rd1864.eq (by native_decide) (by evm_ov)
  have htauEq :
      UInt256.eq (UInt256.shiftLeft (⟨7627125⟩ : UInt256) ⟨232⟩)
          (calldataWord I.calldata 4) = ⟨0⟩ := by
    rw [← fileUintTauBytes_word]
    exact u256_eq_of_ne (by intro hbad; exact hnotTau hbad.symm)
  rw [htauEq] at rd1865
  have rd1866 := rd1865.iszero (by native_decide) (by evm_ov)
  have rd1869 := rd1866.push2 ⟨1911⟩ (by native_decide) (by evm_ov)
  have rd1911 := rd1869.jumpiT (by native_decide) one_ne_zero_uint (by jump_dest)
    (by evm_ov)
  exact RD.flipperFileUnrecognizedRevert rd1911
    (twoWordHashMem_size_96 (solcSourceWord I) ⟨0⟩ solcFreePtrMem_size)
    (twoWordHashMem_read64 (solcSourceWord I) ⟨0⟩ solcFreePtrMem_size solcFreePtrMem_read64)
    (by simp only [List.length_cons, List.length_nil]; omega)

theorem flipperFileUintX_unrecognized {cA σ I} {g : Sat256} {s0 : State}
    {k C : ℕ} {sel : UInt256}
    (hnotBeg : calldataWord I.calldata 4 ≠ ABI.bytesToWord fileUintBegBytes)
    (hnotTtl : calldataWord I.calldata 4 ≠ ABI.bytesToWord fileUintTtlBytes)
    (hnotTau : calldataWord I.calldata 4 ≠ ABI.bytesToWord fileUintTauBytes)
    (h : RD flipperBytecode I g s0 ⟨1787⟩
      [fileUintData I, calldataWord I.calldata 4, ⟨323⟩, sel]
      (twoWordHashMem (solcSourceWord I) ⟨0⟩ solcFreePtrMem)
      (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    RDrev flipperBytecode g s0 := by
  obtain ⟨_, _, rd1855⟩ := flipperFileUintX_skipBegTtl hnotBeg hnotTtl h
  exact flipperFileUintX_unrecognizedTau hnotTau rd1855

theorem flipperFileUintX_shortarg {cA gh bl σ σ₀ A I} {g : Sat256}
    {sel : UInt256}
    (hsz4 : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hshort : I.calldata.size < 68)
    (hreach : ∃ k C, RD flipperBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨325⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    RDrev flipperBytecode g (initState cA gh bl σ σ₀ g A I) := by
  have hlt :
      UInt256.lt (UInt256.sub (UInt256.ofNat I.calldata.size) ⟨4⟩) ⟨64⟩ = ⟨1⟩ := by
    apply ult_one
    rw [usub_ofNat_word_toNat (by simpa using hsz4) hsize]
    change I.calldata.size - 4 < 64
    omega
  exact RD.solcExternalStaticArgsShortReverts
    (code := flipperBytecode) (sel := sel) (entry := ⟨325⟩) (ret := ⟨323⟩)
    (decoded := ⟨347⟩) (need := ⟨64⟩) hreach
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) hlt

theorem flipperFileUintBodyCoreOkBeg
    {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256} {sel : UInt256}
    (hcode : I.code = flipperBytecode) (hsize : I.calldata.size < UInt256.size)
    (hperm : I.perm = true) (hwv : I.weiValue = ⟨0⟩)
    (hsz68 : 68 ≤ I.calldata.size)
    (hauth : flipperSlotWord (flipperCallerWardsSlot I) σ_evm I = ⟨1⟩)
    (hwhat : fileUintWhat I = fileUintBegBytes)
    (hdispatch : dispatchMsg contract I.calldata = some fileUintTransition)
    (hdecode :
      decodeCalldataWithMode config.abiDecodeMode (fileUintTransition.params.map Param.name)
        (transitionSignature fileUintTransition).paramTypes I.calldata =
          some (fileUintLocals I))
    (hreach : ∃ k C, RD flipperBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) ⟨325⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ_evm) k C)
    (hAccounts : accountMapEquiv σ_evm σ_solm) :
    runtimeEquivalenceFor config contract cA gh bl σ_evm σ_solm σ₀ g A I := by
  let locals := fileUintLocals I
  let evm0 := initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I
  let evm1 := Solm.EVM.storageStore evm0 I.codeOwner ⟨4⟩ (fileUintData I)
  have hauthSolm : flipperSlotWord (flipperCallerWardsSlot I) σ_solm I = ⟨1⟩ := by
    have hword : flipperSlotWord (flipperCallerWardsSlot I) σ_evm I =
        flipperSlotWord (flipperCallerWardsSlot I) σ_solm I :=
      accountMapEquiv_storage_findD hAccounts I.codeOwner (flipperCallerWardsSlot I) ⟨0⟩
    rw [← hword]
    exact hauth
  have hbody :
      ExecTransitionBody config contract evm0 locals fileUintTransition.body
        (.returned { contract := contract, locals := locals } evm1 none) := by
    simpa [evm0, evm1, locals, initState] using
      (flipperFileUintSourceBodyBeg (cA := cA) (gh := gh) (bl := bl) (σ := σ_solm)
        (σ₀ := σ₀) (A := A) (I := I) (g := g) hwv hauthSolm hwhat)
  obtain ⟨_, _, hdecoded⟩ := flipperFileUintX_decoded (g := Sat256.ofUInt256 g)
    hsz68 hsize hreach
  obtain ⟨_, _, hswitch⟩ := flipperFileUintX_authorized (I := I) hauth hdecoded
  have hmatch : calldataWord I.calldata 4 = ABI.bytesToWord fileUintBegBytes :=
    fileUintWhatWord_eq_of_bytes_eq (by omega) hwhat
  have hret := flipperFileUintX_storeBeg hperm hmatch hswitch
  exact hret.reEquivExecutionGenAccountMapEquiv hcode hdispatch hdecode hbody
    (by simp [evm1, evm0, initState, storageStore_createdAccounts])
    (by
      simpa [evm1, evm0, initState, storageStore_accountMap] using
        accountMapEquiv_sstoreAccountMap I.codeOwner ⟨4⟩ (fileUintData I) hAccounts)
    (by
      rw [show fileUintTransition.returnType = [] by rfl]
      exact returnEquiv.fallthrough rfl (by rfl) (by native_decide))

theorem flipperFileUintBodyCoreOkTtl
    {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256} {sel : UInt256}
    (hcode : I.code = flipperBytecode) (hsize : I.calldata.size < UInt256.size)
    (hperm : I.perm = true) (hwv : I.weiValue = ⟨0⟩)
    (hsz68 : 68 ≤ I.calldata.size)
    (hauth : flipperSlotWord (flipperCallerWardsSlot I) σ_evm I = ⟨1⟩)
    (hnotBeg : fileUintWhat I ≠ fileUintBegBytes)
    (hwhat : fileUintWhat I = fileUintTtlBytes)
    (hdispatch : dispatchMsg contract I.calldata = some fileUintTransition)
    (hdecode :
      decodeCalldataWithMode config.abiDecodeMode (fileUintTransition.params.map Param.name)
        (transitionSignature fileUintTransition).paramTypes I.calldata =
          some (fileUintLocals I))
    (hreach : ∃ k C, RD flipperBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) ⟨325⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ_evm) k C)
    (hAccounts : accountMapEquiv σ_evm σ_solm) :
    runtimeEquivalenceFor config contract cA gh bl σ_evm σ_solm σ₀ g A I := by
  let data := fileUintData48 I
  let stored := setUint48Offset0Word (solcSlotWord σ_evm I ⟨5⟩) data
  let locals := fileUintLocals I
  let evm0 := initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I
  let evm1 := Solm.EVM.storageStore evm0 I.codeOwner ⟨5⟩ stored
  have hauthSolm : flipperSlotWord (flipperCallerWardsSlot I) σ_solm I = ⟨1⟩ := by
    have hword : flipperSlotWord (flipperCallerWardsSlot I) σ_evm I =
        flipperSlotWord (flipperCallerWardsSlot I) σ_solm I :=
      accountMapEquiv_storage_findD hAccounts I.codeOwner (flipperCallerWardsSlot I) ⟨0⟩
    rw [← hword]
    exact hauth
  have hslot5 : flipperSlotWord ⟨5⟩ σ_evm I = flipperSlotWord ⟨5⟩ σ_solm I :=
    accountMapEquiv_storage_findD hAccounts I.codeOwner ⟨5⟩ ⟨0⟩
  have hstoredSolm :
      stored = setUint48Offset0Word (solcSlotWord σ_solm I ⟨5⟩) data := by
    simpa [stored, flipperSlotWord] using congrArg (fun old => setUint48Offset0Word old data)
      hslot5
  have hbody :
      ExecTransitionBody config contract evm0 locals fileUintTransition.body
        (.returned { contract := contract, locals := locals } evm1 none) := by
    simpa [evm0, evm1, locals, stored, data, hstoredSolm, solcSlotWord, initState,
      Solm.EVM.storageLoad] using
      (flipperFileUintSourceBodyTtl (cA := cA) (gh := gh) (bl := bl) (σ := σ_solm)
        (σ₀ := σ₀) (A := A) (I := I) (g := g) hwv hauthSolm hnotBeg hwhat)
  obtain ⟨_, _, hdecoded⟩ := flipperFileUintX_decoded (g := Sat256.ofUInt256 g)
    hsz68 hsize hreach
  obtain ⟨_, _, hswitch⟩ := flipperFileUintX_authorized (I := I) hauth hdecoded
  have hnotBegWord : calldataWord I.calldata 4 ≠ ABI.bytesToWord fileUintBegBytes :=
    fileUintWhatWord_ne_of_bytes_ne (by omega) hnotBeg fileUintBegBytes_length
  have hmatch : calldataWord I.calldata 4 = ABI.bytesToWord fileUintTtlBytes :=
    fileUintWhatWord_eq_of_bytes_eq (by omega) hwhat
  have hret := flipperFileUintX_storeTtl hperm hnotBegWord hmatch hswitch
  have hret' :
      RDret flipperBytecode (Sat256.ofUInt256 g)
        (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I)
        (cA, sstoreAccountMap I.codeOwner σ_evm ⟨5⟩ stored) ByteArray.empty := by
    simpa [stored, data] using hret
  exact hret'.reEquivExecutionGenAccountMapEquiv hcode hdispatch hdecode hbody
    (by simp [evm1, evm0, initState, storageStore_createdAccounts])
    (by
      simpa [evm1, evm0, initState, storageStore_accountMap, stored, data, hstoredSolm,
        solcSlotWord, Solm.EVM.storageLoad] using
        accountMapEquiv_sstoreAccountMap I.codeOwner ⟨5⟩ stored hAccounts)
    (by
      rw [show fileUintTransition.returnType = [] by rfl]
      exact returnEquiv.fallthrough rfl (by rfl) (by native_decide))

theorem flipperFileUintBodyCoreOkTau
    {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256} {sel : UInt256}
    (hcode : I.code = flipperBytecode) (hsize : I.calldata.size < UInt256.size)
    (hperm : I.perm = true) (hwv : I.weiValue = ⟨0⟩)
    (hsz68 : 68 ≤ I.calldata.size)
    (hauth : flipperSlotWord (flipperCallerWardsSlot I) σ_evm I = ⟨1⟩)
    (hnotBeg : fileUintWhat I ≠ fileUintBegBytes)
    (hnotTtl : fileUintWhat I ≠ fileUintTtlBytes)
    (hwhat : fileUintWhat I = fileUintTauBytes)
    (hdispatch : dispatchMsg contract I.calldata = some fileUintTransition)
    (hdecode :
      decodeCalldataWithMode config.abiDecodeMode (fileUintTransition.params.map Param.name)
        (transitionSignature fileUintTransition).paramTypes I.calldata =
          some (fileUintLocals I))
    (hreach : ∃ k C, RD flipperBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) ⟨325⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ_evm) k C)
    (hAccounts : accountMapEquiv σ_evm σ_solm) :
    runtimeEquivalenceFor config contract cA gh bl σ_evm σ_solm σ₀ g A I := by
  let data := fileUintData48 I
  let stored := setUint48Offset6Word (solcSlotWord σ_evm I ⟨5⟩) data
  let locals := fileUintLocals I
  let evm0 := initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I
  let evm1 := Solm.EVM.storageStore evm0 I.codeOwner ⟨5⟩ stored
  have hauthSolm : flipperSlotWord (flipperCallerWardsSlot I) σ_solm I = ⟨1⟩ := by
    have hword : flipperSlotWord (flipperCallerWardsSlot I) σ_evm I =
        flipperSlotWord (flipperCallerWardsSlot I) σ_solm I :=
      accountMapEquiv_storage_findD hAccounts I.codeOwner (flipperCallerWardsSlot I) ⟨0⟩
    rw [← hword]
    exact hauth
  have hslot5 : flipperSlotWord ⟨5⟩ σ_evm I = flipperSlotWord ⟨5⟩ σ_solm I :=
    accountMapEquiv_storage_findD hAccounts I.codeOwner ⟨5⟩ ⟨0⟩
  have hstoredSolm :
      stored = setUint48Offset6Word (solcSlotWord σ_solm I ⟨5⟩) data := by
    simpa [stored, flipperSlotWord] using congrArg (fun old => setUint48Offset6Word old data)
      hslot5
  have hbody :
      ExecTransitionBody config contract evm0 locals fileUintTransition.body
        (.returned { contract := contract, locals := locals } evm1 none) := by
    simpa [evm0, evm1, locals, stored, data, hstoredSolm, solcSlotWord, initState,
      Solm.EVM.storageLoad] using
      (flipperFileUintSourceBodyTau (cA := cA) (gh := gh) (bl := bl) (σ := σ_solm)
        (σ₀ := σ₀) (A := A) (I := I) (g := g) hwv hauthSolm hnotBeg hnotTtl hwhat)
  obtain ⟨_, _, hdecoded⟩ := flipperFileUintX_decoded (g := Sat256.ofUInt256 g)
    hsz68 hsize hreach
  obtain ⟨_, _, hswitch⟩ := flipperFileUintX_authorized (I := I) hauth hdecoded
  have hnotBegWord : calldataWord I.calldata 4 ≠ ABI.bytesToWord fileUintBegBytes :=
    fileUintWhatWord_ne_of_bytes_ne (by omega) hnotBeg fileUintBegBytes_length
  have hnotTtlWord : calldataWord I.calldata 4 ≠ ABI.bytesToWord fileUintTtlBytes :=
    fileUintWhatWord_ne_of_bytes_ne (by omega) hnotTtl fileUintTtlBytes_length
  have hmatch : calldataWord I.calldata 4 = ABI.bytesToWord fileUintTauBytes :=
    fileUintWhatWord_eq_of_bytes_eq (by omega) hwhat
  have hret := flipperFileUintX_storeTau hperm hnotBegWord hnotTtlWord hmatch hswitch
  have hret' :
      RDret flipperBytecode (Sat256.ofUInt256 g)
        (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I)
        (cA, sstoreAccountMap I.codeOwner σ_evm ⟨5⟩ stored) ByteArray.empty := by
    simpa [stored, data] using hret
  exact hret'.reEquivExecutionGenAccountMapEquiv hcode hdispatch hdecode hbody
    (by simp [evm1, evm0, initState, storageStore_createdAccounts])
    (by
      simpa [evm1, evm0, initState, storageStore_accountMap, stored, data, hstoredSolm,
        solcSlotWord, Solm.EVM.storageLoad] using
        accountMapEquiv_sstoreAccountMap I.codeOwner ⟨5⟩ stored hAccounts)
    (by
      rw [show fileUintTransition.returnType = [] by rfl]
      exact returnEquiv.fallthrough rfl (by rfl) (by native_decide))

theorem flipperFileUintBodyCoreUnauthorized
    {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256} {sel : UInt256}
    (hcode : I.code = flipperBytecode) (hsize : I.calldata.size < UInt256.size)
    (hwv : I.weiValue = ⟨0⟩)
    (hsz68 : 68 ≤ I.calldata.size)
    (hauth : flipperSlotWord (flipperCallerWardsSlot I) σ_evm I ≠ ⟨1⟩)
    (hdispatch : dispatchMsg contract I.calldata = some fileUintTransition)
    (hdecode :
      decodeCalldataWithMode config.abiDecodeMode (fileUintTransition.params.map Param.name)
        (transitionSignature fileUintTransition).paramTypes I.calldata =
          some (fileUintLocals I))
    (hreach : ∃ k C, RD flipperBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) ⟨325⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ_evm) k C)
    (hAccounts : accountMapEquiv σ_evm σ_solm) :
    runtimeEquivalenceFor config contract cA gh bl σ_evm σ_solm σ₀ g A I := by
  let locals := fileUintLocals I
  let evm0 := initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I
  have hauthSolm : flipperSlotWord (flipperCallerWardsSlot I) σ_solm I ≠ ⟨1⟩ := by
    have hword : flipperSlotWord (flipperCallerWardsSlot I) σ_evm I =
        flipperSlotWord (flipperCallerWardsSlot I) σ_solm I :=
      accountMapEquiv_storage_findD hAccounts I.codeOwner (flipperCallerWardsSlot I) ⟨0⟩
    intro hbad
    exact hauth (by rw [hword, hbad])
  have hbody :
      ExecTransitionBody config contract evm0 locals fileUintTransition.body .reverted := by
    simpa [evm0, locals] using
      (flipperFileUintSourceBodyAuthReverts (cA := cA) (gh := gh) (bl := bl)
        (σ := σ_solm) (σ₀ := σ₀) (A := A) (I := I) (g := g) hwv hauthSolm)
  obtain ⟨_, _, hdecoded⟩ := flipperFileUintX_decoded (g := Sat256.ofUInt256 g)
    hsz68 hsize hreach
  exact (flipperFileUintX_unauthorized (I := I) hauth hdecoded)
    |>.reEquivExecutionRevert hcode hdispatch hdecode hbody

theorem flipperFileUintBodyCoreUnrecognized
    {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256} {sel : UInt256}
    (hcode : I.code = flipperBytecode) (hsize : I.calldata.size < UInt256.size)
    (hwv : I.weiValue = ⟨0⟩)
    (hsz68 : 68 ≤ I.calldata.size)
    (hauth : flipperSlotWord (flipperCallerWardsSlot I) σ_evm I = ⟨1⟩)
    (hnotBeg : fileUintWhat I ≠ fileUintBegBytes)
    (hnotTtl : fileUintWhat I ≠ fileUintTtlBytes)
    (hnotTau : fileUintWhat I ≠ fileUintTauBytes)
    (hdispatch : dispatchMsg contract I.calldata = some fileUintTransition)
    (hdecode :
      decodeCalldataWithMode config.abiDecodeMode (fileUintTransition.params.map Param.name)
        (transitionSignature fileUintTransition).paramTypes I.calldata =
          some (fileUintLocals I))
    (hreach : ∃ k C, RD flipperBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) ⟨325⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ_evm) k C)
    (hAccounts : accountMapEquiv σ_evm σ_solm) :
    runtimeEquivalenceFor config contract cA gh bl σ_evm σ_solm σ₀ g A I := by
  let locals := fileUintLocals I
  let evm0 := initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I
  have hauthSolm : flipperSlotWord (flipperCallerWardsSlot I) σ_solm I = ⟨1⟩ := by
    have hword : flipperSlotWord (flipperCallerWardsSlot I) σ_evm I =
        flipperSlotWord (flipperCallerWardsSlot I) σ_solm I :=
      accountMapEquiv_storage_findD hAccounts I.codeOwner (flipperCallerWardsSlot I) ⟨0⟩
    rw [← hword]
    exact hauth
  have hbody :
      ExecTransitionBody config contract evm0 locals fileUintTransition.body .reverted := by
    simpa [evm0, locals] using
      (flipperFileUintSourceBodyUnrecognized (cA := cA) (gh := gh) (bl := bl)
        (σ := σ_solm) (σ₀ := σ₀) (A := A) (I := I) (g := g) hwv hauthSolm
        hnotBeg hnotTtl hnotTau)
  obtain ⟨_, _, hdecoded⟩ := flipperFileUintX_decoded (g := Sat256.ofUInt256 g)
    hsz68 hsize hreach
  obtain ⟨_, _, hswitch⟩ := flipperFileUintX_authorized (I := I) hauth hdecoded
  have hnotBegWord : calldataWord I.calldata 4 ≠ ABI.bytesToWord fileUintBegBytes :=
    fileUintWhatWord_ne_of_bytes_ne (by omega) hnotBeg fileUintBegBytes_length
  have hnotTtlWord : calldataWord I.calldata 4 ≠ ABI.bytesToWord fileUintTtlBytes :=
    fileUintWhatWord_ne_of_bytes_ne (by omega) hnotTtl fileUintTtlBytes_length
  have hnotTauWord : calldataWord I.calldata 4 ≠ ABI.bytesToWord fileUintTauBytes :=
    fileUintWhatWord_ne_of_bytes_ne (by omega) hnotTau fileUintTauBytes_length
  exact (flipperFileUintX_unrecognized hnotBegWord hnotTtlWord hnotTauWord hswitch)
    |>.reEquivExecutionRevert hcode hdispatch hdecode hbody

theorem flipperFileUintBodyCoreDecodeFailed_short
    {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256} {sel : UInt256}
    (hcode : I.code = flipperBytecode) (hsize : I.calldata.size < UInt256.size)
    (hsz4 : 4 ≤ I.calldata.size) (hshort : I.calldata.size < 68)
    (hdispatch : dispatchMsg contract I.calldata = some fileUintTransition)
    (hreach : ∃ k C, RD flipperBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) ⟨325⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ_evm) k C) :
    runtimeEquivalenceFor config contract cA gh bl σ_evm σ_solm σ₀ g A I := by
  exact (flipperFileUintX_shortarg (g := Sat256.ofUInt256 g) hsz4 hsize hshort hreach)
    |>.reEquivDecodingFailed hcode hdispatch
      (flipperDecode_fileUint_none_short hsz4 hshort)

theorem flipperFileUintBodyCore {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256}
    (hcode : I.code = flipperBytecode)
    (hsize : I.calldata.size < UInt256.size)
    (hperm : I.perm = true)
    (hwv : I.weiValue = ⟨0⟩)
    (hsel : selIs I (flipperSelBytes 7))
    (hAccounts : accountMapEquiv σ_evm σ_solm) :
    runtimeEquivalenceFor config contract cA gh bl σ_evm σ_solm σ₀ g A I := by
  have hsz4 : 4 ≤ I.calldata.size :=
    calldata_size_ge_of_selIs I (flipperSelBytes 7) rfl hsel
  have hdispatch : dispatchMsg contract I.calldata = some fileUintTransition :=
    flipperDispatchFileUint hsel
  have hreach := flipperReachFileUintBody (cA := cA) (gh := gh) (bl := bl)
    (σ := σ_evm) (σ₀ := σ₀) (A := A) (I := I) (g := Sat256.ofUInt256 g)
    hcode hwv hsz4 hsize hsel
  by_cases hsz68 : 68 ≤ I.calldata.size
  · by_cases hauth : flipperSlotWord (flipperCallerWardsSlot I) σ_evm I = ⟨1⟩
    · by_cases hbeg : fileUintWhat I = fileUintBegBytes
      · exact flipperFileUintBodyCoreOkBeg hcode hsize hperm hwv hsz68 hauth hbeg
          hdispatch (flipperDecode_fileUint_ok hsz68) hreach hAccounts
      · by_cases httl : fileUintWhat I = fileUintTtlBytes
        · exact flipperFileUintBodyCoreOkTtl hcode hsize hperm hwv hsz68 hauth hbeg httl
            hdispatch (flipperDecode_fileUint_ok hsz68) hreach hAccounts
        · by_cases htau : fileUintWhat I = fileUintTauBytes
          · exact flipperFileUintBodyCoreOkTau hcode hsize hperm hwv hsz68 hauth hbeg httl
              htau hdispatch (flipperDecode_fileUint_ok hsz68) hreach hAccounts
          · exact flipperFileUintBodyCoreUnrecognized hcode hsize hwv hsz68 hauth hbeg httl
              htau hdispatch (flipperDecode_fileUint_ok hsz68) hreach hAccounts
    · exact flipperFileUintBodyCoreUnauthorized hcode hsize hwv hsz68 hauth hdispatch
        (flipperDecode_fileUint_ok hsz68) hreach hAccounts
  · exact flipperFileUintBodyCoreDecodeFailed_short hcode hsize hsz4 (by omega)
      hdispatch hreach

end Benchmarks.Dss.Flipper
