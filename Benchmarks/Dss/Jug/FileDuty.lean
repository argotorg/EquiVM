import Benchmarks.Dss.Jug.FileBase
import Benchmarks.Dss.Jug.Ilks

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

set_option maxRecDepth 2000000
set_option maxHeartbeats 0

namespace Benchmarks.Dss.Jug

/-! ## `file(bytes32,bytes32,uint256)` -/

abbrev fileDutyIlkBytes (I : ExecutionEnv) : List UInt8 :=
  (I.calldata.toList.drop 4).take 32

abbrev fileDutyWhatBytes (I : ExecutionEnv) : List UInt8 :=
  (I.calldata.toList.drop 36).take 32

abbrev fileDutyIlkWord (I : ExecutionEnv) : UInt256 :=
  calldataWord I.calldata 4

abbrev fileDutyWhatWord (I : ExecutionEnv) : UInt256 :=
  calldataWord I.calldata 36

abbrev fileDutyData (I : ExecutionEnv) : UInt256 :=
  calldataWord I.calldata 68

abbrev fileDutyIlkKey (I : ExecutionEnv) : KeyValue :=
  .fixedBytes bytes32Width (fileDutyIlkBytes I)

abbrev fileDutyDutySlotFor (I : ExecutionEnv) : UInt256 :=
  ilksBase (fileDutyIlkKey I)

abbrev fileDutyRhoSlotFor (I : ExecutionEnv) : UInt256 :=
  fileDutyDutySlotFor I + ⟨1⟩

abbrev fileDutyDutyEvaledRef (I : ExecutionEnv) : EvaledStorageRef :=
  { base := "ilks", steps := [.mindex (fileDutyIlkKey I), .field "duty"] }

abbrev fileDutyRhoEvaledRef (I : ExecutionEnv) : EvaledStorageRef :=
  { base := "ilks", steps := [.mindex (fileDutyIlkKey I), .field "rho"] }

abbrev fileDutyBytes : List UInt8 :=
  [100, 117, 116, 121, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
   0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]

abbrev fileDutyLocals (I : ExecutionEnv) : Store :=
  (((∅ : Store).insert "ilk" (.fixedBytes bytes32Width (fileDutyIlkBytes I))).insert
    "what" (.fixedBytes bytes32Width (fileDutyWhatBytes I))).insert
    "data" (.int (Int.ofNat (fileDutyData I).toNat))

noncomputable abbrev fileDutyIlkHashMem (I : ExecutionEnv) : ByteArray :=
  twoWordHashMem (fileDutyIlkWord I) ⟨1⟩ (relyAuthHashMem I)

noncomputable abbrev fileDutyIlkStoreHashMem (I : ExecutionEnv) : ByteArray :=
  twoWordHashMem (fileDutyIlkWord I) ⟨1⟩ (fileDutyIlkHashMem I)

theorem fileDutyIlkBytes_length {I : ExecutionEnv} (hsz36 : 36 ≤ I.calldata.size) :
    (fileDutyIlkBytes I).length = 32 := by
  simp [fileDutyIlkBytes, List.length_take, List.length_drop, byteArray_toList_eq]
  omega

theorem fileDutyIlkBytes_len_min {I : ExecutionEnv} (hsz36 : 36 ≤ I.calldata.size) :
    min 32 (I.calldata.toList.length - 4) = bytes32Width.val + 1 := by
  have htlen : I.calldata.toList.length = I.calldata.size := by
    rw [byteArray_toList_eq, Array.length_toList]
    rfl
  rw [htlen]
  simp [bytes32Width]
  omega

theorem fileDutyWhatBytes_length {I : ExecutionEnv} (hsz68 : 68 ≤ I.calldata.size) :
    (fileDutyWhatBytes I).length = 32 := by
  simp [fileDutyWhatBytes, List.length_take, List.length_drop, byteArray_toList_eq]
  omega

theorem fileDutyWhatWord_eq {I : ExecutionEnv} (hsz68 : 68 ≤ I.calldata.size) :
    ABI.bytesToWord (fileDutyWhatBytes I) = fileDutyWhatWord I := by
  simpa [fileDutyWhatBytes, fileDutyWhatWord] using
    decode_word_at_eq I.calldata 36 (by omega) (by norm_num)

theorem fileDutyWhatWord_eq_of_bytes_eq {I : ExecutionEnv} {bs : List UInt8}
    (hsz68 : 68 ≤ I.calldata.size) (hbs : fileDutyWhatBytes I = bs) :
    fileDutyWhatWord I = ABI.bytesToWord bs := by
  rw [← hbs]
  exact (fileDutyWhatWord_eq (I := I) hsz68).symm

theorem fileDutyWhat_eq_of_word_eq {I : ExecutionEnv} {bs : List UInt8}
    (hsz68 : 68 ≤ I.calldata.size) (hword : fileDutyWhatWord I = ABI.bytesToWord bs)
    (hbsLen : bs.length = 32) :
    fileDutyWhatBytes I = bs := by
  have hto := toBytesBE_bytesToWord_of_length (bs := fileDutyWhatBytes I)
    (fileDutyWhatBytes_length (I := I) hsz68)
  rw [fileDutyWhatWord_eq (I := I) hsz68, hword] at hto
  exact hto.symm.trans (toBytesBE_bytesToWord_of_length (bs := bs) hbsLen)

theorem fileDutyWhatWord_ne_of_bytes_ne {I : ExecutionEnv} {bs : List UInt8}
    (hsz68 : 68 ≤ I.calldata.size) (hneq : fileDutyWhatBytes I ≠ bs)
    (hbsLen : bs.length = 32) :
    fileDutyWhatWord I ≠ ABI.bytesToWord bs := by
  intro hword
  exact hneq (fileDutyWhat_eq_of_word_eq hsz68 hword hbsLen)

theorem keyValueToWord_fileDutyIlkKey {I : ExecutionEnv} (hsz36 : 36 ≤ I.calldata.size) :
    keyValueToWord (fileDutyIlkKey I) = fileDutyIlkWord I := by
  have hlen32 : (fileDutyIlkBytes I).length = 32 := fileDutyIlkBytes_length hsz36
  have hword : ABI.bytesToWord (fileDutyIlkBytes I) = fileDutyIlkWord I := by
    simpa [fileDutyIlkBytes, fileDutyIlkWord] using
      decode_word_at_eq I.calldata 4 (by omega) (by norm_num)
  have hbytes : fileDutyIlkBytes I = EVM.Word.toBytesBE (fileDutyIlkWord I) := by
    have hto := toBytesBE_bytesToWord_of_length (bs := fileDutyIlkBytes I) hlen32
    rw [hword] at hto
    exact hto.symm
  simpa [fileDutyIlkKey, bytes32Width, hbytes] using
    keyValueToWord_fixedBytes32 (fileDutyIlkWord I)

theorem fileDutyDutySlotFor_eq {I : ExecutionEnv} (hsz36 : 36 ≤ I.calldata.size) :
    fileDutyDutySlotFor I = solcMappingSlot ⟨1⟩ (fileDutyIlkWord I) := by
  unfold fileDutyDutySlotFor ilksBase mapSlot solcMappingSlot
  rw [keyValueToWord_fileDutyIlkKey hsz36]

theorem fileDutyRhoSlotFor_eq {I : ExecutionEnv} (hsz36 : 36 ≤ I.calldata.size) :
    fileDutyRhoSlotFor I = solcMappingSlot ⟨1⟩ (fileDutyIlkWord I) + ⟨1⟩ := by
  simp [fileDutyRhoSlotFor, fileDutyDutySlotFor_eq hsz36]

theorem fileDutyIlkHashMem_size (I : ExecutionEnv) :
    (fileDutyIlkHashMem I).size = 96 := by
  exact twoWordHashMem_size_96 (fileDutyIlkWord I) ⟨1⟩ (relyAuthHashMem_size I)

theorem fileDutyIlkHashMem_read64 (I : ExecutionEnv) :
    (fileDutyIlkHashMem I).readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩ := by
  exact twoWordHashMem_read64 (fileDutyIlkWord I) ⟨1⟩
    (relyAuthHashMem_size I) (relyAuthHashMem_read64 I)

theorem fileDutyIlkStoreHashMem_size (I : ExecutionEnv) :
    (fileDutyIlkStoreHashMem I).size = 96 := by
  exact twoWordHashMem_size_96 (fileDutyIlkWord I) ⟨1⟩ (fileDutyIlkHashMem_size I)

-- LIBRARY CANDIDATE: legacy solc05 decoding for `(bytes32,bytes32,uint256)`.
theorem decodeABIValues_bytes32_bytes32_uint256_legacy_ok {bytes : List UInt8}
    (hlen0 : (bytes.take 32).length = 32)
    (hlen32 : ((bytes.drop 32).take 32).length = 32)
    (hlen64 : ((bytes.drop 64).take 32).length = 32) :
    decodeABIValues? [abiBytes32, abiBytes32, abiUInt256] bytes 0 0 96 96
        DecodeMode.legacySolc05 =
      some ([.fixedBytes abiBytes32Width (bytes.take 32),
        .fixedBytes abiBytes32Width ((bytes.drop 32).take 32),
        .int (Int.ofNat (ABI.bytesToWord ((bytes.drop 64).take 32)).toNat)], 96) := by
  simp [decodeABIValues?, abiBytes32, abiBytes32Width, abiUInt256, isDynamicABIType,
    staticABIEncodedSize?, decodeABIValue?, readBytes?, hlen0]
  have hlen32le : 32 ≤ bytes.length - 32 := by
    rw [List.length_take, List.length_drop] at hlen32
    omega
  rw [if_pos hlen32le]
  have hlen64le : 32 ≤ bytes.length - 64 := by
    rw [List.length_take, List.length_drop] at hlen64
    omega
  simp [readWord?, readBytes?, decodeABIWord?, hlen64]
  rw [Int.emod_eq_of_lt]
  · simp [UInt256.toNat]
  · exact Int.natCast_nonneg _
  · exact_mod_cast (ABI.bytesToWord ((bytes.drop 64).take 32)).val.isLt

-- LIBRARY CANDIDATE: legacy solc05 short-calldata rejection for `(bytes32,bytes32,uint256)`.
theorem decodeABIValues_bytes32_bytes32_uint256_legacy_none_short {bytes : List UInt8}
    (hshort : bytes.length < 96) :
    decodeABIValues? [abiBytes32, abiBytes32, abiUInt256] bytes 0 0 96 96
        DecodeMode.legacySolc05 =
      none := by
  simp only [decodeABIValues?, abiBytes32, abiBytes32Width, abiUInt256, isDynamicABIType,
    Bool.false_eq_true, if_false, staticABIEncodedSize?, bind, Option.bind, Nat.zero_add]
  by_cases h32 : bytes.length < 32
  · have hnot : ¬ 32 ≤ bytes.length := by omega
    simp [decodeABIValue?, readBytes?, hnot]
  · have htake0 : (bytes.take 32).length = 32 := by
      rw [List.length_take]
      omega
    simp [decodeABIValue?, readBytes?, htake0]
    by_cases h64 : bytes.length < 64
    · have htake32n : ¬ ((bytes.drop 32).take 32).length = 32 := by
        rw [List.length_take, List.length_drop]
        omega
      have hnot : ¬ 32 ≤ bytes.length - 32 := by
        rw [List.length_take, List.length_drop] at htake32n
        omega
      simp [readBytes?, hnot]
    · have htake32 : ((bytes.drop 32).take 32).length = 32 := by
        rw [List.length_take, List.length_drop]
        omega
      have hlen32le : 32 ≤ bytes.length - 32 := by omega
      rw [if_pos hlen32le]
      have hnot : ¬ 32 ≤ bytes.length - 64 := by omega
      simp [readWord?, readBytes?, hnot]

theorem decodeCalldata_legacyBytes32_bytes32_uint256_ok {cd : ByteArray}
    {x y z : Solm.Ident} (hsz100 : 100 ≤ cd.size) :
    decodeCalldataWithMode DecodeMode.legacySolc05 [x, y, z]
        [abiBytes32, abiBytes32, abiUInt256] cd =
      some ((((∅ : Solm.Store).insert x
        (.fixedBytes abiBytes32Width ((cd.toList.drop 4).take 32))).insert y
        (.fixedBytes abiBytes32Width ((cd.toList.drop 36).take 32))).insert z
        (.int (Int.ofNat (calldataWord cd 68).toNat))) := by
  have htlen : cd.toList.length = cd.size := by
    rw [byteArray_toList_eq, Array.length_toList]
    rfl
  have htake4 : ((cd.toList.drop 4).take 32).length = 32 := by
    rw [List.length_take, List.length_drop, htlen]
    omega
  have htake36 : ((cd.toList.drop 36).take 32).length = 32 := by
    rw [List.length_take, List.length_drop, htlen]
    omega
  have htake68 : ((cd.toList.drop 68).take 32).length = 32 := by
    rw [List.length_take, List.length_drop, htlen]
    omega
  have hword68 : ABI.bytesToWord ((cd.toList.drop 68).take 32) = calldataWord cd 68 :=
    decode_word_at_eq cd 68 (by omega) (by norm_num)
  unfold decodeCalldataWithMode decodeCalldata
  rw [if_neg (by rw [htlen]; omega : ¬ cd.toList.length < 4)]
  rw [if_neg (by simp [abiBytes32, abiUInt256, isDynamicABIType])]
  simp only [decodeCalldata.decodeArgs]
  rw [show abiTupleHeadSize? [abiBytes32, abiBytes32, abiUInt256] = some 96 by decide +native]
  simp only [bind, Option.bind]
  rw [decodeABIValues_bytes32_bytes32_uint256_legacy_ok (bytes := cd.toList.drop 4)
    (by simpa using htake4)
    (by simpa [List.drop_drop, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using htake36)
    (by simpa [List.drop_drop, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using htake68)]
  rw [if_neg (by rw [List.length_drop, htlen]; omega : ¬ (cd.toList.drop 4).length < 96)]
  simp [decodeCalldata.insertValues]
  rw [hword68]

theorem decodeCalldata_legacyBytes32_bytes32_uint256_none_short {cd : ByteArray}
    {x y z : Solm.Ident} (hsz4 : 4 ≤ cd.size) (hshort : cd.size < 100) :
    decodeCalldataWithMode DecodeMode.legacySolc05 [x, y, z]
        [abiBytes32, abiBytes32, abiUInt256] cd =
      none := by
  have htlen : cd.toList.length = cd.size := by
    rw [byteArray_toList_eq, Array.length_toList]
    rfl
  unfold decodeCalldataWithMode decodeCalldata
  rw [if_neg (by rw [htlen]; omega : ¬ cd.toList.length < 4)]
  rw [if_neg (by simp [abiBytes32, abiUInt256, isDynamicABIType])]
  simp only [decodeCalldata.decodeArgs]
  rw [show abiTupleHeadSize? [abiBytes32, abiBytes32, abiUInt256] = some 96 by decide +native]
  simp only [bind, Option.bind]
  by_cases hbytes : (cd.toList.drop 4).length < 96
  · rw [if_pos hbytes]
  · rw [if_neg hbytes]
    rw [decodeABIValues_bytes32_bytes32_uint256_legacy_none_short
      (bytes := cd.toList.drop 4) (by
        rw [List.length_drop, htlen]
        omega)]

theorem jugDecode_fileDuty_ok {I : ExecutionEnv} (hsz100 : 100 ≤ I.calldata.size) :
    decodeCalldataWithMode config.abiDecodeMode (fileDutyTransition.params.map Param.name)
      (transitionSignature fileDutyTransition).paramTypes I.calldata =
        some (fileDutyLocals I) := by
  simpa [config, fileDutyTransition, bytes32, bytes32Width, uint256, uint256Int,
    fileDutyLocals, fileDutyIlkBytes, fileDutyWhatBytes, fileDutyData, abiBytes32,
    abiBytes32Width, abiUInt256] using
    (decodeCalldata_legacyBytes32_bytes32_uint256_ok (cd := I.calldata) (x := "ilk")
      (y := "what") (z := "data") hsz100)

theorem jugDecode_fileDuty_none_short {I : ExecutionEnv}
    (hsz4 : 4 ≤ I.calldata.size) (hshort : I.calldata.size < 100) :
    decodeCalldataWithMode config.abiDecodeMode (fileDutyTransition.params.map Param.name)
      (transitionSignature fileDutyTransition).paramTypes I.calldata = none := by
  simpa [config, fileDutyTransition, bytes32, bytes32Width, uint256, uint256Int,
    abiBytes32, abiBytes32Width, abiUInt256] using
    (decodeCalldata_legacyBytes32_bytes32_uint256_none_short (cd := I.calldata) (x := "ilk")
      (y := "what") (z := "data") hsz4 hshort)

theorem fileDutyLocals_get_ilk (I : ExecutionEnv) :
    (fileDutyLocals I).get? "ilk" =
      some (.fixedBytes bytes32Width (fileDutyIlkBytes I)) := by
  rw [fileDutyLocals, store_get_ne _ _ (by decide), store_get_ne _ _ (by decide),
    store_get_self]

theorem fileDutyLocals_get_what (I : ExecutionEnv) :
    (fileDutyLocals I).get? "what" =
      some (.fixedBytes bytes32Width (fileDutyWhatBytes I)) := by
  rw [fileDutyLocals, store_get_ne _ _ (by decide), store_get_self]

theorem fileDutyLocals_get_data (I : ExecutionEnv) :
    (fileDutyLocals I).get? "data" =
      some (.int (Int.ofNat (fileDutyData I).toNat)) := by
  rw [fileDutyLocals, store_get_self]

theorem fileDutyLocals_get_wards (I : ExecutionEnv) :
    (fileDutyLocals I).get? "wards" = none := by
  rw [fileDutyLocals, store_get_ne _ _ (by decide), store_get_ne _ _ (by decide),
    store_get_ne _ _ (by decide)]
  simp

theorem fileDutyLocals_get_ilks (I : ExecutionEnv) :
    (fileDutyLocals I).get? "ilks" = none := by
  rw [fileDutyLocals, store_get_ne _ _ (by decide), store_get_ne _ _ (by decide),
    store_get_ne _ _ (by decide)]
  simp

theorem evalExpr_fileDutyData {evm : EVM.State} {I : ExecutionEnv} {locals : Store}
    (h : locals.get? "data" = some (.int (Int.ofNat (fileDutyData I).toNat))) :
    evalExpr? config { contract := contract, locals := locals } evm (.var "data") =
      .ok (.int (Int.ofNat (fileDutyData I).toNat)) := by
  rw [evalExpr?]
  change EvalResult.ofOption EvalError.unboundVariable (locals.get? "data") =
    .ok (.int (Int.ofNat (fileDutyData I).toNat))
  rw [h]
  rfl

theorem evalExpr_fileDutyWhatEq_true {evm : EVM.State} {I : ExecutionEnv} {locals : Store}
    {bs : List UInt8}
    (hget : locals.get? "what" = some (.fixedBytes bytes32Width (fileDutyWhatBytes I)))
    (hwhat : fileDutyWhatBytes I = bs) :
    evalExpr? config { contract := contract, locals := locals } evm
      (.binary .eq (.var "what") (.fixedBytesLit bytes32Width bs)) = .ok (.bool true) := by
  have hvar :
      evalExpr? config { contract := contract, locals := locals } evm (.var "what") =
        .ok (.fixedBytes bytes32Width (fileDutyWhatBytes I)) := by
    rw [evalExpr?]
    change EvalResult.ofOption EvalError.unboundVariable (locals.get? "what") =
      .ok (.fixedBytes bytes32Width (fileDutyWhatBytes I))
    rw [hget]
    rfl
  rw [evalExpr?]
  simp only [hvar, EvalResult.bind, bind]
  simp [evalExpr?, evalBinaryOp?, hwhat]
  all_goals decide

theorem evalExpr_fileDutyWhatEq_false {evm : EVM.State} {I : ExecutionEnv} {locals : Store}
    {bs : List UInt8}
    (hget : locals.get? "what" = some (.fixedBytes bytes32Width (fileDutyWhatBytes I)))
    (hwhat : fileDutyWhatBytes I ≠ bs) :
    evalExpr? config { contract := contract, locals := locals } evm
      (.binary .eq (.var "what") (.fixedBytesLit bytes32Width bs)) = .ok (.bool false) := by
  have hvar :
      evalExpr? config { contract := contract, locals := locals } evm (.var "what") =
        .ok (.fixedBytes bytes32Width (fileDutyWhatBytes I)) := by
    rw [evalExpr?]
    change EvalResult.ofOption EvalError.unboundVariable (locals.get? "what") =
      .ok (.fixedBytes bytes32Width (fileDutyWhatBytes I))
    rw [hget]
    rfl
  rw [evalExpr?]
  simp only [hvar, EvalResult.bind, bind]
  simp [evalExpr?, evalBinaryOp?, hwhat]
  all_goals decide

theorem evalExpr_fileDutyStorageDuty (evm : EVM.State) (I : ExecutionEnv)
    (hsz36 : 36 ≤ I.calldata.size) :
    evalExpr? config { contract := contract, locals := fileDutyLocals I } evm
      (.storage (ilksF (.var "ilk") "duty")) =
        .ok (.int (Int.ofNat
          (jugSlotWord (fileDutyDutySlotFor I) evm.accountMap evm.executionEnv).toNat)) := by
  exact evalExpr_storage_scalar_value
    (cfg := config) (solm := { contract := contract, locals := fileDutyLocals I }) (evm := evm)
    (slot := ilksF (.var "ilk") "duty") (er := fileDutyDutyEvaledRef I)
    (t := .int uint256Int) (loc := wordLoc (fileDutyDutySlotFor I))
    (value := .int (Int.ofNat
      (jugSlotWord (fileDutyDutySlotFor I) evm.accountMap evm.executionEnv).toNat))
    (fileDutyLocals_get_ilks I)
    (by
      have hkeyLen : (fileDutyIlkBytes I).length = ↑bytes32Width + 1 := by
        simpa [bytes32Width] using fileDutyIlkBytes_length (I := I) hsz36
      simp [fileDutyDutyEvaledRef, fileDutyIlkKey, evalStorageRef, evalStorageRefSteps,
        evalStorageRefStep, ilksF, evalExpr?, valueToKey?,
        ← Std.HashMap.get?_eq_getElem?, fileDutyLocals_get_ilk I, EvalResult.ofOption,
        EvalResult.bind, pure, bind, hkeyLen])
    (by
      simp [fileDutyIlkKey, storageTypeAt?, storageTypeStep?, contract, storageDecls,
        IlkStructTy, uint256St])
    (by rfl)
    (by simpa [jugSlotWord] using jugStorageLocLoad_uint256 evm (fileDutyDutySlotFor I))

theorem evalExpr_fileDutyStorageRho (evm : EVM.State) (I : ExecutionEnv)
    (hsz36 : 36 ≤ I.calldata.size) :
    evalExpr? config { contract := contract, locals := fileDutyLocals I } evm
      (.storage (ilksF (.var "ilk") "rho")) =
        .ok (.int (Int.ofNat
          (jugSlotWord (fileDutyRhoSlotFor I) evm.accountMap evm.executionEnv).toNat)) := by
  exact evalExpr_storage_scalar_value
    (cfg := config) (solm := { contract := contract, locals := fileDutyLocals I }) (evm := evm)
    (slot := ilksF (.var "ilk") "rho") (er := fileDutyRhoEvaledRef I)
    (t := .int uint256Int) (loc := wordLoc (fileDutyRhoSlotFor I))
    (value := .int (Int.ofNat
      (jugSlotWord (fileDutyRhoSlotFor I) evm.accountMap evm.executionEnv).toNat))
    (fileDutyLocals_get_ilks I)
    (by
      have hkeyLen : (fileDutyIlkBytes I).length = ↑bytes32Width + 1 := by
        simpa [bytes32Width] using fileDutyIlkBytes_length (I := I) hsz36
      simp [fileDutyRhoEvaledRef, fileDutyIlkKey, evalStorageRef, evalStorageRefSteps,
        evalStorageRefStep, ilksF, evalExpr?, valueToKey?,
        ← Std.HashMap.get?_eq_getElem?, fileDutyLocals_get_ilk I, EvalResult.ofOption,
        EvalResult.bind, pure, bind, hkeyLen])
    (by
      simp [fileDutyIlkKey, storageTypeAt?, storageTypeStep?, contract, storageDecls,
        IlkStructTy, uint256St])
    (by rfl)
    (by simpa [jugSlotWord] using jugStorageLocLoad_uint256 evm (fileDutyRhoSlotFor I))

theorem evalExpr_fileDutyNowEqRho_true {evm : EVM.State} {I : ExecutionEnv}
    (hsz36 : 36 ≤ I.calldata.size)
    (htime :
      jugSlotWord (fileDutyRhoSlotFor I) evm.accountMap evm.executionEnv =
        UInt256.ofNat evm.executionEnv.header.timestamp) :
    evalExpr? config { contract := contract, locals := fileDutyLocals I } evm
      (.binary .eq (.env .timestamp) (.storage (ilksF (.var "ilk") "rho"))) =
        .ok (.bool true) := by
  have hrho := evalExpr_fileDutyStorageRho evm I hsz36
  have hval :
      (Value.int (Int.ofNat (UInt256.ofNat evm.executionEnv.header.timestamp).toNat) ==
        Value.int (Int.ofNat
          (jugSlotWord (fileDutyRhoSlotFor I) evm.accountMap evm.executionEnv).toNat)) =
        true := by
    rw [← htime]
    simp
  simp only [evalExpr?, envValue, hrho, EvalResult.bind, bind, pure, evalBinaryOp?, hval]

theorem evalExpr_fileDutyNowEqRho_false {evm : EVM.State} {I : ExecutionEnv}
    (hsz36 : 36 ≤ I.calldata.size)
    (htime :
      UInt256.ofNat evm.executionEnv.header.timestamp ≠
        jugSlotWord (fileDutyRhoSlotFor I) evm.accountMap evm.executionEnv) :
    evalExpr? config { contract := contract, locals := fileDutyLocals I } evm
      (.binary .eq (.env .timestamp) (.storage (ilksF (.var "ilk") "rho"))) =
        .ok (.bool false) := by
  have hrho := evalExpr_fileDutyStorageRho evm I hsz36
  have hval :
      (Value.int (Int.ofNat (UInt256.ofNat evm.executionEnv.header.timestamp).toNat) ==
        Value.int (Int.ofNat
          (jugSlotWord (fileDutyRhoSlotFor I) evm.accountMap evm.executionEnv).toNat)) =
        false := by
    rw [beq_eq_false_iff_ne]
    intro hbad
    rw [Value.int.injEq] at hbad
    exact htime (u256_inj (Int.ofNat.inj hbad))
  simp only [evalExpr?, envValue, hrho, EvalResult.bind, bind, pure, evalBinaryOp?, hval]

theorem assign_fileDutyStorage (evm : EVM.State) (I : ExecutionEnv)
    (hsz36 : 36 ≤ I.calldata.size) :
    let evm' := Solm.EVM.storageStore evm evm.executionEnv.codeOwner (fileDutyDutySlotFor I)
      (fileDutyData I)
    assignStorageRef? config { contract := contract, locals := fileDutyLocals I } evm
      .storage (ilksF (.var "ilk") "duty") (.int (Int.ofNat (fileDutyData I).toNat)) =
        .ok ({ contract := contract, locals := fileDutyLocals I }, evm') := by
  intro evm'
  apply assignStorageRef_storage_scalar
      (ty := uint256St)
      (er := fileDutyDutyEvaledRef I)
      (loc := wordLoc (fileDutyDutySlotFor I))
      (hbase := fileDutyLocals_get_ilks I)
      (her := by
        have hkeyLen : (fileDutyIlkBytes I).length = ↑bytes32Width + 1 := by
          simpa [bytes32Width] using fileDutyIlkBytes_length (I := I) hsz36
        simp [fileDutyDutyEvaledRef, fileDutyIlkKey, evalStorageRef, evalStorageRefSteps,
          evalStorageRefStep, ilksF, evalExpr?, valueToKey?,
          ← Std.HashMap.get?_eq_getElem?, fileDutyLocals_get_ilk I, EvalResult.ofOption,
          EvalResult.bind, pure, bind, hkeyLen])
      (hty := by
        simp [fileDutyIlkKey, storageTypeAt?, storageTypeStep?, contract, storageDecls,
          IlkStructTy, uint256St])
      (hloc := by rfl)
  simpa [evm'] using jugStorageLocStore_uint256 evm (fileDutyDutySlotFor I) (fileDutyData I)

theorem jugFileDutySourceBody {cA gh bl σ σ₀ A I} {g : UInt256}
    (hwv : I.weiValue = ⟨0⟩)
    (hsz36 : 36 ≤ I.calldata.size)
    (hauth : relyAuthWord σ I = ⟨1⟩)
    (htime : jugSlotWord (fileDutyRhoSlotFor I) σ I = UInt256.ofNat I.header.timestamp)
    (hwhat : fileDutyWhatBytes I = fileDutyBytes) :
    let locals := fileDutyLocals I
    let evm0 := initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I
    let evm1 := Solm.EVM.storageStore evm0 I.codeOwner (fileDutyDutySlotFor I) (fileDutyData I)
    ExecTransitionBody config contract evm0 locals fileDutyTransition.body
      (.returned { contract := contract, locals := locals } evm1 none) := by
  intro locals evm0 evm1
  have hguard :
      evalExpr? config { contract := contract, locals := locals } evm0
        (.binary .eq (.storage (wardsRef sender)) (.intLit 1)) = .ok (.bool true) := by
    exact evalExpr_auth_true_of_wards_none evm0 I locals
      (by simpa [locals] using fileDutyLocals_get_wards I)
      (by simp [evm0, initState])
      (by
        simpa [evm0, relyAuthWord, jugSlotWord, initState, Solm.EVM.storageLoad,
          State.lookupAccount] using hauth)
  have htimeGuard :
      evalExpr? config { contract := contract, locals := locals } evm0
        (.binary .eq (.env .timestamp) (.storage (ilksF (.var "ilk") "rho"))) =
          .ok (.bool true) := by
    simpa [locals, evm0, initState, jugSlotWord] using
      (evalExpr_fileDutyNowEqRho_true (evm := evm0) (I := I) hsz36 (by
        simpa [evm0, initState, jugSlotWord] using htime))
  have hcond :
      evalExpr? config { contract := contract, locals := locals } evm0
        (.binary .eq (.var "what") dutyParamLit) = .ok (.bool true) := by
    simpa [dutyParamLit, fileDutyBytes] using
      (evalExpr_fileDutyWhatEq_true (evm := evm0) (I := I) (locals := locals)
        (bs := fileDutyBytes) (by simpa [locals] using fileDutyLocals_get_what I) hwhat)
  have hdata :
      evalExpr? config { contract := contract, locals := locals } evm0 (.var "data") =
        .ok (.int (Int.ofNat (fileDutyData I).toNat)) := by
    exact evalExpr_fileDutyData (evm := evm0) (I := I) (locals := locals)
      (by simpa [locals] using fileDutyLocals_get_data I)
  have hassign :
      assignStorageRef? config { contract := contract, locals := locals } evm0
        .storage (ilksF (.var "ilk") "duty") (.int (Int.ofNat (fileDutyData I).toNat)) =
          .ok ({ contract := contract, locals := locals }, evm1) := by
    simpa [locals, evm1] using assign_fileDutyStorage evm0 I hsz36
  have hthen :
      ExecBlock config { contract := contract, locals := locals } evm0
        [.assign .storage (ilksF (.var "ilk") "duty") (.var "data")]
        (.ok { contract := contract, locals := locals } evm1) := by
    exact ExecBlock.consNormal (ExecStmt.assign hdata hassign) ExecBlock.nil
  have hblock :
      ExecBlock config { contract := contract, locals := locals } evm0 fileDutyTransition.body
        (.ok { contract := contract, locals := locals } evm1) := by
    refine ExecBlock.consNormal (ExecStmt.requireTrue ?_) ?_
    · exact evalCallvalueEq_true (by simp [evm0, initState]; exact hwv)
    refine ExecBlock.consNormal (ExecStmt.requireTrue hguard) ?_
    refine ExecBlock.consNormal (ExecStmt.requireTrue htimeGuard) ?_
    exact ExecBlock.consNormal (ExecStmt.iteTrue hcond hthen) ExecBlock.nil
  simpa [ExecTransitionBody, locals, evm0, evm1] using ExecFuncBody.execBlockOK hblock

theorem jugFileDutySourceBodyAuthReverts {cA gh bl σ σ₀ A I} {g : UInt256}
    (hwv : I.weiValue = ⟨0⟩)
    (hauth : relyAuthWord σ I ≠ ⟨1⟩) :
    let locals := fileDutyLocals I
    let evm0 := initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I
    ExecTransitionBody config contract evm0 locals fileDutyTransition.body .reverted := by
  intro locals evm0
  have hguard :
      evalExpr? config { contract := contract, locals := locals } evm0
        (.binary .eq (.storage (wardsRef sender)) (.intLit 1)) = .ok (.bool false) := by
    exact evalExpr_auth_false_of_wards_none evm0 I locals
      (by simpa [locals] using fileDutyLocals_get_wards I)
      (by simp [evm0, initState])
      (by
        simpa [evm0, relyAuthWord, jugSlotWord, initState, Solm.EVM.storageLoad,
          State.lookupAccount] using hauth)
  refine ExecFuncBody.execBlockRevert ?_
  simpa [fileDutyTransition, nonpayable, auth] using
    nonpayableSecondRequireReverts
      (cfg := config)
      (solm := { contract := contract, locals := locals })
      (evm := evm0)
      (guard := .binary .eq (.storage (wardsRef sender)) (.intLit 1))
      (rest := [.require (.binary .eq (.env .timestamp) (.storage (ilksF (.var "ilk") "rho"))),
        .ite (.binary .eq (.var "what") dutyParamLit)
          [.assign .storage (ilksF (.var "ilk") "duty") (.var "data")]
          [.require (.boolLit false)]])
      (by simp [evm0, initState]; exact hwv)
      hguard

theorem jugFileDutySourceBodyRhoReverts {cA gh bl σ σ₀ A I} {g : UInt256}
    (hwv : I.weiValue = ⟨0⟩)
    (hsz36 : 36 ≤ I.calldata.size)
    (hauth : relyAuthWord σ I = ⟨1⟩)
    (htime :
      UInt256.ofNat I.header.timestamp ≠ jugSlotWord (fileDutyRhoSlotFor I) σ I) :
    let locals := fileDutyLocals I
    let evm0 := initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I
    ExecTransitionBody config contract evm0 locals fileDutyTransition.body .reverted := by
  intro locals evm0
  have hguard :
      evalExpr? config { contract := contract, locals := locals } evm0
        (.binary .eq (.storage (wardsRef sender)) (.intLit 1)) = .ok (.bool true) := by
    exact evalExpr_auth_true_of_wards_none evm0 I locals
      (by simpa [locals] using fileDutyLocals_get_wards I)
      (by simp [evm0, initState])
      (by
        simpa [evm0, relyAuthWord, jugSlotWord, initState, Solm.EVM.storageLoad,
          State.lookupAccount] using hauth)
  have htimeGuard :
      evalExpr? config { contract := contract, locals := locals } evm0
        (.binary .eq (.env .timestamp) (.storage (ilksF (.var "ilk") "rho"))) =
          .ok (.bool false) := by
    simpa [locals, evm0, initState, jugSlotWord] using
      (evalExpr_fileDutyNowEqRho_false (evm := evm0) (I := I) hsz36 (by
        simpa [evm0, initState, jugSlotWord] using htime))
  have hblock :
      ExecBlock config { contract := contract, locals := locals } evm0 fileDutyTransition.body
        .reverted := by
    refine ExecBlock.consNormal (ExecStmt.requireTrue ?_) ?_
    · exact evalCallvalueEq_true (by simp [evm0, initState]; exact hwv)
    refine ExecBlock.consNormal (ExecStmt.requireTrue hguard) ?_
    exact ExecBlock.consRevert (ExecStmt.requireFalse htimeGuard)
  simpa [ExecTransitionBody, locals, evm0] using ExecFuncBody.execBlockRevert hblock

theorem jugFileDutySourceBodyUnrecognized {cA gh bl σ σ₀ A I} {g : UInt256}
    (hwv : I.weiValue = ⟨0⟩)
    (hsz36 : 36 ≤ I.calldata.size)
    (hauth : relyAuthWord σ I = ⟨1⟩)
    (htime : jugSlotWord (fileDutyRhoSlotFor I) σ I = UInt256.ofNat I.header.timestamp)
    (hwhat : fileDutyWhatBytes I ≠ fileDutyBytes) :
    let locals := fileDutyLocals I
    let evm0 := initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I
    ExecTransitionBody config contract evm0 locals fileDutyTransition.body .reverted := by
  intro locals evm0
  have hguard :
      evalExpr? config { contract := contract, locals := locals } evm0
        (.binary .eq (.storage (wardsRef sender)) (.intLit 1)) = .ok (.bool true) := by
    exact evalExpr_auth_true_of_wards_none evm0 I locals
      (by simpa [locals] using fileDutyLocals_get_wards I)
      (by simp [evm0, initState])
      (by
        simpa [evm0, relyAuthWord, jugSlotWord, initState, Solm.EVM.storageLoad,
          State.lookupAccount] using hauth)
  have htimeGuard :
      evalExpr? config { contract := contract, locals := locals } evm0
        (.binary .eq (.env .timestamp) (.storage (ilksF (.var "ilk") "rho"))) =
          .ok (.bool true) := by
    simpa [locals, evm0, initState, jugSlotWord] using
      (evalExpr_fileDutyNowEqRho_true (evm := evm0) (I := I) hsz36 (by
        simpa [evm0, initState, jugSlotWord] using htime))
  have hcond :
      evalExpr? config { contract := contract, locals := locals } evm0
        (.binary .eq (.var "what") dutyParamLit) = .ok (.bool false) := by
    simpa [dutyParamLit, fileDutyBytes] using
      (evalExpr_fileDutyWhatEq_false (evm := evm0) (I := I) (locals := locals)
        (bs := fileDutyBytes) (by simpa [locals] using fileDutyLocals_get_what I) hwhat)
  have hreqFalse :
      evalExpr? config { contract := contract, locals := locals } evm0 (.boolLit false) =
        .ok (.bool false) := by
    simp [evalExpr?, pure]
  have helse :
      ExecBlock config { contract := contract, locals := locals } evm0
        [.require (.boolLit false)] .reverted := by
    exact ExecBlock.consRevert (ExecStmt.requireFalse hreqFalse)
  have hblock :
      ExecBlock config { contract := contract, locals := locals } evm0 fileDutyTransition.body
        .reverted := by
    refine ExecBlock.consNormal (ExecStmt.requireTrue ?_) ?_
    · exact evalCallvalueEq_true (by simp [evm0, initState]; exact hwv)
    refine ExecBlock.consNormal (ExecStmt.requireTrue hguard) ?_
    refine ExecBlock.consNormal (ExecStmt.requireTrue htimeGuard) ?_
    exact ExecBlock.consRevert (ExecStmt.iteFalse hcond helse)
  simpa [ExecTransitionBody, locals, evm0] using ExecFuncBody.execBlockRevert hblock

theorem jugReachFileDutyBody {cA gh bl σ σ₀ A I} {g : Sat256}
    (hcode : I.code = jugBytecode) (hwv : I.weiValue = ⟨0⟩)
    (hsz : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hsel : selIs I (jugSelBytes 4)) :
    ∃ k C, RD jugBytecode I g (initState cA gh bl σ σ₀ g A I)
        ⟨185⟩ [jugSelWord I] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty
        (cA, σ) k C := by
  have hword : jugSelWord I = ⟨0x1a0b287e⟩ :=
    jugSelWord_eq_of_beq I hsz 0x1a 0x0b 0x28 0x7e ⟨0x1a0b287e⟩
      (by decide +native) (by simpa [jugSelBytes] using hsel)
  have hroot : UInt256.gt (armSelNat jugBytecode jugRootSplitPc) (jugSelWord I) ≠ ⟨0⟩ := by
    rw [hword]
    decide +native
  have heq0 : ∀ j, j < 0 →
      UInt256.eq (armSelNat jugBytecode (nthArmPc jugBytecode jugLowFirstArmPc j))
        (jugSelWord I) = ⟨0⟩ := by
    intro j hj
    omega
  have htake :
      UInt256.eq (armSelNat jugBytecode (nthArmPc jugBytecode jugLowFirstArmPc 0))
        (jugSelWord I) ≠ ⟨0⟩ := by
    rw [hword]
    decide +native
  exact jugReachLowBody 0 (by omega) ⟨185⟩ hcode hwv hsz hsize hroot heq0 htake
    (by jump_dest) (by decide +native)

theorem RD.jugFileDutyDecodeToRoutine {code : ByteArray} {g : Sat256} {s0 : State}
    {ee : ExecutionEnv} {k C : ℕ} {ret de sel : UInt256} {R : List UInt256}
    {mem rdata : ByteArray} {aw : UInt256}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    (h : RD code ee g s0 ⟨207⟩ (de :: ⟨4⟩ :: ret :: sel :: R) mem aw rdata acc k C)
    (hwf : code = jugBytecode)
    (hroutine : (D_J code 0).contains ⟨603⟩ = true)
    (hov : R.length + 10 ≤ 1024) :
    ∃ k' C', RD code ee g s0 ⟨603⟩
      (calldataWord ee.calldata 68 :: calldataWord ee.calldata 36 ::
        calldataWord ee.calldata 4 :: ret :: sel :: R)
      mem aw rdata acc k' C' := by
  subst hwf
  have rd208 := h.jumpdest (by decide +native) (by evm_ov)
  have rd209 := rd208.pop (by decide +native) (by evm_ov)
  have rd210 := rd209.dup1 (by decide +native) (by evm_ov)
  have rd211 := rd210.calldataload (by decide +native) (by evm_ov)
  have rd212 := rd211.swap1 (by decide +native) (by evm_ov)
  have rd214 := rd212.push1 ⟨32⟩ (by decide +native) (by evm_ov)
  have rd215 := rd214.dup2 (by decide +native) (by evm_ov)
  have rd216 := rd215.add (by decide +native) (by evm_ov)
  have rd217 := rd216.calldataload (by decide +native) (by evm_ov)
  have rd218 := rd217.swap1 (by decide +native) (by evm_ov)
  have rd220 := rd218.push1 ⟨64⟩ (by decide +native) (by evm_ov)
  have rd221 := rd220.add (by decide +native) (by evm_ov)
  have rd222 := rd221.calldataload (by decide +native) (by evm_ov)
  have rd225 := rd222.push2 ⟨603⟩ (by decide +native) (by evm_ov)
  exact ⟨_, _, by
    simpa [calldataWord, show (⟨4⟩ : UInt256).toNat = 4 from by decide,
      show (⟨36⟩ : UInt256).toNat = 36 from by decide,
      show (⟨68⟩ : UInt256).toNat = 68 from by decide]
      using rd225.jump (by decide +native) hroutine (by evm_ov)⟩

theorem jugFileDutyX_decoded {cA gh bl σ σ₀ A I} {g : Sat256} {sel : UInt256}
    (hsz100 : 100 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hreach : ∃ k C, RD jugBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨185⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    ∃ k C, RD jugBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨603⟩
        [fileDutyData I, fileDutyWhatWord I, fileDutyIlkWord I, ⟨226⟩, sel]
        solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
  obtain ⟨_, _, hdecoded⟩ := RD.solcExternalStaticArgsLenOk
    (code := jugBytecode) (sel := sel) (entry := ⟨185⟩) (ret := ⟨226⟩)
    (decoded := ⟨207⟩) (need := ⟨96⟩) hreach
    (by decide +native) (by decide +native) (by decide +native) (by decide +native)
    (by decide +native) (by decide +native) (by decide +native) (by decide +native)
    (by decide +native) (by decide +native) (by decide +native) (by decide +native)
    (by jump_dest)
    (by
      exact solcDecodeLenCheckOkUnsigned (by simpa using hsz100) hsize)
  obtain ⟨_, _, hroutine⟩ := RD.jugFileDutyDecodeToRoutine
    (code := jugBytecode) (ret := ⟨226⟩) (sel := sel) (R := [])
    hdecoded rfl (by jump_dest) (by simp)
  exact ⟨_, _, by simpa [fileDutyData, fileDutyWhatWord, fileDutyIlkWord] using hroutine⟩

set_option maxHeartbeats 1000000 in
theorem jugFileDutyX_authorized {cA σ I} {g : Sat256} {s0 : State} {k C : ℕ}
    {sel : UInt256} (hauth : relyAuthWord σ I = ⟨1⟩)
    (h : RD jugBytecode I g s0 ⟨603⟩
      [fileDutyData I, fileDutyWhatWord I, fileDutyIlkWord I, ⟨226⟩, sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    ∃ k' C', RD jugBytecode I g s0 ⟨692⟩
      [fileDutyData I, fileDutyWhatWord I, fileDutyIlkWord I, ⟨226⟩, sel]
      (relyAuthHashMem I) (UInt256.ofNat 3) ByteArray.empty (cA, σ) k' C' := by
  have hauthSlot :
      UInt256.ofNat (fromByteArrayBigEndian
          (ffi.KEC ((relyAuthHashMem I).readWithPadding 0 64))) =
        mapSlot (relySourceWord I) ⟨0⟩ := by
    simpa [relyAuthHashMem, mapSlot, solcMappingSlot] using
      twoWordHashMem_solcMappingSlot (⟨0⟩ : UInt256) (relySourceWord I)
        solcFreePtrMem_size
  have rd609pre := evm_run h with [
    raw jumpdest (by decide +native) (by evm_ov),
    raw caller (by decide +native) (by evm_ov),
    raw push1 ⟨0⟩ (by decide +native) (by evm_ov),
    raw swap1 (by decide +native) (by evm_ov),
    raw dup2 (by decide +native) (by evm_ov)]
  have rd610 := rd609pre.mstore 0 (wordAt0Mem (relySourceWord I) solcFreePtrMem)
    (UInt256.ofNat 3) (by decide +native) mem_cost (by rfl) (by decide +native) (by evm_ov)
  have rd614pre := evm_run rd610 with [
    raw push1 ⟨32⟩ (by decide +native) (by evm_ov),
    raw dup2 (by decide +native) (by evm_ov),
    raw swap1 (by decide +native) (by evm_ov)]
  have rd615 := rd614pre.mstore 0 (relyAuthHashMem I)
    (UInt256.ofNat 3) (by decide +native) mem_cost (by rfl) (by decide +native) (by evm_ov)
  have rd618pre := evm_run rd615 with [
    raw push1 ⟨64⟩ (by decide +native) (by evm_ov),
    raw swap1 (by decide +native) (by evm_ov)]
  have rd619 := rd618pre.keccak256 0 (mapSlot (relySourceWord I) ⟨0⟩)
    (UInt256.ofNat 3) (by decide +native) mem_cost hauthSlot (by decide +native)
    (by evm_ov)
  obtain ⟨k620, C620, rd620raw⟩ := rd619.sload (by decide +native) (by evm_ov)
  have rd620 : RD jugBytecode I g s0 ⟨620⟩
      (relyAuthWord σ I :: fileDutyData I :: fileDutyWhatWord I :: fileDutyIlkWord I ::
        ⟨226⟩ :: [sel])
      (relyAuthHashMem I) (UInt256.ofNat 3) ByteArray.empty (cA, σ) k620 C620 := by
    simpa [relyAuthWord, jugSlotWord, relyAuthStorageSlot_eq_mapSlot_source I] using rd620raw
  have rd623pre := evm_run rd620 with [
    raw push1 ⟨1⟩ (by decide +native) (by evm_ov),
    raw eq (by decide +native) (by evm_ov)]
  rw [hauth, u256_eq_refl] at rd623pre
  have rd626 := rd623pre.pushConst (⟨692⟩ : UInt256)
    (width := 2) (op := .PUSH2) (by decide) (by decide +native) (by evm_ov)
  exact ⟨_, _, rd626.jumpiT (by decide +native) one_ne_zero_uint
    (by jump_dest) (by evm_ov)⟩

set_option maxHeartbeats 1000000 in
theorem jugFileDutyX_unauthorized {cA σ I} {g : Sat256} {s0 : State} {k C : ℕ}
    {sel : UInt256} (hauth : relyAuthWord σ I ≠ ⟨1⟩)
    (h : RD jugBytecode I g s0 ⟨603⟩
      [fileDutyData I, fileDutyWhatWord I, fileDutyIlkWord I, ⟨226⟩, sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    RDrev jugBytecode g s0 := by
  have hauthSlot :
      UInt256.ofNat (fromByteArrayBigEndian
          (ffi.KEC ((relyAuthHashMem I).readWithPadding 0 64))) =
        mapSlot (relySourceWord I) ⟨0⟩ := by
    simpa [relyAuthHashMem, mapSlot, solcMappingSlot] using
      twoWordHashMem_solcMappingSlot (⟨0⟩ : UInt256) (relySourceWord I)
        solcFreePtrMem_size
  have rd609pre := evm_run h with [
    raw jumpdest (by decide +native) (by evm_ov),
    raw caller (by decide +native) (by evm_ov),
    raw push1 ⟨0⟩ (by decide +native) (by evm_ov),
    raw swap1 (by decide +native) (by evm_ov),
    raw dup2 (by decide +native) (by evm_ov)]
  have rd610 := rd609pre.mstore 0 (wordAt0Mem (relySourceWord I) solcFreePtrMem)
    (UInt256.ofNat 3) (by decide +native) mem_cost (by rfl) (by decide +native) (by evm_ov)
  have rd614pre := evm_run rd610 with [
    raw push1 ⟨32⟩ (by decide +native) (by evm_ov),
    raw dup2 (by decide +native) (by evm_ov),
    raw swap1 (by decide +native) (by evm_ov)]
  have rd615 := rd614pre.mstore 0 (relyAuthHashMem I)
    (UInt256.ofNat 3) (by decide +native) mem_cost (by rfl) (by decide +native) (by evm_ov)
  have rd618pre := evm_run rd615 with [
    raw push1 ⟨64⟩ (by decide +native) (by evm_ov),
    raw swap1 (by decide +native) (by evm_ov)]
  have rd619 := rd618pre.keccak256 0 (mapSlot (relySourceWord I) ⟨0⟩)
    (UInt256.ofNat 3) (by decide +native) mem_cost hauthSlot (by decide +native)
    (by evm_ov)
  obtain ⟨k620, C620, rd620raw⟩ := rd619.sload (by decide +native) (by evm_ov)
  have rd620 : RD jugBytecode I g s0 ⟨620⟩
      (relyAuthWord σ I :: fileDutyData I :: fileDutyWhatWord I :: fileDutyIlkWord I ::
        ⟨226⟩ :: [sel])
      (relyAuthHashMem I) (UInt256.ofNat 3) ByteArray.empty (cA, σ) k620 C620 := by
    simpa [relyAuthWord, jugSlotWord, relyAuthStorageSlot_eq_mapSlot_source I] using rd620raw
  have rd623pre := evm_run rd620 with [
    raw push1 ⟨1⟩ (by decide +native) (by evm_ov),
    raw eq (by decide +native) (by evm_ov)]
  have heq : UInt256.eq (⟨1⟩ : UInt256) (relyAuthWord σ I) = ⟨0⟩ := by
    exact u256_eq_of_ne (by intro hbad; exact hauth hbad.symm)
  rw [heq] at rd623pre
  have rd626 := rd623pre.pushConst (⟨692⟩ : UInt256)
    (width := 2) (op := .PUSH2) (by decide) (by decide +native) (by evm_ov)
  have rd627 := rd626.jumpiNT (by decide +native) rfl (by evm_ov)
  exact RD.solcErrorStringRevertTail
    (pc := ⟨627⟩)
    (len := ⟨18⟩)
    (rawWord := ⟨0x129d59cbdb9bdd0b585d5d1a1bdc9a5e9959⟩)
    (shift := ⟨114⟩)
    (word := ⟨0x4a75672f6e6f742d617574686f72697a65640000000000000000000000000000⟩)
    (op := .PUSH18)
    (width := 18)
    rd627
    (by
      unfold solcErrorStringRevertTailWf
      repeat' first | apply And.intro | decide +native)
    (by decide)
    relyNotAuthorizedWord
    (relyAuthHashMem_size I)
    (relyAuthHashMem_read64 I)
    (by simp only [List.length_cons, List.length_nil]; omega)

theorem jugFileDutyX_rhoOk {cA σ I} {g : Sat256} {s0 : State} {k C : ℕ}
    {sel : UInt256} (hsz36 : 36 ≤ I.calldata.size)
    (htime : jugSlotWord (fileDutyRhoSlotFor I) σ I = UInt256.ofNat I.header.timestamp)
    (h : RD jugBytecode I g s0 ⟨692⟩
      [fileDutyData I, fileDutyWhatWord I, fileDutyIlkWord I, ⟨226⟩, sel]
      (relyAuthHashMem I) (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    ∃ k' C', RD jugBytecode I g s0 ⟨784⟩
      [fileDutyData I, fileDutyWhatWord I, fileDutyIlkWord I, ⟨226⟩, sel]
      (fileDutyIlkHashMem I) (UInt256.ofNat 3) ByteArray.empty (cA, σ) k' C' := by
  have hslot :
      UInt256.ofNat (fromByteArrayBigEndian
          (ffi.KEC ((fileDutyIlkHashMem I).readWithPadding 0 64))) =
        solcMappingSlot ⟨1⟩ (fileDutyIlkWord I) := by
    simpa [fileDutyIlkHashMem] using
      twoWordHashMem_solcMappingSlot (⟨1⟩ : UInt256) (fileDutyIlkWord I)
        (relyAuthHashMem_size I)
  have rd693 := h.jumpdest (by decide +native) (by evm_ov)
  have rd695 := rd693.push1 ⟨0⟩ (by decide +native) (by evm_ov)
  have rd696 := rd695.dup4 (by decide +native) (by evm_ov)
  have rd697pre := rd696.dup2 (by decide +native) (by evm_ov)
  have rd698 := rd697pre.mstore 0 (wordAt0Mem (fileDutyIlkWord I) (relyAuthHashMem I))
    (UInt256.ofNat 3) (by decide +native) mem_cost (by rfl) (by decide +native) (by evm_ov)
  have rd704pre := evm_run rd698 with [
    raw push1 ⟨1⟩ (by decide +native) (by evm_ov),
    raw push1 ⟨32⟩ (by decide +native) (by evm_ov),
    raw dup2 (by decide +native) (by evm_ov),
    raw swap1 (by decide +native) (by evm_ov)]
  have rd705 := rd704pre.mstore 0 (fileDutyIlkHashMem I)
    (UInt256.ofNat 3) (by decide +native) mem_cost (by rfl) (by decide +native) (by evm_ov)
  have rd709pre := evm_run rd705 with [
    raw push1 ⟨64⟩ (by decide +native) (by evm_ov),
    raw swap1 (by decide +native) (by evm_ov),
    raw swap2 (by decide +native) (by evm_ov)]
  have rd710 := rd709pre.keccak256 0 (solcMappingSlot ⟨1⟩ (fileDutyIlkWord I))
    (UInt256.ofNat 3) (by decide +native) mem_cost hslot (by decide +native) (by evm_ov)
  have rd711 := rd710.add (by decide +native) (by evm_ov)
  obtain ⟨k712, C712, rd712raw⟩ := rd711.sload (by decide +native) (by evm_ov)
  have rd712 : RD jugBytecode I g s0 ⟨712⟩
      (jugSlotWord (fileDutyRhoSlotFor I) σ I :: fileDutyData I :: fileDutyWhatWord I ::
        fileDutyIlkWord I :: ⟨226⟩ :: [sel])
      (fileDutyIlkHashMem I) (UInt256.ofNat 3) ByteArray.empty (cA, σ) k712 C712 := by
    simpa [jugSlotWord, fileDutyRhoSlotFor_eq hsz36] using rd712raw
  have rd713 := RD.timestamp rd712 (by decide +native) (by evm_ov)
  have rd714 := rd713.eq (by decide +native) (by evm_ov)
  rw [← htime, u256_eq_refl] at rd714
  have rd717 := rd714.pushConst (⟨784⟩ : UInt256)
    (width := 2) (op := .PUSH2) (by decide) (by decide +native) (by evm_ov)
  exact ⟨_, _, rd717.jumpiT (by decide +native) one_ne_zero_uint
    (by jump_dest) (by evm_ov)⟩

theorem jugFileDutyX_rhoReverts {cA σ I} {g : Sat256} {s0 : State} {k C : ℕ}
    {sel : UInt256} (hsz36 : 36 ≤ I.calldata.size)
    (htime :
      UInt256.ofNat I.header.timestamp ≠ jugSlotWord (fileDutyRhoSlotFor I) σ I)
    (h : RD jugBytecode I g s0 ⟨692⟩
      [fileDutyData I, fileDutyWhatWord I, fileDutyIlkWord I, ⟨226⟩, sel]
      (relyAuthHashMem I) (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    RDrev jugBytecode g s0 := by
  have hslot :
      UInt256.ofNat (fromByteArrayBigEndian
          (ffi.KEC ((fileDutyIlkHashMem I).readWithPadding 0 64))) =
        solcMappingSlot ⟨1⟩ (fileDutyIlkWord I) := by
    simpa [fileDutyIlkHashMem] using
      twoWordHashMem_solcMappingSlot (⟨1⟩ : UInt256) (fileDutyIlkWord I)
        (relyAuthHashMem_size I)
  have rd693 := h.jumpdest (by decide +native) (by evm_ov)
  have rd695 := rd693.push1 ⟨0⟩ (by decide +native) (by evm_ov)
  have rd696 := rd695.dup4 (by decide +native) (by evm_ov)
  have rd697pre := rd696.dup2 (by decide +native) (by evm_ov)
  have rd698 := rd697pre.mstore 0 (wordAt0Mem (fileDutyIlkWord I) (relyAuthHashMem I))
    (UInt256.ofNat 3) (by decide +native) mem_cost (by rfl) (by decide +native) (by evm_ov)
  have rd704pre := evm_run rd698 with [
    raw push1 ⟨1⟩ (by decide +native) (by evm_ov),
    raw push1 ⟨32⟩ (by decide +native) (by evm_ov),
    raw dup2 (by decide +native) (by evm_ov),
    raw swap1 (by decide +native) (by evm_ov)]
  have rd705 := rd704pre.mstore 0 (fileDutyIlkHashMem I)
    (UInt256.ofNat 3) (by decide +native) mem_cost (by rfl) (by decide +native) (by evm_ov)
  have rd709pre := evm_run rd705 with [
    raw push1 ⟨64⟩ (by decide +native) (by evm_ov),
    raw swap1 (by decide +native) (by evm_ov),
    raw swap2 (by decide +native) (by evm_ov)]
  have rd710 := rd709pre.keccak256 0 (solcMappingSlot ⟨1⟩ (fileDutyIlkWord I))
    (UInt256.ofNat 3) (by decide +native) mem_cost hslot (by decide +native) (by evm_ov)
  have rd711 := rd710.add (by decide +native) (by evm_ov)
  obtain ⟨k712, C712, rd712raw⟩ := rd711.sload (by decide +native) (by evm_ov)
  have rd712 : RD jugBytecode I g s0 ⟨712⟩
      (jugSlotWord (fileDutyRhoSlotFor I) σ I :: fileDutyData I :: fileDutyWhatWord I ::
        fileDutyIlkWord I :: ⟨226⟩ :: [sel])
      (fileDutyIlkHashMem I) (UInt256.ofNat 3) ByteArray.empty (cA, σ) k712 C712 := by
    simpa [jugSlotWord, fileDutyRhoSlotFor_eq hsz36] using rd712raw
  have rd713 := RD.timestamp rd712 (by decide +native) (by evm_ov)
  have rd714 := rd713.eq (by decide +native) (by evm_ov)
  have heq : UInt256.eq (UInt256.ofNat I.header.timestamp)
      (jugSlotWord (fileDutyRhoSlotFor I) σ I) = ⟨0⟩ := by
    exact u256_eq_of_ne htime
  rw [heq] at rd714
  have rd717 := rd714.pushConst (⟨784⟩ : UInt256)
    (width := 2) (op := .PUSH2) (by decide) (by decide +native) (by evm_ov)
  have rd718 := rd717.jumpiNT (by decide +native) rfl (by evm_ov)
  exact RD.solcErrorStringRevertTail
    (pc := ⟨718⟩)
    (len := ⟨19⟩)
    (rawWord := ⟨0x129d59cbdc9a1bcb5b9bdd0b5d5c19185d1959⟩)
    (shift := ⟨106⟩)
    (word := ⟨0x4a75672f72686f2d6e6f742d7570646174656400000000000000000000000000⟩)
    (op := .PUSH19)
    (width := 19)
    rd718
    (by
      unfold solcErrorStringRevertTailWf
      repeat' first | apply And.intro | decide +native)
    (by decide)
    (by decide +native)
    (fileDutyIlkHashMem_size I)
    (fileDutyIlkHashMem_read64 I)
    (by simp only [List.length_cons, List.length_nil]; omega)

theorem jugFileDutyX_storeAuthorized {cA σ I} {g : Sat256} {s0 : State} {k C : ℕ}
    {sel : UInt256} (hsz36 : 36 ≤ I.calldata.size) (hperm : I.perm = true)
    (hmatch : fileDutyWhatWord I = ABI.bytesToWord fileDutyBytes)
    (h : RD jugBytecode I g s0 ⟨784⟩
      [fileDutyData I, fileDutyWhatWord I, fileDutyIlkWord I, ⟨226⟩, sel]
      (fileDutyIlkHashMem I) (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    RDret jugBytecode g s0
      (cA, sstoreAccountMap I.codeOwner σ (fileDutyDutySlotFor I) (fileDutyData I))
      ByteArray.empty := by
  have hslot :
      UInt256.ofNat (fromByteArrayBigEndian
          (ffi.KEC ((fileDutyIlkStoreHashMem I).readWithPadding 0 64))) =
        solcMappingSlot ⟨1⟩ (fileDutyIlkWord I) := by
    simpa [fileDutyIlkStoreHashMem] using
      twoWordHashMem_solcMappingSlot (⟨1⟩ : UInt256) (fileDutyIlkWord I)
        (fileDutyIlkHashMem_size I)
  have rd785 := h.jumpdest (by decide +native) (by evm_ov)
  have rd786 := rd785.dup2 (by decide +native) (by evm_ov)
  have rd791 := rd786.pushConst (⟨0x64757479⟩ : UInt256)
    (width := 4) (op := .PUSH4) (by decide) (by decide +native) (by evm_ov)
  have rd793 := rd791.push1 ⟨224⟩ (by decide +native) (by evm_ov)
  have rd794 := rd793.shl (by decide +native) (by evm_ov)
  have hconst : UInt256.shiftLeft (⟨0x64757479⟩ : UInt256) ⟨224⟩ =
      ABI.bytesToWord fileDutyBytes := by
    decide +native
  rw [hmatch, ← hconst] at rd794
  have rd795 := rd794.eq (by decide +native) (by evm_ov)
  rw [uInt256_eq_self] at rd795
  have rd796 := rd795.iszero (by decide +native) (by evm_ov)
  rw [show UInt256.isZero (⟨1⟩ : UInt256) = ⟨0⟩ from by decide] at rd796
  have rd799 := rd796.pushConst (⟨821⟩ : UInt256)
    (width := 2) (op := .PUSH2) (by decide) (by decide +native) (by evm_ov)
  have rd800 := rd799.jumpiNT (by decide +native)
    (by decide : (⟨0⟩ : UInt256) = ⟨0⟩) (by evm_ov)
  have rd802 := rd800.push1 ⟨0⟩ (by decide +native) (by evm_ov)
  have rd803 := rd802.dup4 (by decide +native) (by evm_ov)
  have rd804pre := rd803.dup2 (by decide +native) (by evm_ov)
  have rd805 := rd804pre.mstore 0 (wordAt0Mem (fileDutyIlkWord I) (fileDutyIlkHashMem I))
    (UInt256.ofNat 3) (by decide +native) mem_cost (by rfl) (by decide +native) (by evm_ov)
  have rd809pre := evm_run rd805 with [
    raw push1 ⟨1⟩ (by decide +native) (by evm_ov),
    raw push1 ⟨32⟩ (by decide +native) (by evm_ov)]
  have rd810 := rd809pre.mstore 0 (fileDutyIlkStoreHashMem I)
    (UInt256.ofNat 3) (by decide +native) mem_cost (by rfl) (by decide +native) (by evm_ov)
  have rd813pre := evm_run rd810 with [
    raw push1 ⟨64⟩ (by decide +native) (by evm_ov),
    raw swap1 (by decide +native) (by evm_ov)]
  have rd814 := rd813pre.keccak256 0 (solcMappingSlot ⟨1⟩ (fileDutyIlkWord I))
    (UInt256.ofNat 3) (by decide +native) mem_cost hslot (by decide +native) (by evm_ov)
  have rd815 := rd814.dup2 (by decide +native) (by evm_ov)
  have rd816 := rd815.swap1 (by decide +native) (by evm_ov)
  obtain ⟨_, _, rd817⟩ := rd816.sstore hperm (by decide +native) (by evm_ov)
  have rd820 := rd817.push2 ⟨898⟩ (by decide +native) (by evm_ov)
  have rd898 := rd820.jump (by decide +native) (by jump_dest) (by evm_ov)
  have rd899 := rd898.jumpdest (by decide +native) (by evm_ov)
  have rd900 := rd899.pop (by decide +native) (by evm_ov)
  have rd901 := rd900.pop (by decide +native) (by evm_ov)
  have rd902 := rd901.pop (by decide +native) (by evm_ov)
  have rd226 := rd902.jump (by decide +native) (by jump_dest) (by evm_ov)
  have rd227 := rd226.jumpdest (by decide +native) (by evm_ov)
  simpa [fileDutyDutySlotFor_eq hsz36] using RD.stop rd227 (by decide +native) (by evm_ov)

theorem jugFileDutyX_unrecognized {cA σ I} {g : Sat256} {s0 : State} {k C : ℕ}
    {sel : UInt256}
    (hneq : fileDutyWhatWord I ≠ ABI.bytesToWord fileDutyBytes)
    (h : RD jugBytecode I g s0 ⟨784⟩
      [fileDutyData I, fileDutyWhatWord I, fileDutyIlkWord I, ⟨226⟩, sel]
      (fileDutyIlkHashMem I) (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    RDrev jugBytecode g s0 := by
  have rd785 := h.jumpdest (by decide +native) (by evm_ov)
  have rd786 := rd785.dup2 (by decide +native) (by evm_ov)
  have rd791 := rd786.pushConst (⟨0x64757479⟩ : UInt256)
    (width := 4) (op := .PUSH4) (by decide) (by decide +native) (by evm_ov)
  have rd793 := rd791.push1 ⟨224⟩ (by decide +native) (by evm_ov)
  have rd794 := rd793.shl (by decide +native) (by evm_ov)
  have hconst : UInt256.shiftLeft (⟨0x64757479⟩ : UInt256) ⟨224⟩ =
      ABI.bytesToWord fileDutyBytes := by
    decide +native
  rw [hconst] at rd794
  have rd795 := rd794.eq (by decide +native) (by evm_ov)
  have heq0 : UInt256.eq (ABI.bytesToWord fileDutyBytes) (fileDutyWhatWord I) = ⟨0⟩ := by
    exact u256_eq_of_ne (fun h => hneq h.symm)
  rw [heq0] at rd795
  have rd796 := rd795.iszero (by decide +native) (by evm_ov)
  rw [show UInt256.isZero (⟨0⟩ : UInt256) = ⟨1⟩ from by decide] at rd796
  have rd799 := rd796.pushConst (⟨821⟩ : UInt256)
    (width := 2) (op := .PUSH2) (by decide) (by decide +native) (by evm_ov)
  have rd821 := rd799.jumpiT (by decide +native) one_ne_zero_uint (by jump_dest)
    (by evm_ov)
  exact RD.jugFileUnrecognizedRevert rd821
    (fileDutyIlkHashMem_size I)
    (fileDutyIlkHashMem_read64 I)
    (by simp only [List.length_cons, List.length_nil]; omega)

theorem jugFileDutyX_shortarg {cA gh bl σ σ₀ A I} {g : Sat256} {sel : UInt256}
    (hsz4 : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hshort : I.calldata.size < 100)
    (hreach : ∃ k C, RD jugBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨185⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    RDrev jugBytecode g (initState cA gh bl σ σ₀ g A I) := by
  have hlt :
      UInt256.lt (UInt256.sub (UInt256.ofNat I.calldata.size) ⟨4⟩) ⟨96⟩ = ⟨1⟩ := by
    apply ult_one
    rw [usub_ofNat_word_toNat (by simpa using hsz4) hsize]
    change I.calldata.size - 4 < 96
    omega
  exact RD.solcExternalStaticArgsShortReverts
    (code := jugBytecode) (sel := sel) (entry := ⟨185⟩) (ret := ⟨226⟩)
    (decoded := ⟨207⟩) (need := ⟨96⟩) hreach
    (by decide +native) (by decide +native) (by decide +native) (by decide +native)
    (by decide +native) (by decide +native) (by decide +native) (by decide +native)
    (by decide +native) (by decide +native) (by decide +native) (by decide +native)
    (by decide +native) (by decide +native) (by decide +native) hlt

theorem jugFileDutyBodyCoreOk
    {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256} {sel : UInt256}
    (hcode : I.code = jugBytecode) (hsize : I.calldata.size < UInt256.size)
    (hperm : I.perm = true) (hwv : I.weiValue = ⟨0⟩)
    (hsz100 : 100 ≤ I.calldata.size)
    (hauth : relyAuthWord σ_evm I = ⟨1⟩)
    (htime : jugSlotWord (fileDutyRhoSlotFor I) σ_evm I = UInt256.ofNat I.header.timestamp)
    (hwhat : fileDutyWhatBytes I = fileDutyBytes)
    (hdispatch : dispatchMsg contract I.calldata = some fileDutyTransition)
    (hdecode :
      decodeCalldataWithMode config.abiDecodeMode (fileDutyTransition.params.map Param.name)
        (transitionSignature fileDutyTransition).paramTypes I.calldata = some (fileDutyLocals I))
    (hreach : ∃ k C, RD jugBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) ⟨185⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ_evm) k C)
    (hAccounts : accountMapEquiv σ_evm σ_solm) :
    runtimeEquivalenceFor config contract cA gh bl σ_evm σ_solm σ₀ g A I := by
  let data := fileDutyData I
  let dutySlot := fileDutyDutySlotFor I
  let locals := fileDutyLocals I
  let evm0 := initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I
  let evm1 := Solm.EVM.storageStore evm0 I.codeOwner dutySlot data
  have hauthSolm : relyAuthWord σ_solm I = ⟨1⟩ := by
    have hword : relyAuthWord σ_evm I = relyAuthWord σ_solm I :=
      accountMapEquiv_storage_findD hAccounts I.codeOwner (relyAuthStorageSlot I) ⟨0⟩
    rw [← hword]
    exact hauth
  have hrhoWord : jugSlotWord (fileDutyRhoSlotFor I) σ_evm I =
      jugSlotWord (fileDutyRhoSlotFor I) σ_solm I :=
    accountMapEquiv_storage_findD hAccounts I.codeOwner (fileDutyRhoSlotFor I) ⟨0⟩
  have htimeSolm : jugSlotWord (fileDutyRhoSlotFor I) σ_solm I =
      UInt256.ofNat I.header.timestamp := by
    rw [← hrhoWord]
    exact htime
  have hbody :
      ExecTransitionBody config contract evm0 locals fileDutyTransition.body
        (.returned { contract := contract, locals := locals } evm1 none) := by
    simpa [evm0, evm1, locals, dutySlot, data] using
      (jugFileDutySourceBody (cA := cA) (gh := gh) (bl := bl) (σ := σ_solm)
        (σ₀ := σ₀) (A := A) (I := I) (g := g) hwv (by omega) hauthSolm
        htimeSolm hwhat)
  obtain ⟨_, _, hdecoded⟩ := jugFileDutyX_decoded (g := Sat256.ofUInt256 g)
    hsz100 hsize hreach
  obtain ⟨_, _, hauthz⟩ := jugFileDutyX_authorized (I := I) hauth hdecoded
  obtain ⟨_, _, htimeOk⟩ := jugFileDutyX_rhoOk (I := I) (by omega) htime hauthz
  have hmatch : fileDutyWhatWord I = ABI.bytesToWord fileDutyBytes :=
    fileDutyWhatWord_eq_of_bytes_eq (by omega) hwhat
  have hret := jugFileDutyX_storeAuthorized (I := I) (by omega) hperm hmatch htimeOk
  exact hret.reEquivExecutionGenAccountMapEquiv hcode hdispatch hdecode hbody
    (by simp [evm1, evm0, initState, storageStore_createdAccounts])
    (by
      simpa [evm1, evm0, initState, storageStore_accountMap, dutySlot, data] using
        accountMapEquiv_sstoreAccountMap I.codeOwner dutySlot data hAccounts)
    (by
      simpa [fileDutyTransition] using
        (returnEquiv.fallthrough (o := ByteArray.empty) (r := none) (t := [])
          (dvs := []) rfl (by decide +native) (by decide +native)))

theorem jugFileDutyBodyCoreUnauthorized
    {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256} {sel : UInt256}
    (hcode : I.code = jugBytecode) (hsize : I.calldata.size < UInt256.size)
    (hwv : I.weiValue = ⟨0⟩)
    (hsz100 : 100 ≤ I.calldata.size)
    (hauth : relyAuthWord σ_evm I ≠ ⟨1⟩)
    (hdispatch : dispatchMsg contract I.calldata = some fileDutyTransition)
    (hdecode :
      decodeCalldataWithMode config.abiDecodeMode (fileDutyTransition.params.map Param.name)
        (transitionSignature fileDutyTransition).paramTypes I.calldata = some (fileDutyLocals I))
    (hreach : ∃ k C, RD jugBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) ⟨185⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ_evm) k C)
    (hAccounts : accountMapEquiv σ_evm σ_solm) :
    runtimeEquivalenceFor config contract cA gh bl σ_evm σ_solm σ₀ g A I := by
  let locals := fileDutyLocals I
  let evm0 := initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I
  have hauthSolm : relyAuthWord σ_solm I ≠ ⟨1⟩ := by
    have hword : relyAuthWord σ_evm I = relyAuthWord σ_solm I :=
      accountMapEquiv_storage_findD hAccounts I.codeOwner (relyAuthStorageSlot I) ⟨0⟩
    intro hbad
    exact hauth (by rw [hword, hbad])
  have hbody :
      ExecTransitionBody config contract evm0 locals fileDutyTransition.body .reverted := by
    simpa [evm0, locals] using
      (jugFileDutySourceBodyAuthReverts (cA := cA) (gh := gh) (bl := bl) (σ := σ_solm)
        (σ₀ := σ₀) (A := A) (I := I) (g := g) hwv hauthSolm)
  obtain ⟨_, _, hdecoded⟩ := jugFileDutyX_decoded (g := Sat256.ofUInt256 g)
    hsz100 hsize hreach
  exact (jugFileDutyX_unauthorized (I := I) hauth hdecoded)
    |>.reEquivExecutionRevert hcode hdispatch hdecode hbody

theorem jugFileDutyBodyCoreRhoMismatch
    {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256} {sel : UInt256}
    (hcode : I.code = jugBytecode) (hsize : I.calldata.size < UInt256.size)
    (hwv : I.weiValue = ⟨0⟩)
    (hsz100 : 100 ≤ I.calldata.size)
    (hauth : relyAuthWord σ_evm I = ⟨1⟩)
    (htime :
      UInt256.ofNat I.header.timestamp ≠ jugSlotWord (fileDutyRhoSlotFor I) σ_evm I)
    (hdispatch : dispatchMsg contract I.calldata = some fileDutyTransition)
    (hdecode :
      decodeCalldataWithMode config.abiDecodeMode (fileDutyTransition.params.map Param.name)
        (transitionSignature fileDutyTransition).paramTypes I.calldata = some (fileDutyLocals I))
    (hreach : ∃ k C, RD jugBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) ⟨185⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ_evm) k C)
    (hAccounts : accountMapEquiv σ_evm σ_solm) :
    runtimeEquivalenceFor config contract cA gh bl σ_evm σ_solm σ₀ g A I := by
  let locals := fileDutyLocals I
  let evm0 := initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I
  have hauthSolm : relyAuthWord σ_solm I = ⟨1⟩ := by
    have hword : relyAuthWord σ_evm I = relyAuthWord σ_solm I :=
      accountMapEquiv_storage_findD hAccounts I.codeOwner (relyAuthStorageSlot I) ⟨0⟩
    rw [← hword]
    exact hauth
  have hrhoWord : jugSlotWord (fileDutyRhoSlotFor I) σ_evm I =
      jugSlotWord (fileDutyRhoSlotFor I) σ_solm I :=
    accountMapEquiv_storage_findD hAccounts I.codeOwner (fileDutyRhoSlotFor I) ⟨0⟩
  have htimeSolm :
      UInt256.ofNat I.header.timestamp ≠ jugSlotWord (fileDutyRhoSlotFor I) σ_solm I := by
    intro hbad
    exact htime (by rw [hrhoWord, ← hbad])
  have hbody :
      ExecTransitionBody config contract evm0 locals fileDutyTransition.body .reverted := by
    simpa [evm0, locals] using
      (jugFileDutySourceBodyRhoReverts (cA := cA) (gh := gh) (bl := bl) (σ := σ_solm)
        (σ₀ := σ₀) (A := A) (I := I) (g := g) hwv (by omega) hauthSolm htimeSolm)
  obtain ⟨_, _, hdecoded⟩ := jugFileDutyX_decoded (g := Sat256.ofUInt256 g)
    hsz100 hsize hreach
  obtain ⟨_, _, hauthz⟩ := jugFileDutyX_authorized (I := I) hauth hdecoded
  exact (jugFileDutyX_rhoReverts (I := I) (by omega) htime hauthz)
    |>.reEquivExecutionRevert hcode hdispatch hdecode hbody

theorem jugFileDutyBodyCoreUnrecognized
    {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256} {sel : UInt256}
    (hcode : I.code = jugBytecode) (hsize : I.calldata.size < UInt256.size)
    (hwv : I.weiValue = ⟨0⟩)
    (hsz100 : 100 ≤ I.calldata.size)
    (hauth : relyAuthWord σ_evm I = ⟨1⟩)
    (htime : jugSlotWord (fileDutyRhoSlotFor I) σ_evm I = UInt256.ofNat I.header.timestamp)
    (hwhat : fileDutyWhatBytes I ≠ fileDutyBytes)
    (hdispatch : dispatchMsg contract I.calldata = some fileDutyTransition)
    (hdecode :
      decodeCalldataWithMode config.abiDecodeMode (fileDutyTransition.params.map Param.name)
        (transitionSignature fileDutyTransition).paramTypes I.calldata = some (fileDutyLocals I))
    (hreach : ∃ k C, RD jugBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) ⟨185⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ_evm) k C)
    (hAccounts : accountMapEquiv σ_evm σ_solm) :
    runtimeEquivalenceFor config contract cA gh bl σ_evm σ_solm σ₀ g A I := by
  let locals := fileDutyLocals I
  let evm0 := initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I
  have hauthSolm : relyAuthWord σ_solm I = ⟨1⟩ := by
    have hword : relyAuthWord σ_evm I = relyAuthWord σ_solm I :=
      accountMapEquiv_storage_findD hAccounts I.codeOwner (relyAuthStorageSlot I) ⟨0⟩
    rw [← hword]
    exact hauth
  have hrhoWord : jugSlotWord (fileDutyRhoSlotFor I) σ_evm I =
      jugSlotWord (fileDutyRhoSlotFor I) σ_solm I :=
    accountMapEquiv_storage_findD hAccounts I.codeOwner (fileDutyRhoSlotFor I) ⟨0⟩
  have htimeSolm : jugSlotWord (fileDutyRhoSlotFor I) σ_solm I =
      UInt256.ofNat I.header.timestamp := by
    rw [← hrhoWord]
    exact htime
  have hbody :
      ExecTransitionBody config contract evm0 locals fileDutyTransition.body .reverted := by
    simpa [evm0, locals] using
      (jugFileDutySourceBodyUnrecognized (cA := cA) (gh := gh) (bl := bl) (σ := σ_solm)
        (σ₀ := σ₀) (A := A) (I := I) (g := g) hwv (by omega) hauthSolm
        htimeSolm hwhat)
  obtain ⟨_, _, hdecoded⟩ := jugFileDutyX_decoded (g := Sat256.ofUInt256 g)
    hsz100 hsize hreach
  obtain ⟨_, _, hauthz⟩ := jugFileDutyX_authorized (I := I) hauth hdecoded
  obtain ⟨_, _, htimeOk⟩ := jugFileDutyX_rhoOk (I := I) (by omega) htime hauthz
  have hneq : fileDutyWhatWord I ≠ ABI.bytesToWord fileDutyBytes :=
    fileDutyWhatWord_ne_of_bytes_ne (by omega) hwhat (by decide +native)
  exact (jugFileDutyX_unrecognized hneq htimeOk)
    |>.reEquivExecutionRevert hcode hdispatch hdecode hbody

theorem jugFileDutyBodyCoreDecodeFailed_short
    {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256} {sel : UInt256}
    (hcode : I.code = jugBytecode) (hsize : I.calldata.size < UInt256.size)
    (hsz4 : 4 ≤ I.calldata.size) (hshort : I.calldata.size < 100)
    (hdispatch : dispatchMsg contract I.calldata = some fileDutyTransition)
    (hreach : ∃ k C, RD jugBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) ⟨185⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ_evm) k C) :
    runtimeEquivalenceFor config contract cA gh bl σ_evm σ_solm σ₀ g A I := by
  exact (jugFileDutyX_shortarg (g := Sat256.ofUInt256 g) hsz4 hsize hshort hreach)
    |>.reEquivDecodingFailed hcode hdispatch (jugDecode_fileDuty_none_short hsz4 hshort)

theorem jugFileDutyBody {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256}
    (hcode : I.code = jugBytecode)
    (hsize : I.calldata.size < UInt256.size)
    (hperm : I.perm = true)
    (hwv : I.weiValue = ⟨0⟩)
    (hsel : selIs I (jugSelBytes 4))
    (hAccounts : accountMapEquiv σ_evm σ_solm) :
    runtimeEquivalenceFor config contract cA gh bl σ_evm σ_solm σ₀ g A I := by
  have hsz4 : 4 ≤ I.calldata.size :=
    calldata_size_ge_of_selIs I (jugSelBytes 4) rfl hsel
  have hdispatch : dispatchMsg contract I.calldata = some fileDutyTransition :=
    jugDispatchFileDuty hsel
  have hreach := jugReachFileDutyBody (cA := cA) (gh := gh) (bl := bl)
    (σ := σ_evm) (σ₀ := σ₀) (A := A) (I := I) (g := Sat256.ofUInt256 g)
    hcode hwv hsz4 hsize hsel
  by_cases hsz100 : 100 ≤ I.calldata.size
  · by_cases hauth : relyAuthWord σ_evm I = ⟨1⟩
    · by_cases htime :
        jugSlotWord (fileDutyRhoSlotFor I) σ_evm I = UInt256.ofNat I.header.timestamp
      · by_cases hwhat : fileDutyWhatBytes I = fileDutyBytes
        · exact jugFileDutyBodyCoreOk hcode hsize hperm hwv hsz100 hauth htime hwhat
            hdispatch (jugDecode_fileDuty_ok hsz100) hreach hAccounts
        · exact jugFileDutyBodyCoreUnrecognized hcode hsize hwv hsz100 hauth htime hwhat
            hdispatch (jugDecode_fileDuty_ok hsz100) hreach hAccounts
      · exact jugFileDutyBodyCoreRhoMismatch hcode hsize hwv hsz100 hauth (by
          intro hbad
          exact htime hbad.symm)
          hdispatch (jugDecode_fileDuty_ok hsz100) hreach hAccounts
    · exact jugFileDutyBodyCoreUnauthorized hcode hsize hwv hsz100 hauth hdispatch
        (jugDecode_fileDuty_ok hsz100) hreach hAccounts
  · exact jugFileDutyBodyCoreDecodeFailed_short hcode hsize hsz4 (by omega)
      hdispatch hreach

end Benchmarks.Dss.Jug
