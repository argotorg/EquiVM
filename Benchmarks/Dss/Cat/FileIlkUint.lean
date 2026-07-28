import Benchmarks.Dss.Cat.Storage

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

set_option maxRecDepth 2000000
set_option maxHeartbeats 0

namespace Benchmarks.Dss.Cat

/-! ## `file(bytes32,bytes32,uint256)` — LOW-LOW dispatch arm 0, entry ⟨261⟩ -/

abbrev fileIlkUintIlk (I : ExecutionEnv) : List UInt8 :=
  (I.calldata.toList.drop 4).take 32

abbrev fileIlkUintWhat (I : ExecutionEnv) : List UInt8 :=
  (I.calldata.toList.drop 36).take 32

abbrev fileIlkUintIlkWord (I : ExecutionEnv) : UInt256 :=
  calldataWord I.calldata 4

abbrev fileIlkUintWhatWord (I : ExecutionEnv) : UInt256 :=
  calldataWord I.calldata 36

abbrev fileIlkUintData (I : ExecutionEnv) : UInt256 :=
  calldataWord I.calldata 68

abbrev fileIlkUintIlkKey (I : ExecutionEnv) : KeyValue :=
  .fixedBytes bytes32Width (fileIlkUintIlk I)

abbrev fileIlkUintChopSlotFor (I : ExecutionEnv) : UInt256 :=
  ilksBase (fileIlkUintIlkKey I) + ⟨1⟩

abbrev fileIlkUintDunkSlotFor (I : ExecutionEnv) : UInt256 :=
  ilksBase (fileIlkUintIlkKey I) + ⟨2⟩

abbrev fileIlkUintChopEvaledRef (I : ExecutionEnv) : EvaledStorageRef :=
  { base := "ilks", steps := [.mindex (fileIlkUintIlkKey I), .field "chop"] }

abbrev fileIlkUintDunkEvaledRef (I : ExecutionEnv) : EvaledStorageRef :=
  { base := "ilks", steps := [.mindex (fileIlkUintIlkKey I), .field "dunk"] }

abbrev fileIlkChopBytes : List UInt8 :=
  [99, 104, 111, 112] ++ zeroPad28

abbrev fileIlkDunkBytes : List UInt8 :=
  [100, 117, 110, 107] ++ zeroPad28

abbrev fileIlkUintLocals (I : ExecutionEnv) : Store :=
  (((∅ : Store).insert "ilk" (.fixedBytes bytes32Width (fileIlkUintIlk I))).insert
    "what" (.fixedBytes bytes32Width (fileIlkUintWhat I))).insert
    "data" (.int (Int.ofNat (fileIlkUintData I).toNat))

/-! ### key / word helpers -/

theorem fileIlkUintIlk_length {I : ExecutionEnv} (hsz36 : 36 ≤ I.calldata.size) :
    (fileIlkUintIlk I).length = 32 := by
  simp [fileIlkUintIlk, List.length_take, List.length_drop, byteArray_toList_eq]
  omega

theorem fileIlkUintWhat_length {I : ExecutionEnv} (hsz68 : 68 ≤ I.calldata.size) :
    (fileIlkUintWhat I).length = 32 := by
  simp [fileIlkUintWhat, List.length_take, List.length_drop, byteArray_toList_eq]
  omega

theorem fileIlkUintWhatWord_eq {I : ExecutionEnv} (hsz68 : 68 ≤ I.calldata.size) :
    ABI.bytesToWord (fileIlkUintWhat I) = fileIlkUintWhatWord I := by
  simpa [fileIlkUintWhat, fileIlkUintWhatWord] using
    decode_word_at_eq I.calldata 36 (by omega) (by norm_num)

theorem fileIlkUintWhatWord_eq_of_bytes_eq {I : ExecutionEnv} {bs : List UInt8}
    (hsz68 : 68 ≤ I.calldata.size) (hbs : fileIlkUintWhat I = bs) :
    fileIlkUintWhatWord I = ABI.bytesToWord bs := by
  rw [← hbs]
  exact (fileIlkUintWhatWord_eq (I := I) hsz68).symm

theorem fileIlkUintWhat_eq_of_word_eq {I : ExecutionEnv} {bs : List UInt8}
    (hsz68 : 68 ≤ I.calldata.size) (hword : fileIlkUintWhatWord I = ABI.bytesToWord bs)
    (hbsLen : bs.length = 32) :
    fileIlkUintWhat I = bs := by
  have hto := toBytesBE_bytesToWord_of_length (bs := fileIlkUintWhat I)
    (fileIlkUintWhat_length (I := I) hsz68)
  rw [fileIlkUintWhatWord_eq (I := I) hsz68, hword] at hto
  exact hto.symm.trans (toBytesBE_bytesToWord_of_length (bs := bs) hbsLen)

theorem fileIlkUintWhatWord_ne_of_bytes_ne {I : ExecutionEnv} {bs : List UInt8}
    (hsz68 : 68 ≤ I.calldata.size) (hneq : fileIlkUintWhat I ≠ bs)
    (hbsLen : bs.length = 32) :
    fileIlkUintWhatWord I ≠ ABI.bytesToWord bs := by
  intro hword
  exact hneq (fileIlkUintWhat_eq_of_word_eq hsz68 hword hbsLen)

theorem keyValueToWord_fileIlkUintIlkKey {I : ExecutionEnv} (hsz36 : 36 ≤ I.calldata.size) :
    keyValueToWord (fileIlkUintIlkKey I) = fileIlkUintIlkWord I := by
  have hlen32 : (fileIlkUintIlk I).length = 32 := fileIlkUintIlk_length hsz36
  have hword : ABI.bytesToWord (fileIlkUintIlk I) = fileIlkUintIlkWord I := by
    simpa [fileIlkUintIlk, fileIlkUintIlkWord] using
      decode_word_at_eq I.calldata 4 (by omega) (by norm_num)
  have hbytes : fileIlkUintIlk I = EVM.Word.toBytesBE (fileIlkUintIlkWord I) := by
    have hto := toBytesBE_bytesToWord_of_length (bs := fileIlkUintIlk I) hlen32
    rw [hword] at hto
    exact hto.symm
  simpa [fileIlkUintIlkKey, bytes32Width, hbytes] using
    keyValueToWord_fixedBytes32 (fileIlkUintIlkWord I)

theorem fileIlkUintChopSlotFor_eq {I : ExecutionEnv} (hsz36 : 36 ≤ I.calldata.size) :
    fileIlkUintChopSlotFor I = solcMappingSlot ⟨1⟩ (fileIlkUintIlkWord I) + ⟨1⟩ := by
  unfold fileIlkUintChopSlotFor ilksBase mapSlot solcMappingSlot
  rw [keyValueToWord_fileIlkUintIlkKey hsz36]

theorem fileIlkUintDunkSlotFor_eq {I : ExecutionEnv} (hsz36 : 36 ≤ I.calldata.size) :
    fileIlkUintDunkSlotFor I = solcMappingSlot ⟨1⟩ (fileIlkUintIlkWord I) + ⟨2⟩ := by
  unfold fileIlkUintDunkSlotFor ilksBase mapSlot solcMappingSlot
  rw [keyValueToWord_fileIlkUintIlkKey hsz36]

/-! ### ABI decode (LIBRARY CANDIDATE, ported from Jug/FileDuty) -/

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
  rw [show abiTupleHeadSize? [abiBytes32, abiBytes32, abiUInt256] = some 96 by native_decide]
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
  rw [show abiTupleHeadSize? [abiBytes32, abiBytes32, abiUInt256] = some 96 by native_decide]
  simp only [bind, Option.bind]
  by_cases hbytes : (cd.toList.drop 4).length < 96
  · rw [if_pos hbytes]
  · rw [if_neg hbytes]
    rw [decodeABIValues_bytes32_bytes32_uint256_legacy_none_short
      (bytes := cd.toList.drop 4) (by
        rw [List.length_drop, htlen]
        omega)]

theorem catDispatch_fileIlkUint {I : ExecutionEnv}
    (hsel : selIs I ⟨#[0x1a, 0x0b, 0x28, 0x7e]⟩) :
    dispatchMsg contract I.calldata = some fileIlkUintTransition := by
  apply dispatchMsg_eq_some_of_split (hfallback := by rfl)
    (pre := [biteTransition, boxTransition, cageTransition, clawTransition, denyTransition,
      fileAddressTransition, fileIlkFlipTransition])
    (post := [fileUintTransition, ilksTransition, litterTransition, liveTransition,
      relyTransition, vatTransition, vowTransition, wardsTransition])
    (ti := fileIlkUintTransition)
    (htr := by rfl)
  · intro t ht
    have hcd : I.calldata.extract 0 4 = (⟨#[0x1a, 0x0b, 0x28, 0x7e]⟩ : ByteArray) :=
      (byteArray_eq_of_beq hsel).symm
    simp at ht
    rcases ht with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals
      simp [selectorOf, biteSelectorBytes, boxSelectorBytes, cageSelectorBytes,
        clawSelectorBytes, denySelectorBytes, fileAddressSelectorBytes,
        fileIlkFlipSelectorBytes, hcd]
      native_decide
  · rw [selectorOf, fileIlkUintSelectorBytes]
    exact hsel

theorem catDecode_fileIlkUint_ok {I : ExecutionEnv} (hsz100 : 100 ≤ I.calldata.size) :
    decodeCalldataWithMode config.abiDecodeMode (fileIlkUintTransition.params.map Param.name)
      (transitionSignature fileIlkUintTransition).paramTypes I.calldata =
        some (fileIlkUintLocals I) := by
  simpa [config, fileIlkUintTransition, bytes32, bytes32Width, uint256, uint256Int,
    fileIlkUintLocals, fileIlkUintIlk, fileIlkUintWhat, fileIlkUintData, abiBytes32,
    abiBytes32Width, abiUInt256] using
    (decodeCalldata_legacyBytes32_bytes32_uint256_ok (cd := I.calldata) (x := "ilk")
      (y := "what") (z := "data") hsz100)

theorem catDecode_fileIlkUint_none_short {I : ExecutionEnv}
    (hsz4 : 4 ≤ I.calldata.size) (hshort : I.calldata.size < 100) :
    decodeCalldataWithMode config.abiDecodeMode (fileIlkUintTransition.params.map Param.name)
      (transitionSignature fileIlkUintTransition).paramTypes I.calldata = none := by
  simpa [config, fileIlkUintTransition, bytes32, bytes32Width, uint256, uint256Int,
    abiBytes32, abiBytes32Width, abiUInt256] using
    (decodeCalldata_legacyBytes32_bytes32_uint256_none_short (cd := I.calldata) (x := "ilk")
      (y := "what") (z := "data") hsz4 hshort)

/-! ### locals getters -/

theorem fileIlkUintLocals_get_ilk (I : ExecutionEnv) :
    (fileIlkUintLocals I).get? "ilk" =
      some (.fixedBytes bytes32Width (fileIlkUintIlk I)) := by
  rw [fileIlkUintLocals, store_get_ne _ _ (by decide), store_get_ne _ _ (by decide),
    store_get_self]

theorem fileIlkUintLocals_get_what (I : ExecutionEnv) :
    (fileIlkUintLocals I).get? "what" =
      some (.fixedBytes bytes32Width (fileIlkUintWhat I)) := by
  rw [fileIlkUintLocals, store_get_ne _ _ (by decide), store_get_self]

theorem fileIlkUintLocals_get_data (I : ExecutionEnv) :
    (fileIlkUintLocals I).get? "data" =
      some (.int (Int.ofNat (fileIlkUintData I).toNat)) := by
  rw [fileIlkUintLocals, store_get_self]

theorem fileIlkUintLocals_get_wards (I : ExecutionEnv) :
    (fileIlkUintLocals I).get? "wards" = none := by
  rw [fileIlkUintLocals, store_get_ne _ _ (by decide), store_get_ne _ _ (by decide),
    store_get_ne _ _ (by decide)]
  simp

theorem fileIlkUintLocals_get_ilks (I : ExecutionEnv) :
    (fileIlkUintLocals I).get? "ilks" = none := by
  rw [fileIlkUintLocals, store_get_ne _ _ (by decide), store_get_ne _ _ (by decide),
    store_get_ne _ _ (by decide)]
  simp

/-! ### Solm expression / assignment helpers -/

theorem evalExpr_fileIlkUintData {evm : EVM.State} {I : ExecutionEnv} {locals : Store}
    (h : locals.get? "data" = some (.int (Int.ofNat (fileIlkUintData I).toNat))) :
    evalExpr? config { contract := contract, locals := locals } evm (.var "data") =
      .ok (.int (Int.ofNat (fileIlkUintData I).toNat)) := by
  rw [evalExpr?]
  change EvalResult.ofOption EvalError.unboundVariable (locals.get? "data") =
    .ok (.int (Int.ofNat (fileIlkUintData I).toNat))
  rw [h]
  rfl

theorem evalExpr_fileIlkUintWhatEq_true {evm : EVM.State} {I : ExecutionEnv} {locals : Store}
    {bs : List UInt8}
    (hget : locals.get? "what" = some (.fixedBytes bytes32Width (fileIlkUintWhat I)))
    (hwhat : fileIlkUintWhat I = bs) :
    evalExpr? config { contract := contract, locals := locals } evm
      (.binary .eq (.var "what") (.fixedBytesLit bytes32Width bs)) = .ok (.bool true) := by
  have hvar :
      evalExpr? config { contract := contract, locals := locals } evm (.var "what") =
        .ok (.fixedBytes bytes32Width (fileIlkUintWhat I)) := by
    rw [evalExpr?]
    change EvalResult.ofOption EvalError.unboundVariable (locals.get? "what") =
      .ok (.fixedBytes bytes32Width (fileIlkUintWhat I))
    rw [hget]
    rfl
  rw [evalExpr?]
  simp only [hvar, EvalResult.bind, bind]
  simp [evalExpr?, evalBinaryOp?, hwhat]
  all_goals decide

theorem evalExpr_fileIlkUintWhatEq_false {evm : EVM.State} {I : ExecutionEnv} {locals : Store}
    {bs : List UInt8}
    (hget : locals.get? "what" = some (.fixedBytes bytes32Width (fileIlkUintWhat I)))
    (hwhat : fileIlkUintWhat I ≠ bs) :
    evalExpr? config { contract := contract, locals := locals } evm
      (.binary .eq (.var "what") (.fixedBytesLit bytes32Width bs)) = .ok (.bool false) := by
  have hvar :
      evalExpr? config { contract := contract, locals := locals } evm (.var "what") =
        .ok (.fixedBytes bytes32Width (fileIlkUintWhat I)) := by
    rw [evalExpr?]
    change EvalResult.ofOption EvalError.unboundVariable (locals.get? "what") =
      .ok (.fixedBytes bytes32Width (fileIlkUintWhat I))
    rw [hget]
    rfl
  rw [evalExpr?]
  simp only [hvar, EvalResult.bind, bind]
  simp [evalExpr?, evalBinaryOp?, hwhat]
  all_goals decide

theorem assign_fileIlkChopStorage (evm : EVM.State) (I : ExecutionEnv)
    (hsz36 : 36 ≤ I.calldata.size) :
    let evm' := Solm.EVM.storageStore evm evm.executionEnv.codeOwner (fileIlkUintChopSlotFor I)
      (fileIlkUintData I)
    assignStorageRef? config { contract := contract, locals := fileIlkUintLocals I } evm
      .storage (ilksF (.var "ilk") "chop") (.int (Int.ofNat (fileIlkUintData I).toNat)) =
        .ok ({ contract := contract, locals := fileIlkUintLocals I }, evm') := by
  intro evm'
  apply assignStorageRef_storage_scalar
      (ty := uint256St) (er := fileIlkUintChopEvaledRef I)
      (loc := wordLoc (fileIlkUintChopSlotFor I))
      (hbase := fileIlkUintLocals_get_ilks I)
      (her := by
        have hkeyLen : (fileIlkUintIlk I).length = ↑bytes32Width + 1 := by
          simpa [bytes32Width] using fileIlkUintIlk_length (I := I) hsz36
        simp [fileIlkUintChopEvaledRef, fileIlkUintIlkKey, evalStorageRef, evalStorageRefSteps,
          evalStorageRefStep, ilksF, evalExpr?, valueToKey?,
          ← Std.HashMap.get?_eq_getElem?, fileIlkUintLocals_get_ilk I, EvalResult.ofOption,
          EvalResult.bind, pure, bind, hkeyLen])
      (hty := by
        simp [fileIlkUintIlkKey, storageTypeAt?, storageTypeStep?, contract, storageDecls,
          IlkStructTy, addrSt, uint256St])
      (hloc := by rfl)
  simpa [evm'] using storageLocStore_uint256 evm (fileIlkUintChopSlotFor I) (fileIlkUintData I)

theorem assign_fileIlkDunkStorage (evm : EVM.State) (I : ExecutionEnv)
    (hsz36 : 36 ≤ I.calldata.size) :
    let evm' := Solm.EVM.storageStore evm evm.executionEnv.codeOwner (fileIlkUintDunkSlotFor I)
      (fileIlkUintData I)
    assignStorageRef? config { contract := contract, locals := fileIlkUintLocals I } evm
      .storage (ilksF (.var "ilk") "dunk") (.int (Int.ofNat (fileIlkUintData I).toNat)) =
        .ok ({ contract := contract, locals := fileIlkUintLocals I }, evm') := by
  intro evm'
  apply assignStorageRef_storage_scalar
      (ty := uint256St) (er := fileIlkUintDunkEvaledRef I)
      (loc := wordLoc (fileIlkUintDunkSlotFor I))
      (hbase := fileIlkUintLocals_get_ilks I)
      (her := by
        have hkeyLen : (fileIlkUintIlk I).length = ↑bytes32Width + 1 := by
          simpa [bytes32Width] using fileIlkUintIlk_length (I := I) hsz36
        simp [fileIlkUintDunkEvaledRef, fileIlkUintIlkKey, evalStorageRef, evalStorageRefSteps,
          evalStorageRefStep, ilksF, evalExpr?, valueToKey?,
          ← Std.HashMap.get?_eq_getElem?, fileIlkUintLocals_get_ilk I, EvalResult.ofOption,
          EvalResult.bind, pure, bind, hkeyLen])
      (hty := by
        simp [fileIlkUintIlkKey, storageTypeAt?, storageTypeStep?, contract, storageDecls,
          IlkStructTy, addrSt, uint256St])
      (hloc := by rfl)
  simpa [evm'] using storageLocStore_uint256 evm (fileIlkUintDunkSlotFor I) (fileIlkUintData I)

/-! ### Solm-side body execution -/

theorem fileIlkUintChopSourceBody {cA gh bl σ σ₀ A I} {g : UInt256}
    (hwv : I.weiValue = ⟨0⟩)
    (hsz36 : 36 ≤ I.calldata.size)
    (hauth : catSlotWord (catCallerWardsSlot I) σ I = ⟨1⟩)
    (hwhat : fileIlkUintWhat I = fileIlkChopBytes) :
    let locals := fileIlkUintLocals I
    let evm0 := initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I
    let evm1 := Solm.EVM.storageStore evm0 I.codeOwner (fileIlkUintChopSlotFor I) (fileIlkUintData I)
    ExecTransitionBody config contract evm0 locals fileIlkUintTransition.body
      (.returned { contract := contract, locals := locals } evm1 none) := by
  intro locals evm0 evm1
  have hguard := catAuthGuardEval_true (cA := cA) (gh := gh) (bl := bl)
    (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := Sat256.ofUInt256 g)
    (locals := locals) (by simp [locals, fileIlkUintLocals]) hauth
  have hcond :
      evalExpr? config { contract := contract, locals := locals } evm0
        (.binary .eq (.var "what") chopParamLit) = .ok (.bool true) := by
    simpa [chopParamLit, fileIlkChopBytes] using
      (evalExpr_fileIlkUintWhatEq_true (evm := evm0) (I := I) (locals := locals)
        (bs := fileIlkChopBytes) (by simpa [locals] using fileIlkUintLocals_get_what I) hwhat)
  have hdata :
      evalExpr? config { contract := contract, locals := locals } evm0 (.var "data") =
        .ok (.int (Int.ofNat (fileIlkUintData I).toNat)) := by
    exact evalExpr_fileIlkUintData (evm := evm0) (I := I) (locals := locals)
      (by simpa [locals] using fileIlkUintLocals_get_data I)
  have hassign :
      assignStorageRef? config { contract := contract, locals := locals } evm0
        .storage (ilksF (.var "ilk") "chop") (.int (Int.ofNat (fileIlkUintData I).toNat)) =
          .ok ({ contract := contract, locals := locals }, evm1) := by
    simpa [locals, evm1] using assign_fileIlkChopStorage evm0 I hsz36
  have hthen :
      ExecBlock config { contract := contract, locals := locals } evm0
        [.assign .storage (ilksF (.var "ilk") "chop") (.var "data")]
        (.ok { contract := contract, locals := locals } evm1) :=
    ExecBlock.consNormal (ExecStmt.assign hdata hassign) ExecBlock.nil
  have hblock :
      ExecBlock config { contract := contract, locals := locals } evm0 fileIlkUintTransition.body
        (.ok { contract := contract, locals := locals } evm1) := by
    refine ExecBlock.consNormal (ExecStmt.requireTrue ?_) ?_
    · exact evalCallvalueEq_true (by simp [evm0, initState]; exact hwv)
    refine ExecBlock.consNormal (ExecStmt.requireTrue hguard) ?_
    exact ExecBlock.consNormal (ExecStmt.iteTrue hcond hthen) ExecBlock.nil
  simpa [ExecTransitionBody, evm0, evm1, locals] using ExecFuncBody.execBlockOK hblock

theorem fileIlkUintDunkSourceBody {cA gh bl σ σ₀ A I} {g : UInt256}
    (hwv : I.weiValue = ⟨0⟩)
    (hsz36 : 36 ≤ I.calldata.size)
    (hauth : catSlotWord (catCallerWardsSlot I) σ I = ⟨1⟩)
    (hnotChop : fileIlkUintWhat I ≠ fileIlkChopBytes)
    (hwhat : fileIlkUintWhat I = fileIlkDunkBytes) :
    let locals := fileIlkUintLocals I
    let evm0 := initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I
    let evm1 := Solm.EVM.storageStore evm0 I.codeOwner (fileIlkUintDunkSlotFor I) (fileIlkUintData I)
    ExecTransitionBody config contract evm0 locals fileIlkUintTransition.body
      (.returned { contract := contract, locals := locals } evm1 none) := by
  intro locals evm0 evm1
  have hguard := catAuthGuardEval_true (cA := cA) (gh := gh) (bl := bl)
    (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := Sat256.ofUInt256 g)
    (locals := locals) (by simp [locals, fileIlkUintLocals]) hauth
  have hchop :
      evalExpr? config { contract := contract, locals := locals } evm0
        (.binary .eq (.var "what") chopParamLit) = .ok (.bool false) := by
    simpa [chopParamLit, fileIlkChopBytes] using
      (evalExpr_fileIlkUintWhatEq_false (evm := evm0) (I := I) (locals := locals)
        (bs := fileIlkChopBytes) (by simpa [locals] using fileIlkUintLocals_get_what I) hnotChop)
  have hcond :
      evalExpr? config { contract := contract, locals := locals } evm0
        (.binary .eq (.var "what") dunkParamLit) = .ok (.bool true) := by
    simpa [dunkParamLit, fileIlkDunkBytes] using
      (evalExpr_fileIlkUintWhatEq_true (evm := evm0) (I := I) (locals := locals)
        (bs := fileIlkDunkBytes) (by simpa [locals] using fileIlkUintLocals_get_what I) hwhat)
  have hdata :
      evalExpr? config { contract := contract, locals := locals } evm0 (.var "data") =
        .ok (.int (Int.ofNat (fileIlkUintData I).toNat)) := by
    exact evalExpr_fileIlkUintData (evm := evm0) (I := I) (locals := locals)
      (by simpa [locals] using fileIlkUintLocals_get_data I)
  have hassign :
      assignStorageRef? config { contract := contract, locals := locals } evm0
        .storage (ilksF (.var "ilk") "dunk") (.int (Int.ofNat (fileIlkUintData I).toNat)) =
          .ok ({ contract := contract, locals := locals }, evm1) := by
    simpa [locals, evm1] using assign_fileIlkDunkStorage evm0 I hsz36
  have hthen :
      ExecBlock config { contract := contract, locals := locals } evm0
        [.assign .storage (ilksF (.var "ilk") "dunk") (.var "data")]
        (.ok { contract := contract, locals := locals } evm1) :=
    ExecBlock.consNormal (ExecStmt.assign hdata hassign) ExecBlock.nil
  have helse :
      ExecBlock config { contract := contract, locals := locals } evm0
        [.ite (.binary .eq (.var "what") dunkParamLit)
          [.assign .storage (ilksF (.var "ilk") "dunk") (.var "data")]
          [.require (.boolLit false)]]
        (.ok { contract := contract, locals := locals } evm1) :=
    ExecBlock.consNormal (ExecStmt.iteTrue hcond hthen) ExecBlock.nil
  have hblock :
      ExecBlock config { contract := contract, locals := locals } evm0 fileIlkUintTransition.body
        (.ok { contract := contract, locals := locals } evm1) := by
    refine ExecBlock.consNormal (ExecStmt.requireTrue ?_) ?_
    · exact evalCallvalueEq_true (by simp [evm0, initState]; exact hwv)
    refine ExecBlock.consNormal (ExecStmt.requireTrue hguard) ?_
    exact ExecBlock.consNormal (ExecStmt.iteFalse hchop helse) ExecBlock.nil
  simpa [ExecTransitionBody, evm0, evm1, locals] using ExecFuncBody.execBlockOK hblock

theorem fileIlkUintUnrecognizedSourceBody {cA gh bl σ σ₀ A I} {g : UInt256}
    (hwv : I.weiValue = ⟨0⟩)
    (hauth : catSlotWord (catCallerWardsSlot I) σ I = ⟨1⟩)
    (hnotChop : fileIlkUintWhat I ≠ fileIlkChopBytes)
    (hnotDunk : fileIlkUintWhat I ≠ fileIlkDunkBytes) :
    let locals := fileIlkUintLocals I
    let evm0 := initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I
    ExecTransitionBody config contract evm0 locals fileIlkUintTransition.body .reverted := by
  intro locals evm0
  have hguard := catAuthGuardEval_true (cA := cA) (gh := gh) (bl := bl)
    (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := Sat256.ofUInt256 g)
    (locals := locals) (by simp [locals, fileIlkUintLocals]) hauth
  have hchop :
      evalExpr? config { contract := contract, locals := locals } evm0
        (.binary .eq (.var "what") chopParamLit) = .ok (.bool false) := by
    simpa [chopParamLit, fileIlkChopBytes] using
      (evalExpr_fileIlkUintWhatEq_false (evm := evm0) (I := I) (locals := locals)
        (bs := fileIlkChopBytes) (by simpa [locals] using fileIlkUintLocals_get_what I) hnotChop)
  have hdunk :
      evalExpr? config { contract := contract, locals := locals } evm0
        (.binary .eq (.var "what") dunkParamLit) = .ok (.bool false) := by
    simpa [dunkParamLit, fileIlkDunkBytes] using
      (evalExpr_fileIlkUintWhatEq_false (evm := evm0) (I := I) (locals := locals)
        (bs := fileIlkDunkBytes) (by simpa [locals] using fileIlkUintLocals_get_what I) hnotDunk)
  have hreqFalse :
      evalExpr? config { contract := contract, locals := locals } evm0 (.boolLit false) =
        .ok (.bool false) := by
    simp [evalExpr?, pure]
  have hinner :
      ExecBlock config { contract := contract, locals := locals } evm0
        [.ite (.binary .eq (.var "what") dunkParamLit)
          [.assign .storage (ilksF (.var "ilk") "dunk") (.var "data")]
          [.require (.boolLit false)]]
        .reverted :=
    ExecBlock.consRevert (ExecStmt.iteFalse hdunk
      (ExecBlock.consRevert (ExecStmt.requireFalse hreqFalse)))
  have hblock :
      ExecBlock config { contract := contract, locals := locals } evm0 fileIlkUintTransition.body
        .reverted := by
    refine ExecBlock.consNormal (ExecStmt.requireTrue ?_) ?_
    · exact evalCallvalueEq_true (by simp [evm0, initState]; exact hwv)
    refine ExecBlock.consNormal (ExecStmt.requireTrue hguard) ?_
    exact ExecBlock.consRevert (ExecStmt.iteFalse hchop hinner)
  simpa [ExecTransitionBody, evm0, locals] using ExecFuncBody.execBlockRevert hblock

theorem fileIlkUintAuthRevertSourceBody {cA gh bl σ σ₀ A I} {g : UInt256}
    (hwv : I.weiValue = ⟨0⟩)
    (hauth : catSlotWord (catCallerWardsSlot I) σ I ≠ ⟨1⟩) :
    let locals := fileIlkUintLocals I
    let evm0 := initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I
    ExecTransitionBody config contract evm0 locals fileIlkUintTransition.body .reverted := by
  intro locals evm0
  have hguard := catAuthGuardEval_false (cA := cA) (gh := gh) (bl := bl)
    (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := Sat256.ofUInt256 g)
    (locals := locals) (by simp [locals, fileIlkUintLocals]) hauth
  have hblock := nonpayableSecondRequireReverts
    (cfg := config) (solm := { contract := contract, locals := locals })
    (evm := evm0)
    (guard := .binary .eq (.storage (wardsRef sender)) (.intLit 1))
    (rest := [
      .ite (.binary .eq (.var "what") chopParamLit)
        [.assign .storage (ilksF (.var "ilk") "chop") (.var "data")]
        [.ite (.binary .eq (.var "what") dunkParamLit)
          [.assign .storage (ilksF (.var "ilk") "dunk") (.var "data")]
          [.require (.boolLit false)]]])
    (by simp [evm0, initState]; exact hwv)
    hguard
  simpa [ExecTransitionBody, fileIlkUintTransition, nonpayable, auth, evm0, locals] using
    ExecFuncBody.execBlockRevert hblock

/-! ### EVM reachability + entry bridge -/

theorem catReachFileIlkUintBody {cA gh bl σ σ₀ A I} {g : Sat256}
    (hcode : I.code = catBytecode) (hwv : I.weiValue = ⟨0⟩)
    (hsz : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hsel : selIs I ⟨#[0x1a, 0x0b, 0x28, 0x7e]⟩) :
    ∃ k C, RD catBytecode I g (initState cA gh bl σ σ₀ g A I)
        ⟨261⟩ [catSelWord I] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty
        (cA, σ) k C := by
  have hword : catSelWord I = ⟨436938878⟩ :=
    catSelWord_eq_of_beq I hsz 0x1a 0x0b 0x28 0x7e ⟨436938878⟩ (by native_decide) hsel
  have hroot : UInt256.gt (armSelNat catBytecode catRootSplitPc) (catSelWord I) ≠ ⟨0⟩ := by
    rw [hword]
    native_decide
  have hlow : UInt256.gt (armSelNat catBytecode catLowSplitPc) (catSelWord I) ≠ ⟨0⟩ := by
    rw [hword]
    native_decide
  have heq0 : ∀ j, j < 0 →
      UInt256.eq (armSelNat catBytecode (nthArmPc catBytecode catLowLowFirstArmPc j))
        (catSelWord I) = ⟨0⟩ := by
    intro j hj
    omega
  have htake :
      UInt256.eq (armSelNat catBytecode (nthArmPc catBytecode catLowLowFirstArmPc 0))
        (catSelWord I) ≠ ⟨0⟩ := by
    rw [hword]
    native_decide
  exact catReachLowLowBody 0 (by omega) ⟨261⟩ hcode hwv hsz hsize hroot hlow heq0 htake
    (by jump_dest) (by native_decide)

theorem RD.catFileIlkUintDecodeToRoutine {code : ByteArray} {g : Sat256} {s0 : State}
    {ee : ExecutionEnv} {k C : ℕ} {ret de sel : UInt256} {R : List UInt256}
    {mem rdata : ByteArray} {aw : UInt256}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    (h : RD code ee g s0 ⟨283⟩ (de :: ⟨4⟩ :: ret :: sel :: R) mem aw rdata acc k C)
    (hwf : code = catBytecode)
    (hroutine : (D_J code 0).contains ⟨783⟩ = true)
    (hov : R.length + 10 ≤ 1024) :
    ∃ k' C', RD code ee g s0 ⟨783⟩
      (calldataWord ee.calldata 68 :: calldataWord ee.calldata 36 ::
        calldataWord ee.calldata 4 :: ret :: sel :: R)
      mem aw rdata acc k' C' := by
  subst hwf
  have rd284 := h.jumpdest (by native_decide) (by evm_ov)
  have rd285 := rd284.pop (by native_decide) (by evm_ov)
  have rd286 := rd285.dup1 (by native_decide) (by evm_ov)
  have rd287 := rd286.calldataload (by native_decide) (by evm_ov)
  have rd288 := rd287.swap1 (by native_decide) (by evm_ov)
  have rd290 := rd288.push1 ⟨32⟩ (by native_decide) (by evm_ov)
  have rd291 := rd290.dup2 (by native_decide) (by evm_ov)
  have rd292 := rd291.add (by native_decide) (by evm_ov)
  have rd293 := rd292.calldataload (by native_decide) (by evm_ov)
  have rd294 := rd293.swap1 (by native_decide) (by evm_ov)
  have rd296 := rd294.push1 ⟨64⟩ (by native_decide) (by evm_ov)
  have rd297 := rd296.add (by native_decide) (by evm_ov)
  have rd298 := rd297.calldataload (by native_decide) (by evm_ov)
  have rd301 := rd298.push2 ⟨783⟩ (by native_decide) (by evm_ov)
  exact ⟨_, _, by
    simpa [calldataWord, show (⟨4⟩ : UInt256).toNat = 4 from by decide,
      show (⟨36⟩ : UInt256).toNat = 36 from by decide,
      show (⟨68⟩ : UInt256).toNat = 68 from by decide]
      using rd301.jump (by native_decide) hroutine (by evm_ov)⟩

theorem RD.catFileIlkUintToSwitch {cA gh bl σ σ₀ A I} {g : Sat256} {sel : UInt256}
    (hreach : ∃ k C, RD catBytecode I g (initState cA gh bl σ σ₀ g A I)
      ⟨261⟩ [sel] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C)
    (hsz100 : 100 ≤ I.calldata.size)
    (hsize : I.calldata.size < UInt256.size)
    (hauth : solcSlotWord σ I (solcMappingSlot ⟨0⟩ (solcSourceWord I)) = ⟨1⟩) :
    ∃ k C, RD catBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨872⟩
      (fileIlkUintData I :: fileIlkUintWhatWord I :: fileIlkUintIlkWord I :: ⟨302⟩ :: sel :: [])
      (twoWordHashMem (solcSourceWord I) ⟨0⟩ solcFreePtrMem)
      (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
  have hlt :
      UInt256.lt (UInt256.sub (UInt256.ofNat I.calldata.size) ⟨4⟩) ⟨96⟩ = ⟨0⟩ :=
    solcDecodeLenCheckOkUnsigned (by simpa using hsz100) hsize
  obtain ⟨_, _, hdecoded⟩ := RD.solcExternalStaticArgsLenOk
    (code := catBytecode) (sel := sel) (entry := ⟨261⟩) (ret := ⟨302⟩)
    (decoded := ⟨283⟩) (need := ⟨96⟩) hreach
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by jump_dest) hlt
  obtain ⟨_, _, hroutine⟩ := RD.catFileIlkUintDecodeToRoutine
    (code := catBytecode) (ret := ⟨302⟩) (sel := sel) (R := [])
    hdecoded rfl (by jump_dest) (by simp)
  obtain ⟨_, _, hafterAuth⟩ := RD.catAuthCheckOk
    (code := catBytecode) (pc := ⟨783⟩) (okPc := ⟨872⟩)
    (key := fileIlkUintData I) (ret := fileIlkUintWhatWord I)
    (R := [fileIlkUintIlkWord I, ⟨302⟩, sel])
    (by simpa [fileIlkUintData, fileIlkUintWhatWord, fileIlkUintIlkWord] using hroutine)
    (by
      unfold catAuthCheckWf
      repeat' first | apply And.intro | native_decide)
    hauth (by jump_dest) (by simp)
  exact ⟨_, _, hafterAuth⟩

theorem RD.catFileIlkUintAuthRevert {cA gh bl σ σ₀ A I} {g : Sat256} {sel : UInt256}
    (hreach : ∃ k C, RD catBytecode I g (initState cA gh bl σ σ₀ g A I)
      ⟨261⟩ [sel] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C)
    (hsz100 : 100 ≤ I.calldata.size)
    (hsize : I.calldata.size < UInt256.size)
    (hauth : solcSlotWord σ I (solcMappingSlot ⟨0⟩ (solcSourceWord I)) ≠ ⟨1⟩) :
    RDrev catBytecode g (initState cA gh bl σ σ₀ g A I) := by
  have hlt :
      UInt256.lt (UInt256.sub (UInt256.ofNat I.calldata.size) ⟨4⟩) ⟨96⟩ = ⟨0⟩ :=
    solcDecodeLenCheckOkUnsigned (by simpa using hsz100) hsize
  obtain ⟨_, _, hdecoded⟩ := RD.solcExternalStaticArgsLenOk
    (code := catBytecode) (sel := sel) (entry := ⟨261⟩) (ret := ⟨302⟩)
    (decoded := ⟨283⟩) (need := ⟨96⟩) hreach
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by jump_dest) hlt
  obtain ⟨_, _, hroutine⟩ := RD.catFileIlkUintDecodeToRoutine
    (code := catBytecode) (ret := ⟨302⟩) (sel := sel) (R := [])
    hdecoded rfl (by jump_dest) (by simp)
  exact RD.catAuthCheckRevert
    (code := catBytecode) (pc := ⟨783⟩) (okPc := ⟨872⟩)
    (key := fileIlkUintData I) (ret := fileIlkUintWhatWord I)
    (R := [fileIlkUintIlkWord I, ⟨302⟩, sel])
    (by simpa [fileIlkUintData, fileIlkUintWhatWord, fileIlkUintIlkWord] using hroutine)
    (by
      unfold catAuthCheckWf
      repeat' first | apply And.intro | native_decide)
    (by
      unfold solcErrorStringRevertTailWf catAuthTailPc catNotAuthorizedRawWord
      repeat' first | apply And.intro | native_decide)
    hauth (by simp)

/-! ### chop / dunk store + skip routines -/

theorem RD.catFileIlkStoreChop {g : Sat256} {s0 : State} {ee : ExecutionEnv}
    {k C : ℕ} {data what ilk ret sel : UInt256} {R : List UInt256} {mem rdata : ByteArray}
    {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap}
    (h : RD catBytecode ee g s0 ⟨872⟩ (data :: what :: ilk :: ret :: sel :: R) mem
      (UInt256.ofNat 3) rdata (cA, σ) k C)
    (hmatch : what = ABI.bytesToWord fileIlkChopBytes)
    (hmem : mem.size = 96)
    (hret : (D_J catBytecode 0).contains ret = true)
    (hperm : ee.perm = true)
    (hov : R.length + 16 ≤ 1024) :
    ∃ k' C', RD catBytecode ee g s0 ret (sel :: R) (twoWordHashMem ilk ⟨1⟩ mem)
      (UInt256.ofNat 3) rdata
      (cA, sstoreAccountMap ee.codeOwner σ (solcMappingSlot ⟨1⟩ ilk + ⟨1⟩) data) k' C' := by
  have hslot :
      UInt256.ofNat (fromByteArrayBigEndian
          (ffi.KEC ((twoWordHashMem ilk ⟨1⟩ mem).readWithPadding 0 64))) =
        solcMappingSlot ⟨1⟩ ilk :=
    twoWordHashMem_solcMappingSlot ⟨1⟩ ilk hmem
  have rd873 := h.jumpdest (by native_decide) (by evm_ov)
  have rd874 := rd873.dup2 (by native_decide) (by evm_ov)
  have rd879 := rd874.push4 ⟨104236791⟩ (by native_decide) (by evm_ov)
  have rd881 := rd879.push1 ⟨228⟩ (by native_decide) (by evm_ov)
  have rd882 := rd881.shl (by native_decide) (by evm_ov)
  have hconst : UInt256.shiftLeft ⟨104236791⟩ ⟨228⟩ = ABI.bytesToWord fileIlkChopBytes := by
    native_decide
  rw [hmatch, ← hconst] at rd882
  have rd883 := rd882.eq (by native_decide) (by evm_ov)
  rw [uInt256_eq_self] at rd883
  have rd884 := rd883.iszero (by native_decide) (by evm_ov)
  rw [show UInt256.isZero (⟨1⟩ : UInt256) = ⟨0⟩ from by decide] at rd884
  have rd887 := rd884.push2 ⟨913⟩ (by native_decide) (by evm_ov)
  have rd888 := rd887.jumpiNT (by native_decide) (by decide : (⟨0⟩ : UInt256) = ⟨0⟩) (by evm_ov)
  have rd890 := rd888.push1 ⟨0⟩ (by native_decide) (by evm_ov)
  have rd891 := rd890.dup4 (by native_decide) (by evm_ov)
  have rd892 := rd891.dup2 (by native_decide) (by evm_ov)
  have rd893 := rd892.mstore 0 (wordAt0Mem ilk mem) (UInt256.ofNat 3)
    (by native_decide) mem_cost (by rfl) (by native_decide) (by evm_ov)
  have rd895 := rd893.push1 ⟨1⟩ (by native_decide) (by evm_ov)
  have rd897 := rd895.push1 ⟨32⟩ (by native_decide) (by evm_ov)
  have rd898 := rd897.dup2 (by native_decide) (by evm_ov)
  have rd899 := rd898.swap1 (by native_decide) (by evm_ov)
  have rd900 := rd899.mstore 0 (twoWordHashMem ilk ⟨1⟩ mem) (UInt256.ofNat 3)
    (by native_decide) mem_cost (by rfl) (by native_decide) (by evm_ov)
  have rd902 := rd900.push1 ⟨64⟩ (by native_decide) (by evm_ov)
  have rd903 := rd902.swap1 (by native_decide) (by evm_ov)
  have rd904 := rd903.swap2 (by native_decide) (by evm_ov)
  have rd905 := rd904.keccak256 0 (solcMappingSlot ⟨1⟩ ilk) (UInt256.ofNat 3)
    (by native_decide) mem_cost hslot (by native_decide) (by evm_ov)
  have rd906 := rd905.add (by native_decide) (by evm_ov)
  have rd907 := rd906.dup2 (by native_decide) (by evm_ov)
  have rd908 := rd907.swap1 (by native_decide) (by evm_ov)
  obtain ⟨_, _, rd909⟩ := rd908.sstore hperm (by native_decide) (by evm_ov)
  have rd912 := rd909.push2 ⟨1030⟩ (by native_decide) (by evm_ov)
  have rd1030 := rd912.jump (by native_decide) (by jump_dest) (by evm_ov)
  have rd1031 := rd1030.jumpdest (by native_decide) (by evm_ov)
  have rd1032 := rd1031.pop (by native_decide) (by evm_ov)
  have rd1033 := rd1032.pop (by native_decide) (by evm_ov)
  have rd1034 := rd1033.pop (by native_decide) (by evm_ov)
  exact ⟨_, _, rd1034.jump (by native_decide) hret (by evm_ov)⟩

theorem RD.catFileIlkSkipChop {g : Sat256} {s0 : State} {ee : ExecutionEnv}
    {k C : ℕ} {data what ilk ret sel : UInt256} {R : List UInt256} {mem rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    (h : RD catBytecode ee g s0 ⟨872⟩ (data :: what :: ilk :: ret :: sel :: R) mem
      (UInt256.ofNat 3) rdata acc k C)
    (hneq : what ≠ ABI.bytesToWord fileIlkChopBytes)
    (hov : R.length + 16 ≤ 1024) :
    ∃ k' C', RD catBytecode ee g s0 ⟨913⟩ (data :: what :: ilk :: ret :: sel :: R) mem
      (UInt256.ofNat 3) rdata acc k' C' := by
  have rd873 := h.jumpdest (by native_decide) (by evm_ov)
  have rd874 := rd873.dup2 (by native_decide) (by evm_ov)
  have rd879 := rd874.push4 ⟨104236791⟩ (by native_decide) (by evm_ov)
  have rd881 := rd879.push1 ⟨228⟩ (by native_decide) (by evm_ov)
  have rd882 := rd881.shl (by native_decide) (by evm_ov)
  have hconst : UInt256.shiftLeft ⟨104236791⟩ ⟨228⟩ = ABI.bytesToWord fileIlkChopBytes := by
    native_decide
  rw [hconst] at rd882
  have rd883 := rd882.eq (by native_decide) (by evm_ov)
  have heq0 : UInt256.eq (ABI.bytesToWord fileIlkChopBytes) what = ⟨0⟩ := by
    exact u256_eq_of_ne (fun h => hneq h.symm)
  rw [heq0] at rd883
  have rd884 := rd883.iszero (by native_decide) (by evm_ov)
  rw [show UInt256.isZero (⟨0⟩ : UInt256) = ⟨1⟩ from by decide] at rd884
  have rd887 := rd884.push2 ⟨913⟩ (by native_decide) (by evm_ov)
  exact ⟨_, _, rd887.jumpiT (by native_decide) one_ne_zero_uint (by jump_dest) (by evm_ov)⟩

theorem RD.catFileIlkStoreDunk {g : Sat256} {s0 : State} {ee : ExecutionEnv}
    {k C : ℕ} {data what ilk ret sel : UInt256} {R : List UInt256} {mem rdata : ByteArray}
    {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap}
    (h : RD catBytecode ee g s0 ⟨913⟩ (data :: what :: ilk :: ret :: sel :: R) mem
      (UInt256.ofNat 3) rdata (cA, σ) k C)
    (hmatch : what = ABI.bytesToWord fileIlkDunkBytes)
    (hmem : mem.size = 96)
    (hret : (D_J catBytecode 0).contains ret = true)
    (hperm : ee.perm = true)
    (hov : R.length + 16 ≤ 1024) :
    ∃ k' C', RD catBytecode ee g s0 ret (sel :: R) (twoWordHashMem ilk ⟨1⟩ mem)
      (UInt256.ofNat 3) rdata
      (cA, sstoreAccountMap ee.codeOwner σ (solcMappingSlot ⟨1⟩ ilk + ⟨2⟩) data) k' C' := by
  have hslot :
      UInt256.ofNat (fromByteArrayBigEndian
          (ffi.KEC ((twoWordHashMem ilk ⟨1⟩ mem).readWithPadding 0 64))) =
        solcMappingSlot ⟨1⟩ ilk :=
    twoWordHashMem_solcMappingSlot ⟨1⟩ ilk hmem
  have rd914 := h.jumpdest (by native_decide) (by evm_ov)
  have rd915 := rd914.dup2 (by native_decide) (by evm_ov)
  have rd920 := rd915.push4 ⟨1685417579⟩ (by native_decide) (by evm_ov)
  have rd922 := rd920.push1 ⟨224⟩ (by native_decide) (by evm_ov)
  have rd923 := rd922.shl (by native_decide) (by evm_ov)
  have hconst : UInt256.shiftLeft ⟨1685417579⟩ ⟨224⟩ = ABI.bytesToWord fileIlkDunkBytes := by
    native_decide
  rw [hmatch, ← hconst] at rd923
  have rd924 := rd923.eq (by native_decide) (by evm_ov)
  rw [uInt256_eq_self] at rd924
  have rd925 := rd924.iszero (by native_decide) (by evm_ov)
  rw [show UInt256.isZero (⟨1⟩ : UInt256) = ⟨0⟩ from by decide] at rd925
  have rd928 := rd925.push2 ⟨953⟩ (by native_decide) (by evm_ov)
  have rd929 := rd928.jumpiNT (by native_decide) (by decide : (⟨0⟩ : UInt256) = ⟨0⟩) (by evm_ov)
  have rd931 := rd929.push1 ⟨0⟩ (by native_decide) (by evm_ov)
  have rd932 := rd931.dup4 (by native_decide) (by evm_ov)
  have rd933 := rd932.dup2 (by native_decide) (by evm_ov)
  have rd934 := rd933.mstore 0 (wordAt0Mem ilk mem) (UInt256.ofNat 3)
    (by native_decide) mem_cost (by rfl) (by native_decide) (by evm_ov)
  have rd936 := rd934.push1 ⟨1⟩ (by native_decide) (by evm_ov)
  have rd938 := rd936.push1 ⟨32⟩ (by native_decide) (by evm_ov)
  have rd939 := rd938.mstore 0 (twoWordHashMem ilk ⟨1⟩ mem) (UInt256.ofNat 3)
    (by native_decide) mem_cost (by rfl) (by native_decide) (by evm_ov)
  have rd941 := rd939.push1 ⟨64⟩ (by native_decide) (by evm_ov)
  have rd942 := rd941.swap1 (by native_decide) (by evm_ov)
  have rd943 := rd942.keccak256 0 (solcMappingSlot ⟨1⟩ ilk) (UInt256.ofNat 3)
    (by native_decide) mem_cost hslot (by native_decide) (by evm_ov)
  have rd945 := rd943.push1 ⟨2⟩ (by native_decide) (by evm_ov)
  have rd946 := rd945.add (by native_decide) (by evm_ov)
  rw [u256_add_comm ⟨2⟩ (solcMappingSlot ⟨1⟩ ilk)] at rd946
  have rd947 := rd946.dup2 (by native_decide) (by evm_ov)
  have rd948 := rd947.swap1 (by native_decide) (by evm_ov)
  obtain ⟨_, _, rd949⟩ := rd948.sstore hperm (by native_decide) (by evm_ov)
  have rd952 := rd949.push2 ⟨1030⟩ (by native_decide) (by evm_ov)
  have rd1030 := rd952.jump (by native_decide) (by jump_dest) (by evm_ov)
  have rd1031 := rd1030.jumpdest (by native_decide) (by evm_ov)
  have rd1032 := rd1031.pop (by native_decide) (by evm_ov)
  have rd1033 := rd1032.pop (by native_decide) (by evm_ov)
  have rd1034 := rd1033.pop (by native_decide) (by evm_ov)
  exact ⟨_, _, rd1034.jump (by native_decide) hret (by evm_ov)⟩

theorem RD.catFileIlkSkipDunk {g : Sat256} {s0 : State} {ee : ExecutionEnv}
    {k C : ℕ} {data what ilk ret sel : UInt256} {R : List UInt256} {mem rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    (h : RD catBytecode ee g s0 ⟨913⟩ (data :: what :: ilk :: ret :: sel :: R) mem
      (UInt256.ofNat 3) rdata acc k C)
    (hneq : what ≠ ABI.bytesToWord fileIlkDunkBytes)
    (hov : R.length + 16 ≤ 1024) :
    ∃ k' C', RD catBytecode ee g s0 ⟨953⟩ (data :: what :: ilk :: ret :: sel :: R) mem
      (UInt256.ofNat 3) rdata acc k' C' := by
  have rd914 := h.jumpdest (by native_decide) (by evm_ov)
  have rd915 := rd914.dup2 (by native_decide) (by evm_ov)
  have rd920 := rd915.push4 ⟨1685417579⟩ (by native_decide) (by evm_ov)
  have rd922 := rd920.push1 ⟨224⟩ (by native_decide) (by evm_ov)
  have rd923 := rd922.shl (by native_decide) (by evm_ov)
  have hconst : UInt256.shiftLeft ⟨1685417579⟩ ⟨224⟩ = ABI.bytesToWord fileIlkDunkBytes := by
    native_decide
  rw [hconst] at rd923
  have rd924 := rd923.eq (by native_decide) (by evm_ov)
  have heq0 : UInt256.eq (ABI.bytesToWord fileIlkDunkBytes) what = ⟨0⟩ := by
    exact u256_eq_of_ne (fun h => hneq h.symm)
  rw [heq0] at rd924
  have rd925 := rd924.iszero (by native_decide) (by evm_ov)
  rw [show UInt256.isZero (⟨0⟩ : UInt256) = ⟨1⟩ from by decide] at rd925
  have rd928 := rd925.push2 ⟨953⟩ (by native_decide) (by evm_ov)
  exact ⟨_, _, rd928.jumpiT (by native_decide) one_ne_zero_uint (by jump_dest) (by evm_ov)⟩

/-! ### unrecognized-param revert (byte-identical to Vow FileUint @2156) -/

abbrev catFileIlkUintUnrecognizedRawWord : UInt256 :=
  ⟨30477146900841294791694925804285198379011926721857912948232373309380849827840⟩

theorem RD.catFileIlkUintUnrecognizedRevert {g : Sat256} {s0 : State} {ee : ExecutionEnv}
    {k C : ℕ} {stk : List UInt256} {mem rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    (h : RD catBytecode ee g s0 ⟨953⟩ stk mem (UInt256.ofNat 3) rdata acc k C)
    (hmem : mem.size = 96)
    (hread64 : mem.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩)
    (hov : stk.length + 5 ≤ 1024) :
    RDrev catBytecode g s0 := by
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
  have rdRaw := rdPrefix.pushConst catFileIlkUintUnrecognizedRawWord
    (width := 32) (op := .PUSH32) (by decide) (by native_decide)
    (by simp only [List.length_cons]; omega)
  exact evm_run rdRaw with [
    raw push1 ⟨68⟩ (by native_decide) (by evm_ov),
    raw dup3 (by native_decide) (by evm_ov),
    raw add (by native_decide) (by evm_ov),
    raw mstore 3 (solcErrorStringMem3 ⟨27⟩ catFileIlkUintUnrecognizedRawWord mem)
      (UInt256.ofNat 8) (by native_decide) mem_cost (by rfl) (by decide) (by evm_ov),
    raw swap1 (by native_decide) (by evm_ov),
    raw mload 0 ⟨128⟩ (UInt256.ofNat 8) (by native_decide)
      mem_cost
      (solcErrorStringMem3_mload64 ⟨27⟩ catFileIlkUintUnrecognizedRawWord hmem hread64)
      (by decide) (by evm_ov),
    raw swap1 (by native_decide) (by evm_ov),
    raw dup2 (by native_decide) (by evm_ov),
    raw swap1 (by native_decide) (by evm_ov),
    raw sub (by native_decide) (by evm_ov),
    raw push1 ⟨100⟩ (by native_decide) (by evm_ov),
    raw add (by native_decide) (by evm_ov),
    raw swap1 (by native_decide) (by evm_ov),
    raw rev 0 (by native_decide) mem_cost (by evm_ov)]

/-! ### success / revert wrappers -/

theorem RD.catFileIlkChopSuccess {cA gh bl σ σ₀ A I} {g : Sat256} {sel : UInt256}
    (hreach : ∃ k C, RD catBytecode I g (initState cA gh bl σ σ₀ g A I)
      ⟨261⟩ [sel] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C)
    (hperm : I.perm = true)
    (hsz100 : 100 ≤ I.calldata.size)
    (hsize : I.calldata.size < UInt256.size)
    (hauth : solcSlotWord σ I (solcMappingSlot ⟨0⟩ (solcSourceWord I)) = ⟨1⟩)
    (hwhat : fileIlkUintWhat I = fileIlkChopBytes) :
    RDret catBytecode g (initState cA gh bl σ σ₀ g A I)
      (cA, sstoreAccountMap I.codeOwner σ (fileIlkUintChopSlotFor I) (fileIlkUintData I))
      ByteArray.empty := by
  obtain ⟨_, _, hswitch⟩ := RD.catFileIlkUintToSwitch hreach hsz100 hsize hauth
  have hword : fileIlkUintWhatWord I = ABI.bytesToWord fileIlkChopBytes :=
    fileIlkUintWhatWord_eq_of_bytes_eq (by omega) hwhat
  have hmemAuth : (twoWordHashMem (solcSourceWord I) ⟨0⟩ solcFreePtrMem).size = 96 :=
    twoWordHashMem_size_96 (solcSourceWord I) ⟨0⟩ solcFreePtrMem_size
  obtain ⟨_, _, hretPc⟩ := RD.catFileIlkStoreChop
    (data := fileIlkUintData I) (what := fileIlkUintWhatWord I) (ilk := fileIlkUintIlkWord I)
    (ret := ⟨302⟩) (sel := sel) (R := [])
    hswitch hword hmemAuth (by native_decide) hperm (by simp)
  have hretPc' := hretPc.jumpdest (by native_decide) (by evm_ov)
  simpa [fileIlkUintChopSlotFor_eq (by omega : 36 ≤ I.calldata.size)] using
    RD.stop hretPc' (by native_decide) (by simp)

theorem RD.catFileIlkDunkSuccess {cA gh bl σ σ₀ A I} {g : Sat256} {sel : UInt256}
    (hreach : ∃ k C, RD catBytecode I g (initState cA gh bl σ σ₀ g A I)
      ⟨261⟩ [sel] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C)
    (hperm : I.perm = true)
    (hsz100 : 100 ≤ I.calldata.size)
    (hsize : I.calldata.size < UInt256.size)
    (hauth : solcSlotWord σ I (solcMappingSlot ⟨0⟩ (solcSourceWord I)) = ⟨1⟩)
    (hnotChop : fileIlkUintWhat I ≠ fileIlkChopBytes)
    (hwhat : fileIlkUintWhat I = fileIlkDunkBytes) :
    RDret catBytecode g (initState cA gh bl σ σ₀ g A I)
      (cA, sstoreAccountMap I.codeOwner σ (fileIlkUintDunkSlotFor I) (fileIlkUintData I))
      ByteArray.empty := by
  obtain ⟨_, _, hswitch⟩ := RD.catFileIlkUintToSwitch hreach hsz100 hsize hauth
  have hchopNe : fileIlkUintWhatWord I ≠ ABI.bytesToWord fileIlkChopBytes :=
    fileIlkUintWhatWord_ne_of_bytes_ne (by omega) hnotChop (by native_decide)
  obtain ⟨_, _, hdunkPc⟩ := RD.catFileIlkSkipChop
    (data := fileIlkUintData I) (what := fileIlkUintWhatWord I) (ilk := fileIlkUintIlkWord I)
    (ret := ⟨302⟩) (sel := sel) (R := []) hswitch hchopNe (by simp)
  have hword : fileIlkUintWhatWord I = ABI.bytesToWord fileIlkDunkBytes :=
    fileIlkUintWhatWord_eq_of_bytes_eq (by omega) hwhat
  have hmemAuth : (twoWordHashMem (solcSourceWord I) ⟨0⟩ solcFreePtrMem).size = 96 :=
    twoWordHashMem_size_96 (solcSourceWord I) ⟨0⟩ solcFreePtrMem_size
  obtain ⟨_, _, hretPc⟩ := RD.catFileIlkStoreDunk
    (data := fileIlkUintData I) (what := fileIlkUintWhatWord I) (ilk := fileIlkUintIlkWord I)
    (ret := ⟨302⟩) (sel := sel) (R := [])
    hdunkPc hword hmemAuth (by native_decide) hperm (by simp)
  have hretPc' := hretPc.jumpdest (by native_decide) (by evm_ov)
  simpa [fileIlkUintDunkSlotFor_eq (by omega : 36 ≤ I.calldata.size)] using
    RD.stop hretPc' (by native_decide) (by simp)

theorem RD.catFileIlkUintUnrecognizedParamRevert {cA gh bl σ σ₀ A I} {g : Sat256} {sel : UInt256}
    (hreach : ∃ k C, RD catBytecode I g (initState cA gh bl σ σ₀ g A I)
      ⟨261⟩ [sel] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C)
    (hsz100 : 100 ≤ I.calldata.size)
    (hsize : I.calldata.size < UInt256.size)
    (hauth : solcSlotWord σ I (solcMappingSlot ⟨0⟩ (solcSourceWord I)) = ⟨1⟩)
    (hnotChop : fileIlkUintWhat I ≠ fileIlkChopBytes)
    (hnotDunk : fileIlkUintWhat I ≠ fileIlkDunkBytes) :
    RDrev catBytecode g (initState cA gh bl σ σ₀ g A I) := by
  obtain ⟨_, _, hswitch⟩ := RD.catFileIlkUintToSwitch hreach hsz100 hsize hauth
  have hchopNe : fileIlkUintWhatWord I ≠ ABI.bytesToWord fileIlkChopBytes :=
    fileIlkUintWhatWord_ne_of_bytes_ne (by omega) hnotChop (by native_decide)
  obtain ⟨_, _, hdunkPc⟩ := RD.catFileIlkSkipChop
    (data := fileIlkUintData I) (what := fileIlkUintWhatWord I) (ilk := fileIlkUintIlkWord I)
    (ret := ⟨302⟩) (sel := sel) (R := []) hswitch hchopNe (by simp)
  have hdunkNe : fileIlkUintWhatWord I ≠ ABI.bytesToWord fileIlkDunkBytes :=
    fileIlkUintWhatWord_ne_of_bytes_ne (by omega) hnotDunk (by native_decide)
  obtain ⟨_, _, htailPc⟩ := RD.catFileIlkSkipDunk
    (data := fileIlkUintData I) (what := fileIlkUintWhatWord I) (ilk := fileIlkUintIlkWord I)
    (ret := ⟨302⟩) (sel := sel) (R := []) hdunkPc hdunkNe (by simp)
  have hmemAuth : (twoWordHashMem (solcSourceWord I) ⟨0⟩ solcFreePtrMem).size = 96 :=
    twoWordHashMem_size_96 (solcSourceWord I) ⟨0⟩ solcFreePtrMem_size
  have hread64 :
      (twoWordHashMem (solcSourceWord I) ⟨0⟩ solcFreePtrMem).readWithPadding 64 32 =
        UInt256.toByteArray ⟨128⟩ :=
    twoWordHashMem_read64 (solcSourceWord I) ⟨0⟩ solcFreePtrMem_size solcFreePtrMem_read64
  exact RD.catFileIlkUintUnrecognizedRevert htailPc hmemAuth hread64 (by simp)

/-! ### body core -/

theorem catFileIlkUintBodyCore
    {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256} {sel : UInt256}
    (hcode : I.code = catBytecode) (hwv : I.weiValue = ⟨0⟩)
    (hperm : I.perm = true) (hsz100 : 100 ≤ I.calldata.size)
    (hsize : I.calldata.size < UInt256.size)
    (hdispatch : dispatchMsg contract I.calldata = some fileIlkUintTransition)
    (hdecode :
      decodeCalldataWithMode config.abiDecodeMode (fileIlkUintTransition.params.map Param.name)
        (transitionSignature fileIlkUintTransition).paramTypes I.calldata =
          some (fileIlkUintLocals I))
    (hreach : ∃ k C, RD catBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) ⟨261⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ_evm) k C)
    (hAccounts : accountMapEquiv σ_evm σ_solm) :
    runtimeEquivalenceFor config contract cA gh bl σ_evm σ_solm σ₀ g A I := by
  let callerSlot := catCallerWardsSlot I
  let locals := fileIlkUintLocals I
  have hcallerWord : catSlotWord callerSlot σ_evm I = catSlotWord callerSlot σ_solm I :=
    accountMapEquiv_storage_findD hAccounts I.codeOwner callerSlot ⟨0⟩
  have henc : returnEquiv ByteArray.empty none fileIlkUintTransition.returnType := by
    rw [show fileIlkUintTransition.returnType = [] by rfl]
    exact returnEquiv.fallthrough rfl (by rfl) (by native_decide)
  by_cases hauthEvm : catSlotWord callerSlot σ_evm I = ⟨1⟩
  · have hauthSolm : catSlotWord callerSlot σ_solm I = ⟨1⟩ := by
      rw [← hcallerWord]; exact hauthEvm
    have hauthSolc :
        solcSlotWord σ_evm I (solcMappingSlot ⟨0⟩ (solcSourceWord I)) = ⟨1⟩ := by
      simpa [callerSlot, catCallerWardsSlot, catSlotWord] using hauthEvm
    by_cases hchop : fileIlkUintWhat I = fileIlkChopBytes
    · let evm0 := initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I
      let evm1 := Solm.EVM.storageStore evm0 I.codeOwner (fileIlkUintChopSlotFor I)
        (fileIlkUintData I)
      have hbody :
          ExecTransitionBody config contract evm0 locals fileIlkUintTransition.body
            (.returned { contract := contract, locals := locals } evm1 none) := by
        simpa [evm0, evm1, locals] using
          (fileIlkUintChopSourceBody (cA := cA) (gh := gh) (bl := bl) (σ := σ_solm)
            (σ₀ := σ₀) (A := A) (I := I) (g := g) hwv (by omega) hauthSolm hchop)
      have hret := RD.catFileIlkChopSuccess hreach hperm hsz100 hsize hauthSolc hchop
      exact hret.reEquivExecutionGenAccountMapEquiv hcode hdispatch hdecode hbody
        (by simp [evm1, evm0, initState, storageStore_createdAccounts])
        (by
          simpa [evm1, evm0, initState, storageStore_accountMap] using
            accountMapEquiv_sstoreAccountMap I.codeOwner (fileIlkUintChopSlotFor I)
              (fileIlkUintData I) hAccounts)
        henc
    · by_cases hdunk : fileIlkUintWhat I = fileIlkDunkBytes
      · let evm0 := initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I
        let evm1 := Solm.EVM.storageStore evm0 I.codeOwner (fileIlkUintDunkSlotFor I)
          (fileIlkUintData I)
        have hbody :
            ExecTransitionBody config contract evm0 locals fileIlkUintTransition.body
              (.returned { contract := contract, locals := locals } evm1 none) := by
          simpa [evm0, evm1, locals] using
            (fileIlkUintDunkSourceBody (cA := cA) (gh := gh) (bl := bl) (σ := σ_solm)
              (σ₀ := σ₀) (A := A) (I := I) (g := g) hwv (by omega) hauthSolm hchop hdunk)
        have hret := RD.catFileIlkDunkSuccess hreach hperm hsz100 hsize hauthSolc hchop hdunk
        exact hret.reEquivExecutionGenAccountMapEquiv hcode hdispatch hdecode hbody
          (by simp [evm1, evm0, initState, storageStore_createdAccounts])
          (by
            simpa [evm1, evm0, initState, storageStore_accountMap] using
              accountMapEquiv_sstoreAccountMap I.codeOwner (fileIlkUintDunkSlotFor I)
                (fileIlkUintData I) hAccounts)
          henc
      · let evm0 := initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I
        have hbody :
            ExecTransitionBody config contract evm0 locals fileIlkUintTransition.body
              .reverted := by
          simpa [evm0, locals] using
            (fileIlkUintUnrecognizedSourceBody (cA := cA) (gh := gh) (bl := bl) (σ := σ_solm)
              (σ₀ := σ₀) (A := A) (I := I) (g := g) hwv hauthSolm hchop hdunk)
        have hrev := RD.catFileIlkUintUnrecognizedParamRevert hreach hsz100 hsize hauthSolc
          hchop hdunk
        exact hrev.reEquivExecutionRevert hcode hdispatch hdecode hbody
  · have hauthSolm : catSlotWord callerSlot σ_solm I ≠ ⟨1⟩ := by
      intro hsolm
      exact hauthEvm (by rw [hcallerWord, hsolm])
    have hauthSolc :
        solcSlotWord σ_evm I (solcMappingSlot ⟨0⟩ (solcSourceWord I)) ≠ ⟨1⟩ := by
      simpa [callerSlot, catCallerWardsSlot, catSlotWord] using hauthEvm
    let evm0 := initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I
    have hbody :
        ExecTransitionBody config contract evm0 locals fileIlkUintTransition.body .reverted := by
      simpa [evm0, locals] using
        (fileIlkUintAuthRevertSourceBody (cA := cA) (gh := gh) (bl := bl) (σ := σ_solm)
          (σ₀ := σ₀) (A := A) (I := I) (g := g) hwv hauthSolm)
    have hrev := RD.catFileIlkUintAuthRevert hreach hsz100 hsize hauthSolc
    exact hrev.reEquivExecutionRevert hcode hdispatch hdecode hbody

/-! ### short calldata + top-level -/

theorem catFileIlkUintShort {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256}
    (hcode : I.code = catBytecode) (hsize : I.calldata.size < UInt256.size)
    (_hperm : I.perm = true) (hwv : I.weiValue = ⟨0⟩)
    (hsz4 : 4 ≤ I.calldata.size) (hshort : I.calldata.size < 100)
    (hsel : selIs I ⟨#[0x1a, 0x0b, 0x28, 0x7e]⟩)
    (_hAccounts : accountMapEquiv σ_evm σ_solm) :
    runtimeEquivalenceFor config contract cA gh bl σ_evm σ_solm σ₀ g A I := by
  have hreach :=
    catReachFileIlkUintBody (cA := cA) (gh := gh) (bl := bl) (σ := σ_evm)
      (σ₀ := σ₀) (A := A) (I := I) (g := Sat256.ofUInt256 g)
      hcode hwv hsz4 hsize hsel
  have hlt :
      UInt256.lt (UInt256.sub (UInt256.ofNat I.calldata.size) ⟨4⟩) ⟨96⟩ = ⟨1⟩ := by
    apply ult_one
    rw [usub_ofNat_word_toNat (by simpa using hsz4) hsize]
    change I.calldata.size - 4 < 96
    omega
  have hrev := RD.solcExternalStaticArgsShortReverts
    (code := catBytecode) (sel := catSelWord I) (entry := ⟨261⟩) (ret := ⟨302⟩)
    (decoded := ⟨283⟩) (need := ⟨96⟩) hreach
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) hlt
  exact hrev.reEquivDecodingFailed hcode (catDispatch_fileIlkUint hsel)
    (catDecode_fileIlkUint_none_short hsz4 hshort)

theorem catFileIlkUintBody {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256}
    (hcode : I.code = catBytecode)
    (hsize : I.calldata.size < UInt256.size)
    (hperm : I.perm = true)
    (hwv : I.weiValue = ⟨0⟩)
    (hsel : selIs I ⟨#[0x1a, 0x0b, 0x28, 0x7e]⟩)
    (hAccounts : accountMapEquiv σ_evm σ_solm) :
    runtimeEquivalenceFor config contract cA gh bl σ_evm σ_solm σ₀ g A I := by
  have hsz : 4 ≤ I.calldata.size :=
    calldata_size_ge_of_selIs I ⟨#[0x1a, 0x0b, 0x28, 0x7e]⟩ (by native_decide) hsel
  by_cases hshort : I.calldata.size < 100
  · exact catFileIlkUintShort hcode hsize hperm hwv hsz hshort hsel hAccounts
  · have hsz100 : 100 ≤ I.calldata.size := by omega
    exact catFileIlkUintBodyCore hcode hwv hperm hsz100 hsize (catDispatch_fileIlkUint hsel)
      (catDecode_fileIlkUint_ok hsz100)
      (catReachFileIlkUintBody (g := Sat256.ofUInt256 g) hcode hwv hsz hsize hsel)
      hAccounts

end Benchmarks.Dss.Cat
