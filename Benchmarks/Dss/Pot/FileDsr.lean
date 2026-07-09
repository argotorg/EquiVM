import Benchmarks.Dss.Pot.Rely

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach Reasoning.Refinement

set_option maxRecDepth 2000000
set_option maxHeartbeats 0

namespace Benchmarks.Dss.Pot

/-! ## `file(bytes32,uint256)` external (auth): `require live==1; require now==rho; if what=="dsr"
    dsr = data`.  Group `@223` arm 3, entry `@367`, logic `@990`.  Selector `0x29ae8114`. -/

abbrev fileDsrWhat (I : ExecutionEnv) : List UInt8 :=
  (I.calldata.toList.drop 4).take 32

abbrev fileDsrData (I : ExecutionEnv) : UInt256 :=
  calldataWord I.calldata 36

abbrev fileDsrBytes : List UInt8 :=
  [100, 115, 114, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
   0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]

abbrev fileDsrLocals (I : ExecutionEnv) : Store :=
  ((∅ : Store).insert "what" (.fixedBytes bytes32Width (fileDsrWhat I))).insert
    "data" (.int (Int.ofNat (fileDsrData I).toNat))

/-! ### Calldata `(bytes32,uint256)` decode -/

theorem fileDsrWhat_length {I : ExecutionEnv} (hsz36 : 36 ≤ I.calldata.size) :
    (fileDsrWhat I).length = 32 := by
  simp [fileDsrWhat, List.length_take, List.length_drop, byteArray_toList_eq]
  omega

theorem fileDsrWhatWord_eq {I : ExecutionEnv} (hsz36 : 36 ≤ I.calldata.size) :
    ABI.bytesToWord (fileDsrWhat I) = calldataWord I.calldata 4 := by
  simpa [fileDsrWhat] using decode_word_at_eq I.calldata 4 (by omega) (by norm_num)

theorem fileDsrWhatWord_eq_of_bytes_eq {I : ExecutionEnv} {bs : List UInt8}
    (hsz36 : 36 ≤ I.calldata.size) (hbs : fileDsrWhat I = bs) :
    calldataWord I.calldata 4 = ABI.bytesToWord bs := by
  rw [← hbs]
  exact (fileDsrWhatWord_eq (I := I) hsz36).symm

theorem fileDsrWhat_eq_of_word_eq {I : ExecutionEnv} {bs : List UInt8}
    (hsz36 : 36 ≤ I.calldata.size) (hword : calldataWord I.calldata 4 = ABI.bytesToWord bs)
    (hbsLen : bs.length = 32) :
    fileDsrWhat I = bs := by
  have hto := toBytesBE_bytesToWord_of_length (bs := fileDsrWhat I)
    (fileDsrWhat_length (I := I) hsz36)
  rw [fileDsrWhatWord_eq (I := I) hsz36, hword] at hto
  exact hto.symm.trans (toBytesBE_bytesToWord_of_length (bs := bs) hbsLen)

theorem fileDsrWhatWord_ne_of_bytes_ne {I : ExecutionEnv} {bs : List UInt8}
    (hsz36 : 36 ≤ I.calldata.size) (hneq : fileDsrWhat I ≠ bs)
    (hbsLen : bs.length = 32) :
    calldataWord I.calldata 4 ≠ ABI.bytesToWord bs := by
  intro hword
  exact hneq (fileDsrWhat_eq_of_word_eq hsz36 hword hbsLen)

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

theorem potDecode_fileDsr_ok {I : ExecutionEnv} (hsz68 : 68 ≤ I.calldata.size) :
    decodeCalldataWithMode config.abiDecodeMode (fileDsrTransition.params.map Param.name)
      (transitionSignature fileDsrTransition).paramTypes I.calldata =
        some (fileDsrLocals I) := by
  simpa [config, fileDsrTransition, bytes32, bytes32Width, uint256, uint256Int,
    fileDsrLocals, fileDsrWhat, fileDsrData, abiBytes32, abiBytes32Width, abiUInt256] using
    (decodeCalldata_legacyBytes32_uint256_ok (cd := I.calldata) (x := "what")
      (y := "data") hsz68)

theorem potDecode_fileDsr_none_short {I : ExecutionEnv}
    (hsz4 : 4 ≤ I.calldata.size) (hshort : I.calldata.size < 68) :
    decodeCalldataWithMode config.abiDecodeMode (fileDsrTransition.params.map Param.name)
      (transitionSignature fileDsrTransition).paramTypes I.calldata = none := by
  simpa [config, fileDsrTransition, bytes32, bytes32Width, uint256, uint256Int, abiBytes32,
    abiBytes32Width, abiUInt256] using
    (decodeCalldata_legacyBytes32_uint256_none_short (cd := I.calldata) (x := "what")
      (y := "data") hsz4 hshort)

/-! ### Local-store lookups -/

theorem fileDsrLocals_get_what (I : ExecutionEnv) :
    (fileDsrLocals I).get? "what" =
      some (.fixedBytes bytes32Width (fileDsrWhat I)) := by
  rw [fileDsrLocals, store_get_ne _ _ (by decide), store_get_self]

theorem fileDsrLocals_get_data (I : ExecutionEnv) :
    (fileDsrLocals I).get? "data" =
      some (.int (Int.ofNat (fileDsrData I).toNat)) := by
  rw [fileDsrLocals, store_get_self]

theorem fileDsrLocals_get_wards (I : ExecutionEnv) :
    (fileDsrLocals I).get? "wards" = none := by
  rw [fileDsrLocals, store_get_ne _ _ (by decide), store_get_ne _ _ (by decide)]
  simp

theorem fileDsrLocals_get_dsr (I : ExecutionEnv) :
    (fileDsrLocals I).get? "dsr" = none := by
  rw [fileDsrLocals, store_get_ne _ _ (by decide), store_get_ne _ _ (by decide)]
  simp

theorem fileDsrLocals_get_live (I : ExecutionEnv) :
    (fileDsrLocals I).get? "live" = none := by
  rw [fileDsrLocals, store_get_ne _ _ (by decide), store_get_ne _ _ (by decide)]
  simp

theorem fileDsrLocals_get_rho (I : ExecutionEnv) :
    (fileDsrLocals I).get? "rho" = none := by
  rw [fileDsrLocals, store_get_ne _ _ (by decide), store_get_ne _ _ (by decide)]
  simp

/-! ### Solm-side expression evaluation -/

theorem evalExpr_fileDsrData {evm : EVM.State} {I : ExecutionEnv} {locals : Store}
    (h : locals.get? "data" = some (.int (Int.ofNat (fileDsrData I).toNat))) :
    evalExpr? config { contract := contract, locals := locals } evm (.var "data") =
      .ok (.int (Int.ofNat (fileDsrData I).toNat)) := by
  rw [evalExpr?]
  change EvalResult.ofOption EvalError.unboundVariable (locals.get? "data") =
    .ok (.int (Int.ofNat (fileDsrData I).toNat))
  rw [h]
  rfl

theorem evalExpr_fileDsrWhatEq_true {evm : EVM.State} {I : ExecutionEnv} {locals : Store}
    {bs : List UInt8}
    (hget : locals.get? "what" = some (.fixedBytes bytes32Width (fileDsrWhat I)))
    (hwhat : fileDsrWhat I = bs) :
    evalExpr? config { contract := contract, locals := locals } evm
      (.binary .eq (.var "what") (.fixedBytesLit bytes32Width bs)) = .ok (.bool true) := by
  have hvar :
      evalExpr? config { contract := contract, locals := locals } evm (.var "what") =
        .ok (.fixedBytes bytes32Width (fileDsrWhat I)) := by
    rw [evalExpr?]
    change EvalResult.ofOption EvalError.unboundVariable (locals.get? "what") =
      .ok (.fixedBytes bytes32Width (fileDsrWhat I))
    rw [hget]
    rfl
  rw [evalExpr?]
  simp only [hvar, EvalResult.bind, bind]
  simp [evalExpr?, evalBinaryOp?, hwhat]
  all_goals decide

theorem evalExpr_fileDsrWhatEq_false {evm : EVM.State} {I : ExecutionEnv} {locals : Store}
    {bs : List UInt8}
    (hget : locals.get? "what" = some (.fixedBytes bytes32Width (fileDsrWhat I)))
    (hwhat : fileDsrWhat I ≠ bs) :
    evalExpr? config { contract := contract, locals := locals } evm
      (.binary .eq (.var "what") (.fixedBytesLit bytes32Width bs)) = .ok (.bool false) := by
  have hvar :
      evalExpr? config { contract := contract, locals := locals } evm (.var "what") =
        .ok (.fixedBytes bytes32Width (fileDsrWhat I)) := by
    rw [evalExpr?]
    change EvalResult.ofOption EvalError.unboundVariable (locals.get? "what") =
      .ok (.fixedBytes bytes32Width (fileDsrWhat I))
    rw [hget]
    rfl
  rw [evalExpr?]
  simp only [hvar, EvalResult.bind, bind]
  simp [evalExpr?, evalBinaryOp?, hwhat]
  all_goals decide

theorem evalStorageRef_fileDsr_auth (evm : EVM.State) (I : ExecutionEnv)
    (hsrc : evm.executionEnv.source = I.source) :
    evalStorageRef config { contract := contract, locals := fileDsrLocals I } evm
      (wardsRef sender) = .ok (relyAuthEvaledRef I) := by
  simp [evalStorageRef, evalStorageRefStep, wardsRef, sender, envValue, relyAuthEvaledRef,
    relyAuthKey, hsrc, valueToKey?, EvalResult.bind, EvalResult.ofOption, bind, pure,
    evalExpr?]

theorem evalExpr_fileDsr_auth_true (evm : EVM.State) (I : ExecutionEnv)
    (hsrc : evm.executionEnv.source = I.source)
    (hload :
      Solm.EVM.storageLoad evm evm.executionEnv.codeOwner (relyAuthStorageSlot I) = ⟨1⟩) :
    evalExpr? config { contract := contract, locals := fileDsrLocals I } evm
      (.binary .eq (.storage (wardsRef sender)) (.intLit 1)) = .ok (.bool true) := by
  have hstorage :
      evalExpr? config { contract := contract, locals := fileDsrLocals I } evm
        (.storage (wardsRef sender)) = .ok (.int 1) := by
    rw [evalExpr_storage_scalar_value
      (cfg := config)
      (solm := { contract := contract, locals := fileDsrLocals I })
      (slot := wardsRef sender)
      (er := relyAuthEvaledRef I)
      (t := .int uint256Int)
      (loc := wordLoc (relyAuthStorageSlot I))
      (value := .int 1)
      (hbase := fileDsrLocals_get_wards I)
      (her := evalStorageRef_fileDsr_auth evm I hsrc)
      (hty := by simp [storageTypeAt?, storageTypeStep?, contract, storageDecls, uint256St])
      (hloc := by rfl)
      (hload := by simpa [hload] using potStorageLocLoad_uint256 evm (relyAuthStorageSlot I))]
  simp only [evalExpr?, hstorage, EvalResult.bind, bind, pure]
  rfl

theorem evalExpr_fileDsr_auth_false (evm : EVM.State) (I : ExecutionEnv)
    (hsrc : evm.executionEnv.source = I.source)
    (hload :
      Solm.EVM.storageLoad evm evm.executionEnv.codeOwner (relyAuthStorageSlot I) ≠ ⟨1⟩) :
    evalExpr? config { contract := contract, locals := fileDsrLocals I } evm
      (.binary .eq (.storage (wardsRef sender)) (.intLit 1)) = .ok (.bool false) := by
  have hstorage :
      evalExpr? config { contract := contract, locals := fileDsrLocals I } evm
        (.storage (wardsRef sender)) =
          .ok (.int (Int.ofNat
            (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner
              (relyAuthStorageSlot I)).toNat)) := by
    exact evalExpr_storage_scalar_value
      (cfg := config)
      (solm := { contract := contract, locals := fileDsrLocals I })
      (slot := wardsRef sender)
      (er := relyAuthEvaledRef I)
      (t := .int uint256Int)
      (loc := wordLoc (relyAuthStorageSlot I))
      (hbase := fileDsrLocals_get_wards I)
      (her := evalStorageRef_fileDsr_auth evm I hsrc)
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

theorem evalStorageRef_fileDsr_live (evm : EVM.State) (I : ExecutionEnv) :
    evalStorageRef config { contract := contract, locals := fileDsrLocals I } evm liveRef
      = .ok ({ base := "live", steps := [] } : EvaledStorageRef) := by
  simp [evalStorageRef, evalStorageRefSteps, liveRef, EvalResult.bind, pure, bind]

theorem evalStorageRef_fileDsr_rho (evm : EVM.State) (I : ExecutionEnv) :
    evalStorageRef config { contract := contract, locals := fileDsrLocals I } evm rhoRef
      = .ok ({ base := "rho", steps := [] } : EvaledStorageRef) := by
  simp [evalStorageRef, evalStorageRefSteps, rhoRef, EvalResult.bind, pure, bind]

theorem evalExpr_fileDsrLiveEq_true (evm : EVM.State) (I : ExecutionEnv)
    (hload : Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨8⟩ = ⟨1⟩) :
    evalExpr? config { contract := contract, locals := fileDsrLocals I } evm
      (.binary .eq (.storage liveRef) (.intLit 1)) = .ok (.bool true) := by
  have hstorage :
      evalExpr? config { contract := contract, locals := fileDsrLocals I } evm
        (.storage liveRef) = .ok (.int 1) := by
    rw [evalExpr_storage_scalar_value
      (cfg := config)
      (solm := { contract := contract, locals := fileDsrLocals I })
      (slot := liveRef)
      (er := ({ base := "live", steps := [] } : EvaledStorageRef))
      (t := .int uint256Int)
      (loc := wordLoc ⟨8⟩)
      (value := .int 1)
      (hbase := fileDsrLocals_get_live I)
      (her := evalStorageRef_fileDsr_live evm I)
      (hty := by simp [storageTypeAt?, contract, storageDecls, uint256St])
      (hloc := by rfl)
      (hload := by simpa [hload] using potStorageLocLoad_uint256 evm ⟨8⟩)]
  simp only [evalExpr?, hstorage, EvalResult.bind, bind, pure]
  rfl

theorem evalExpr_fileDsrLiveEq_false (evm : EVM.State) (I : ExecutionEnv)
    (hload : Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨8⟩ ≠ ⟨1⟩) :
    evalExpr? config { contract := contract, locals := fileDsrLocals I } evm
      (.binary .eq (.storage liveRef) (.intLit 1)) = .ok (.bool false) := by
  have hstorage :
      evalExpr? config { contract := contract, locals := fileDsrLocals I } evm
        (.storage liveRef) =
          .ok (.int (Int.ofNat
            (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨8⟩).toNat)) := by
    exact evalExpr_storage_scalar_value
      (cfg := config)
      (solm := { contract := contract, locals := fileDsrLocals I })
      (slot := liveRef)
      (er := ({ base := "live", steps := [] } : EvaledStorageRef))
      (t := .int uint256Int)
      (loc := wordLoc ⟨8⟩)
      (hbase := fileDsrLocals_get_live I)
      (her := evalStorageRef_fileDsr_live evm I)
      (hty := by simp [storageTypeAt?, contract, storageDecls, uint256St])
      (hloc := by rfl)
      (hload := potStorageLocLoad_uint256 evm ⟨8⟩)
  have hne :
      Value.int (Int.ofNat
          (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨8⟩).toNat) ≠ Value.int 1 := by
    intro hbad
    rw [Value.int.injEq] at hbad
    apply hload
    exact uint256_toNat_eq_one (Int.ofNat.inj hbad)
  have hbeq :
      (Value.int (Int.ofNat
          (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨8⟩).toNat) == Value.int 1) =
        false := beq_eq_false_iff_ne.mpr hne
  simp only [evalExpr?, hstorage, EvalResult.bind, bind, pure]
  change evalBinaryOp? BinaryOp.eq
      (Value.int (Int.ofNat
        (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨8⟩).toNat))
      (Value.int 1) = .ok (.bool false)
  simp only [evalBinaryOp?]
  rw [hbeq]

theorem evalExpr_fileDsrStorageRho (evm : EVM.State) (I : ExecutionEnv) :
    evalExpr? config { contract := contract, locals := fileDsrLocals I } evm (.storage rhoRef) =
      .ok (.int (Int.ofNat
        (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨7⟩).toNat)) := by
  exact evalExpr_storage_scalar_value
    (cfg := config)
    (solm := { contract := contract, locals := fileDsrLocals I })
    (slot := rhoRef)
    (er := ({ base := "rho", steps := [] } : EvaledStorageRef))
    (t := .int uint256Int)
    (loc := wordLoc ⟨7⟩)
    (hbase := fileDsrLocals_get_rho I)
    (her := evalStorageRef_fileDsr_rho evm I)
    (hty := by simp [storageTypeAt?, contract, storageDecls, uint256St])
    (hloc := by rfl)
    (hload := potStorageLocLoad_uint256 evm ⟨7⟩)

theorem evalExpr_fileDsrNowEqRho_true (evm : EVM.State) (I : ExecutionEnv)
    (htime :
      Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨7⟩ =
        UInt256.ofNat evm.executionEnv.header.timestamp) :
    evalExpr? config { contract := contract, locals := fileDsrLocals I } evm
      (.binary .eq (.env .timestamp) (.storage rhoRef)) = .ok (.bool true) := by
  have hrho := evalExpr_fileDsrStorageRho evm I
  have hval :
      (Value.int (Int.ofNat (UInt256.ofNat evm.executionEnv.header.timestamp).toNat) ==
        Value.int (Int.ofNat
          (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨7⟩).toNat)) = true := by
    rw [htime]
    simp
  simp only [evalExpr?, envValue, hrho, EvalResult.bind, bind, pure, evalBinaryOp?, hval]

theorem evalExpr_fileDsrNowEqRho_false (evm : EVM.State) (I : ExecutionEnv)
    (htime :
      UInt256.ofNat evm.executionEnv.header.timestamp ≠
        Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨7⟩) :
    evalExpr? config { contract := contract, locals := fileDsrLocals I } evm
      (.binary .eq (.env .timestamp) (.storage rhoRef)) = .ok (.bool false) := by
  have hrho := evalExpr_fileDsrStorageRho evm I
  have hval :
      (Value.int (Int.ofNat (UInt256.ofNat evm.executionEnv.header.timestamp).toNat) ==
        Value.int (Int.ofNat
          (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨7⟩).toNat)) = false := by
    rw [beq_eq_false_iff_ne]
    intro hbad
    rw [Value.int.injEq] at hbad
    exact htime (u256_inj (Int.ofNat.inj hbad))
  simp only [evalExpr?, envValue, hrho, EvalResult.bind, bind, pure, evalBinaryOp?, hval]

theorem assign_fileDsrStorage (evm : EVM.State) (I : ExecutionEnv) :
    let evm' := Solm.EVM.storageStore evm evm.executionEnv.codeOwner ⟨3⟩ (fileDsrData I)
    assignStorageRef? config { contract := contract, locals := fileDsrLocals I } evm
      .storage dsrRef (.int (Int.ofNat (fileDsrData I).toNat)) =
        .ok ({ contract := contract, locals := fileDsrLocals I }, evm') := by
  intro evm'
  apply assignStorageRef_storage_scalar
      (ty := uint256St)
      (er := ({ base := "dsr", steps := [] } : EvaledStorageRef))
      (loc := wordLoc ⟨3⟩)
      (hbase := fileDsrLocals_get_dsr I)
      (her := by simp [dsrRef, evalStorageRef, evalStorageRefSteps, EvalResult.bind, pure, bind])
      (hty := by simp [storageTypeAt?, contract, storageDecls, uint256St])
      (hloc := by rfl)
  simpa [evm'] using potStorageLocStore_uint256 evm ⟨3⟩ (fileDsrData I)

/-! ### Solm-side transition body results -/

theorem potFileDsrSourceBody {cA gh bl σ σ₀ A I} {g : UInt256}
    (hwv : I.weiValue = ⟨0⟩)
    (hauth : relyAuthWord σ I = ⟨1⟩)
    (hlive : potSlotWord ⟨8⟩ σ I = ⟨1⟩)
    (htime : potSlotWord ⟨7⟩ σ I = UInt256.ofNat I.header.timestamp)
    (hwhat : fileDsrWhat I = fileDsrBytes) :
    let locals := fileDsrLocals I
    let evm0 := initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I
    let evm1 := Solm.EVM.storageStore evm0 I.codeOwner ⟨3⟩ (fileDsrData I)
    ExecTransitionBody config contract evm0 locals fileDsrTransition.body
      (.returned { contract := contract, locals := locals } evm1 none) := by
  intro locals evm0 evm1
  have hguard :
      evalExpr? config { contract := contract, locals := locals } evm0
        (.binary .eq (.storage (wardsRef sender)) (.intLit 1)) = .ok (.bool true) := by
    simpa [locals] using evalExpr_fileDsr_auth_true evm0 I
      (by simp [evm0, initState])
      (by
        simpa [evm0, relyAuthWord, potSlotWord, initState, Solm.EVM.storageLoad,
          State.lookupAccount] using hauth)
  have hliveG :
      evalExpr? config { contract := contract, locals := locals } evm0
        (.binary .eq (.storage liveRef) (.intLit 1)) = .ok (.bool true) := by
    simpa [locals] using
      (evalExpr_fileDsrLiveEq_true evm0 I
        (by simpa [evm0, potSlotWord, initState, Solm.EVM.storageLoad, State.lookupAccount,
          solcSlotWord] using hlive))
  have hrhoG :
      evalExpr? config { contract := contract, locals := locals } evm0
        (.binary .eq (.env .timestamp) (.storage rhoRef)) = .ok (.bool true) := by
    simpa [locals] using
      (evalExpr_fileDsrNowEqRho_true evm0 I
        (by simpa [evm0, potSlotWord, initState, Solm.EVM.storageLoad, State.lookupAccount,
          solcSlotWord] using htime))
  have hcond :
      evalExpr? config { contract := contract, locals := locals } evm0
        (.binary .eq (.var "what") dsrParamLit) = .ok (.bool true) := by
    simpa [dsrParamLit, fileDsrBytes] using
      (evalExpr_fileDsrWhatEq_true (evm := evm0) (I := I) (locals := locals)
        (bs := fileDsrBytes) (by simpa [locals] using fileDsrLocals_get_what I) hwhat)
  have hdata :
      evalExpr? config { contract := contract, locals := locals } evm0 (.var "data") =
        .ok (.int (Int.ofNat (fileDsrData I).toNat)) := by
    exact evalExpr_fileDsrData (evm := evm0) (I := I) (locals := locals)
      (fileDsrLocals_get_data I)
  have hassign :
      assignStorageRef? config { contract := contract, locals := locals } evm0
        .storage dsrRef (.int (Int.ofNat (fileDsrData I).toNat)) =
          .ok ({ contract := contract, locals := locals }, evm1) := by
    simpa [locals, evm1] using assign_fileDsrStorage evm0 I
  have hthen :
      ExecBlock config { contract := contract, locals := locals } evm0
        [.assign .storage dsrRef (.var "data")]
        (.ok { contract := contract, locals := locals } evm1) :=
    ExecBlock.consNormal (ExecStmt.assign hdata hassign) ExecBlock.nil
  have hblock :
      ExecBlock config { contract := contract, locals := locals } evm0 fileDsrTransition.body
        (.ok { contract := contract, locals := locals } evm1) := by
    refine ExecBlock.consNormal (ExecStmt.requireTrue ?_) ?_
    · exact evalCallvalueEq_true (by simp [evm0, initState]; exact hwv)
    refine ExecBlock.consNormal (ExecStmt.requireTrue hguard) ?_
    refine ExecBlock.consNormal (ExecStmt.requireTrue hliveG) ?_
    refine ExecBlock.consNormal (ExecStmt.requireTrue hrhoG) ?_
    exact ExecBlock.consNormal (ExecStmt.iteTrue hcond hthen) ExecBlock.nil
  simpa [ExecTransitionBody, locals, evm0, evm1] using ExecFuncBody.execBlockOK hblock

theorem potFileDsrSourceBodyAuthReverts {cA gh bl σ σ₀ A I} {g : UInt256}
    (hwv : I.weiValue = ⟨0⟩)
    (hauth : relyAuthWord σ I ≠ ⟨1⟩) :
    let locals := fileDsrLocals I
    let evm0 := initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I
    ExecTransitionBody config contract evm0 locals fileDsrTransition.body .reverted := by
  intro locals evm0
  have hguard :
      evalExpr? config { contract := contract, locals := locals } evm0
        (.binary .eq (.storage (wardsRef sender)) (.intLit 1)) = .ok (.bool false) := by
    simpa [locals] using evalExpr_fileDsr_auth_false evm0 I
      (by simp [evm0, initState])
      (by
        simpa [evm0, relyAuthWord, potSlotWord, initState, Solm.EVM.storageLoad,
          State.lookupAccount] using hauth)
  refine ExecFuncBody.execBlockRevert ?_
  simpa [fileDsrTransition, nonpayable, auth] using
    nonpayableSecondRequireReverts
      (cfg := config)
      (solm := { contract := contract, locals := locals })
      (evm := evm0)
      (guard := .binary .eq (.storage (wardsRef sender)) (.intLit 1))
      (rest := [.require (.binary .eq (.storage liveRef) (.intLit 1)),
        .require (.binary .eq (.env .timestamp) (.storage rhoRef)),
        .ite (.binary .eq (.var "what") dsrParamLit)
          [.assign .storage dsrRef (.var "data")] [.require (.boolLit false)]])
      (by simp [evm0, initState]; exact hwv)
      hguard

theorem potFileDsrSourceBodyLiveReverts {cA gh bl σ σ₀ A I} {g : UInt256}
    (hwv : I.weiValue = ⟨0⟩)
    (hauth : relyAuthWord σ I = ⟨1⟩)
    (hlive : potSlotWord ⟨8⟩ σ I ≠ ⟨1⟩) :
    let locals := fileDsrLocals I
    let evm0 := initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I
    ExecTransitionBody config contract evm0 locals fileDsrTransition.body .reverted := by
  intro locals evm0
  have hguard :
      evalExpr? config { contract := contract, locals := locals } evm0
        (.binary .eq (.storage (wardsRef sender)) (.intLit 1)) = .ok (.bool true) := by
    simpa [locals] using evalExpr_fileDsr_auth_true evm0 I
      (by simp [evm0, initState])
      (by
        simpa [evm0, relyAuthWord, potSlotWord, initState, Solm.EVM.storageLoad,
          State.lookupAccount] using hauth)
  have hliveG :
      evalExpr? config { contract := contract, locals := locals } evm0
        (.binary .eq (.storage liveRef) (.intLit 1)) = .ok (.bool false) := by
    simpa [locals] using
      (evalExpr_fileDsrLiveEq_false evm0 I
        (by simpa [evm0, potSlotWord, initState, Solm.EVM.storageLoad, State.lookupAccount,
          solcSlotWord] using hlive))
  have hblock :
      ExecBlock config { contract := contract, locals := locals } evm0 fileDsrTransition.body
        .reverted := by
    refine ExecBlock.consNormal (ExecStmt.requireTrue ?_) ?_
    · exact evalCallvalueEq_true (by simp [evm0, initState]; exact hwv)
    refine ExecBlock.consNormal (ExecStmt.requireTrue hguard) ?_
    exact ExecBlock.consRevert (ExecStmt.requireFalse hliveG)
  simpa [ExecTransitionBody, locals, evm0] using ExecFuncBody.execBlockRevert hblock

theorem potFileDsrSourceBodyRhoReverts {cA gh bl σ σ₀ A I} {g : UInt256}
    (hwv : I.weiValue = ⟨0⟩)
    (hauth : relyAuthWord σ I = ⟨1⟩)
    (hlive : potSlotWord ⟨8⟩ σ I = ⟨1⟩)
    (htime : UInt256.ofNat I.header.timestamp ≠ potSlotWord ⟨7⟩ σ I) :
    let locals := fileDsrLocals I
    let evm0 := initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I
    ExecTransitionBody config contract evm0 locals fileDsrTransition.body .reverted := by
  intro locals evm0
  have hguard :
      evalExpr? config { contract := contract, locals := locals } evm0
        (.binary .eq (.storage (wardsRef sender)) (.intLit 1)) = .ok (.bool true) := by
    simpa [locals] using evalExpr_fileDsr_auth_true evm0 I
      (by simp [evm0, initState])
      (by
        simpa [evm0, relyAuthWord, potSlotWord, initState, Solm.EVM.storageLoad,
          State.lookupAccount] using hauth)
  have hliveG :
      evalExpr? config { contract := contract, locals := locals } evm0
        (.binary .eq (.storage liveRef) (.intLit 1)) = .ok (.bool true) := by
    simpa [locals] using
      (evalExpr_fileDsrLiveEq_true evm0 I
        (by simpa [evm0, potSlotWord, initState, Solm.EVM.storageLoad, State.lookupAccount,
          solcSlotWord] using hlive))
  have hrhoG :
      evalExpr? config { contract := contract, locals := locals } evm0
        (.binary .eq (.env .timestamp) (.storage rhoRef)) = .ok (.bool false) := by
    simpa [locals] using
      (evalExpr_fileDsrNowEqRho_false evm0 I
        (by simpa [evm0, potSlotWord, initState, Solm.EVM.storageLoad, State.lookupAccount,
          solcSlotWord] using htime))
  have hblock :
      ExecBlock config { contract := contract, locals := locals } evm0 fileDsrTransition.body
        .reverted := by
    refine ExecBlock.consNormal (ExecStmt.requireTrue ?_) ?_
    · exact evalCallvalueEq_true (by simp [evm0, initState]; exact hwv)
    refine ExecBlock.consNormal (ExecStmt.requireTrue hguard) ?_
    refine ExecBlock.consNormal (ExecStmt.requireTrue hliveG) ?_
    exact ExecBlock.consRevert (ExecStmt.requireFalse hrhoG)
  simpa [ExecTransitionBody, locals, evm0] using ExecFuncBody.execBlockRevert hblock

theorem potFileDsrSourceBodyUnrecognized {cA gh bl σ σ₀ A I} {g : UInt256}
    (hwv : I.weiValue = ⟨0⟩)
    (hauth : relyAuthWord σ I = ⟨1⟩)
    (hlive : potSlotWord ⟨8⟩ σ I = ⟨1⟩)
    (htime : potSlotWord ⟨7⟩ σ I = UInt256.ofNat I.header.timestamp)
    (hwhat : fileDsrWhat I ≠ fileDsrBytes) :
    let locals := fileDsrLocals I
    let evm0 := initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I
    ExecTransitionBody config contract evm0 locals fileDsrTransition.body .reverted := by
  intro locals evm0
  have hguard :
      evalExpr? config { contract := contract, locals := locals } evm0
        (.binary .eq (.storage (wardsRef sender)) (.intLit 1)) = .ok (.bool true) := by
    simpa [locals] using evalExpr_fileDsr_auth_true evm0 I
      (by simp [evm0, initState])
      (by
        simpa [evm0, relyAuthWord, potSlotWord, initState, Solm.EVM.storageLoad,
          State.lookupAccount] using hauth)
  have hliveG :
      evalExpr? config { contract := contract, locals := locals } evm0
        (.binary .eq (.storage liveRef) (.intLit 1)) = .ok (.bool true) := by
    simpa [locals] using
      (evalExpr_fileDsrLiveEq_true evm0 I
        (by simpa [evm0, potSlotWord, initState, Solm.EVM.storageLoad, State.lookupAccount,
          solcSlotWord] using hlive))
  have hrhoG :
      evalExpr? config { contract := contract, locals := locals } evm0
        (.binary .eq (.env .timestamp) (.storage rhoRef)) = .ok (.bool true) := by
    simpa [locals] using
      (evalExpr_fileDsrNowEqRho_true evm0 I
        (by simpa [evm0, potSlotWord, initState, Solm.EVM.storageLoad, State.lookupAccount,
          solcSlotWord] using htime))
  have hcond :
      evalExpr? config { contract := contract, locals := locals } evm0
        (.binary .eq (.var "what") dsrParamLit) = .ok (.bool false) := by
    simpa [dsrParamLit, fileDsrBytes] using
      (evalExpr_fileDsrWhatEq_false (evm := evm0) (I := I) (locals := locals)
        (bs := fileDsrBytes) (by simpa [locals] using fileDsrLocals_get_what I) hwhat)
  have hreqFalse :
      evalExpr? config { contract := contract, locals := locals } evm0 (.boolLit false) =
        .ok (.bool false) := by
    simp [evalExpr?, pure]
  have helse :
      ExecBlock config { contract := contract, locals := locals } evm0
        [.require (.boolLit false)] .reverted :=
    ExecBlock.consRevert (ExecStmt.requireFalse hreqFalse)
  have hblock :
      ExecBlock config { contract := contract, locals := locals } evm0 fileDsrTransition.body
        .reverted := by
    refine ExecBlock.consNormal (ExecStmt.requireTrue ?_) ?_
    · exact evalCallvalueEq_true (by simp [evm0, initState]; exact hwv)
    refine ExecBlock.consNormal (ExecStmt.requireTrue hguard) ?_
    refine ExecBlock.consNormal (ExecStmt.requireTrue hliveG) ?_
    refine ExecBlock.consNormal (ExecStmt.requireTrue hrhoG) ?_
    exact ExecBlock.consRevert (ExecStmt.iteFalse hcond helse)
  simpa [ExecTransitionBody, locals, evm0] using ExecFuncBody.execBlockRevert hblock

/-! ### EVM-side trace -/

theorem potReachFileDsrBody {cA gh bl σ σ₀ A I} {g : Sat256}
    (hcode : I.code = potBytecode) (hwv : I.weiValue = ⟨0⟩)
    (hsz : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hsel : selIs I (potSelBytes 7)) :
    ∃ k C, RD potBytecode I g (initState cA gh bl σ σ₀ g A I)
        ⟨367⟩ [potSelWord I] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty
        (cA, σ) k C := by
  have hword : potSelWord I = ⟨0x29ae8114⟩ :=
    potSelWord_eq_of_beq I hsz 0x29 0xae 0x81 0x14 ⟨0x29ae8114⟩
      (by native_decide) (by simpa [potSelBytes] using hsel)
  have hroot : UInt256.gt (armSelNat potBytecode potRootSplitPc) (potSelWord I) ≠ ⟨0⟩ := by
    rw [hword]; native_decide
  have h163 : UInt256.gt (armSelNat potBytecode potSplit163Pc) (potSelWord I) ≠ ⟨0⟩ := by
    rw [hword]; native_decide
  have heq0 : ∀ j, j < 3 →
      UInt256.eq (armSelNat potBytecode (nthArmPc potBytecode potG223FirstArmPc j))
        (potSelWord I) = ⟨0⟩ := by
    intro j hj; interval_cases j <;> rw [hword] <;> native_decide
  have htake :
      UInt256.eq (armSelNat potBytecode (nthArmPc potBytecode potG223FirstArmPc 3))
        (potSelWord I) ≠ ⟨0⟩ := by rw [hword]; native_decide
  exact potReachG223Body 3 (by omega) ⟨367⟩ hcode hwv hsz hsize hroot h163 heq0 htake
    (by jump_dest) (by native_decide)

theorem RD.potFileDsrDecodeToRoutine {code : ByteArray} {g : Sat256} {s0 : State}
    {ee : ExecutionEnv} {k C : ℕ} {ret de sel : UInt256} {R : List UInt256}
    {mem rdata : ByteArray} {aw : UInt256}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    (h : RD code ee g s0 ⟨389⟩ (de :: ⟨4⟩ :: ret :: sel :: R) mem aw rdata acc k C)
    (hwf : code = potBytecode)
    (hroutine : (D_J code 0).contains ⟨990⟩ = true)
    (hov : R.length + 8 ≤ 1024) :
    ∃ k' C', RD code ee g s0 ⟨990⟩
      (calldataWord ee.calldata 36 :: calldataWord ee.calldata 4 :: ret :: sel :: R)
      mem aw rdata acc k' C' := by
  subst hwf
  have rd390 := h.jumpdest (by native_decide) (by evm_ov)
  have rd391 := rd390.pop (by native_decide) (by evm_ov)
  have rd392 := rd391.dup1 (by native_decide) (by evm_ov)
  have rd393 := rd392.calldataload (by native_decide) (by evm_ov)
  have rd394 := rd393.swap1 (by native_decide) (by evm_ov)
  have rd396 := rd394.push1 ⟨32⟩ (by native_decide) (by evm_ov)
  have rd397 := rd396.add (by native_decide) (by evm_ov)
  have rd398 := rd397.calldataload (by native_decide) (by evm_ov)
  have rd401 := rd398.push2 ⟨990⟩ (by native_decide) (by evm_ov)
  exact ⟨_, _, by
    simpa [calldataWord, show (⟨4⟩ : UInt256).toNat = 4 from by decide,
      show (⟨36⟩ : UInt256).toNat = 36 from by decide]
      using rd401.jump (by native_decide) hroutine (by evm_ov)⟩

theorem potFileDsrX_decoded {cA gh bl σ σ₀ A I} {g : Sat256} {sel : UInt256}
    (hsz68 : 68 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hreach : ∃ k C, RD potBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨367⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    ∃ k C, RD potBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨990⟩
        [fileDsrData I, calldataWord I.calldata 4, ⟨301⟩, sel]
        solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
  obtain ⟨_, _, hdecoded⟩ := RD.solcExternalStaticArgsLenOk
    (code := potBytecode) (sel := sel) (entry := ⟨367⟩) (ret := ⟨301⟩)
    (decoded := ⟨389⟩) (need := ⟨64⟩) hreach
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by jump_dest)
    (by exact solcDecodeLenCheckOkUnsigned (by simpa using hsz68) hsize)
  obtain ⟨_, _, hroutine⟩ := RD.potFileDsrDecodeToRoutine
    (code := potBytecode) (ret := ⟨301⟩) (sel := sel) (R := [])
    hdecoded rfl (by jump_dest) (by simp)
  exact ⟨_, _, by simpa [fileDsrData] using hroutine⟩

set_option maxHeartbeats 1000000 in
theorem potFileDsrX_authorized {cA σ I} {g : Sat256} {s0 : State} {k C : ℕ}
    {sel data what : UInt256} (hauth : relyAuthWord σ I = ⟨1⟩)
    (h : RD potBytecode I g s0 ⟨990⟩
      [data, what, ⟨301⟩, sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    ∃ k' C', RD potBytecode I g s0 ⟨1079⟩
      [data, what, ⟨301⟩, sel]
      (relyAuthHashMem I) (UInt256.ofNat 3) ByteArray.empty (cA, σ) k' C' := by
  have hauthSlot :
      UInt256.ofNat (fromByteArrayBigEndian
          (ffi.KEC ((relyAuthHashMem I).readWithPadding 0 64))) =
        mapSlot (relySourceWord I) ⟨0⟩ := by
    simpa [relyAuthHashMem, mapSlot, solcMappingSlot] using
      twoWordHashMem_solcMappingSlot (⟨0⟩ : UInt256) (relySourceWord I)
        solcFreePtrMem_size
  have rd996pre := evm_run h with [
    raw jumpdest (by native_decide) (by evm_ov),
    raw caller (by native_decide) (by evm_ov),
    raw push1 ⟨0⟩ (by native_decide) (by evm_ov),
    raw swap1 (by native_decide) (by evm_ov),
    raw dup2 (by native_decide) (by evm_ov)]
  have rd997 := rd996pre.mstore 0 (wordAt0Mem (relySourceWord I) solcFreePtrMem)
    (UInt256.ofNat 3) (by native_decide) mem_cost (by rfl) (by native_decide) (by evm_ov)
  have rd1001pre := evm_run rd997 with [
    raw push1 ⟨32⟩ (by native_decide) (by evm_ov),
    raw dup2 (by native_decide) (by evm_ov),
    raw swap1 (by native_decide) (by evm_ov)]
  have rd1002 := rd1001pre.mstore 0 (relyAuthHashMem I)
    (UInt256.ofNat 3) (by native_decide) mem_cost (by rfl) (by native_decide) (by evm_ov)
  have rd1005pre := evm_run rd1002 with [
    raw push1 ⟨64⟩ (by native_decide) (by evm_ov),
    raw swap1 (by native_decide) (by evm_ov)]
  have rd1006 := rd1005pre.keccak256 0 (mapSlot (relySourceWord I) ⟨0⟩)
    (UInt256.ofNat 3) (by native_decide) mem_cost hauthSlot (by native_decide)
    (by evm_ov)
  obtain ⟨k1007, C1007, rd1007raw⟩ := rd1006.sload (by native_decide) (by evm_ov)
  have rd1007 : RD potBytecode I g s0 ⟨1007⟩
      (relyAuthWord σ I :: data :: what :: ⟨301⟩ :: [sel])
      (relyAuthHashMem I) (UInt256.ofNat 3) ByteArray.empty (cA, σ) k1007 C1007 := by
    simpa [relyAuthWord, potSlotWord, relyAuthStorageSlot_eq_mapSlot_source I] using rd1007raw
  have rd1010pre := evm_run rd1007 with [
    raw push1 ⟨1⟩ (by native_decide) (by evm_ov),
    raw eq (by native_decide) (by evm_ov)]
  rw [hauth, u256_eq_refl] at rd1010pre
  have rd1013 := rd1010pre.pushConst (⟨1079⟩ : UInt256)
    (width := 2) (op := .PUSH2) (by decide) (by native_decide) (by evm_ov)
  exact ⟨_, _, rd1013.jumpiT (by native_decide) one_ne_zero_uint
    (by jump_dest) (by evm_ov)⟩

set_option maxHeartbeats 1000000 in
theorem potFileDsrX_unauthorized {cA σ I} {g : Sat256} {s0 : State} {k C : ℕ}
    {sel data what : UInt256} (hauth : relyAuthWord σ I ≠ ⟨1⟩)
    (h : RD potBytecode I g s0 ⟨990⟩
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
  have rd996pre := evm_run h with [
    raw jumpdest (by native_decide) (by evm_ov),
    raw caller (by native_decide) (by evm_ov),
    raw push1 ⟨0⟩ (by native_decide) (by evm_ov),
    raw swap1 (by native_decide) (by evm_ov),
    raw dup2 (by native_decide) (by evm_ov)]
  have rd997 := rd996pre.mstore 0 (wordAt0Mem (relySourceWord I) solcFreePtrMem)
    (UInt256.ofNat 3) (by native_decide) mem_cost (by rfl) (by native_decide) (by evm_ov)
  have rd1001pre := evm_run rd997 with [
    raw push1 ⟨32⟩ (by native_decide) (by evm_ov),
    raw dup2 (by native_decide) (by evm_ov),
    raw swap1 (by native_decide) (by evm_ov)]
  have rd1002 := rd1001pre.mstore 0 (relyAuthHashMem I)
    (UInt256.ofNat 3) (by native_decide) mem_cost (by rfl) (by native_decide) (by evm_ov)
  have rd1005pre := evm_run rd1002 with [
    raw push1 ⟨64⟩ (by native_decide) (by evm_ov),
    raw swap1 (by native_decide) (by evm_ov)]
  have rd1006 := rd1005pre.keccak256 0 (mapSlot (relySourceWord I) ⟨0⟩)
    (UInt256.ofNat 3) (by native_decide) mem_cost hauthSlot (by native_decide)
    (by evm_ov)
  obtain ⟨k1007, C1007, rd1007raw⟩ := rd1006.sload (by native_decide) (by evm_ov)
  have rd1007 : RD potBytecode I g s0 ⟨1007⟩
      (relyAuthWord σ I :: data :: what :: ⟨301⟩ :: [sel])
      (relyAuthHashMem I) (UInt256.ofNat 3) ByteArray.empty (cA, σ) k1007 C1007 := by
    simpa [relyAuthWord, potSlotWord, relyAuthStorageSlot_eq_mapSlot_source I] using rd1007raw
  have rd1010pre := evm_run rd1007 with [
    raw push1 ⟨1⟩ (by native_decide) (by evm_ov),
    raw eq (by native_decide) (by evm_ov)]
  have heq : UInt256.eq (⟨1⟩ : UInt256) (relyAuthWord σ I) = ⟨0⟩ := by
    exact u256_eq_of_ne (by intro hbad; exact hauth hbad.symm)
  rw [heq] at rd1010pre
  have rd1013 := rd1010pre.pushConst (⟨1079⟩ : UInt256)
    (width := 2) (op := .PUSH2) (by decide) (by native_decide) (by evm_ov)
  have rd1014 := rd1013.jumpiNT (by native_decide) rfl (by evm_ov)
  exact RD.solcErrorStringRevertTail
    (pc := ⟨1014⟩)
    (len := ⟨18⟩)
    (rawWord := ⟨0x141bdd0bdb9bdd0b585d5d1a1bdc9a5e9959⟩)
    (shift := ⟨114⟩)
    (word := ⟨0x506f742f6e6f742d617574686f72697a65640000000000000000000000000000⟩)
    (op := .PUSH18)
    (width := 18)
    rd1014
    (by
      unfold solcErrorStringRevertTailWf
      repeat' first | apply And.intro | native_decide)
    (by decide)
    relyNotAuthorizedWord
    (relyAuthHashMem_size I)
    (relyAuthHashMem_read64 I)
    (by simp only [List.length_cons, List.length_nil]; omega)

set_option maxHeartbeats 400000 in
theorem potFileDsrX_liveOK {cA σ I} {g : Sat256} {s0 : State} {k C : ℕ}
    {sel data what : UInt256} (hlive : potSlotWord ⟨8⟩ σ I = ⟨1⟩)
    (h : RD potBytecode I g s0 ⟨1079⟩
      [data, what, ⟨301⟩, sel]
      (relyAuthHashMem I) (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    ∃ k' C', RD potBytecode I g s0 ⟨1149⟩
      [data, what, ⟨301⟩, sel]
      (relyAuthHashMem I) (UInt256.ofNat 3) ByteArray.empty (cA, σ) k' C' := by
  have rd1080 := h.jumpdest (by native_decide) (by evm_ov)
  have rd1082 := rd1080.push1 ⟨8⟩ (by native_decide) (by evm_ov)
  obtain ⟨k1083, C1083, rd1083raw⟩ := rd1082.sload (by native_decide) (by evm_ov)
  have rd1083 : RD potBytecode I g s0 ⟨1083⟩
      (potSlotWord ⟨8⟩ σ I :: data :: what :: ⟨301⟩ :: [sel])
      (relyAuthHashMem I) (UInt256.ofNat 3) ByteArray.empty (cA, σ) k1083 C1083 := by
    simpa [potSlotWord] using rd1083raw
  have rd1085pre := evm_run rd1083 with [
    raw push1 ⟨1⟩ (by native_decide) (by evm_ov),
    raw eq (by native_decide) (by evm_ov)]
  rw [hlive, u256_eq_refl] at rd1085pre
  have rd1088 := rd1085pre.pushConst (⟨1149⟩ : UInt256)
    (width := 2) (op := .PUSH2) (by decide) (by native_decide) (by evm_ov)
  exact ⟨_, _, rd1088.jumpiT (by native_decide) one_ne_zero_uint
    (by jump_dest) (by evm_ov)⟩

set_option maxHeartbeats 1000000 in
theorem potFileDsrX_liveRevert {cA σ I} {g : Sat256} {s0 : State} {k C : ℕ}
    {sel data what : UInt256} (hlive : potSlotWord ⟨8⟩ σ I ≠ ⟨1⟩)
    (h : RD potBytecode I g s0 ⟨1079⟩
      [data, what, ⟨301⟩, sel]
      (relyAuthHashMem I) (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    RDrev potBytecode g s0 := by
  have rd1080 := h.jumpdest (by native_decide) (by evm_ov)
  have rd1082 := rd1080.push1 ⟨8⟩ (by native_decide) (by evm_ov)
  obtain ⟨k1083, C1083, rd1083raw⟩ := rd1082.sload (by native_decide) (by evm_ov)
  have rd1083 : RD potBytecode I g s0 ⟨1083⟩
      (potSlotWord ⟨8⟩ σ I :: data :: what :: ⟨301⟩ :: [sel])
      (relyAuthHashMem I) (UInt256.ofNat 3) ByteArray.empty (cA, σ) k1083 C1083 := by
    simpa [potSlotWord] using rd1083raw
  have rd1085pre := evm_run rd1083 with [
    raw push1 ⟨1⟩ (by native_decide) (by evm_ov),
    raw eq (by native_decide) (by evm_ov)]
  have heq : UInt256.eq (⟨1⟩ : UInt256) (potSlotWord ⟨8⟩ σ I) = ⟨0⟩ := by
    exact u256_eq_of_ne (by intro hbad; exact hlive hbad.symm)
  rw [heq] at rd1085pre
  have rd1088 := rd1085pre.pushConst (⟨1149⟩ : UInt256)
    (width := 2) (op := .PUSH2) (by decide) (by native_decide) (by evm_ov)
  have rd1089 := rd1088.jumpiNT (by native_decide) rfl (by evm_ov)
  exact RD.solcErrorStringRevertTail
    (pc := ⟨1090⟩)
    (len := ⟨12⟩)
    (rawWord := ⟨0x506f742f6e6f742d6c697665⟩)
    (shift := ⟨160⟩)
    (word := ⟨0x506f742f6e6f742d6c6976650000000000000000000000000000000000000000⟩)
    (op := .PUSH12)
    (width := 12)
    rd1089
    (by
      unfold solcErrorStringRevertTailWf
      repeat' first | apply And.intro | native_decide)
    (by decide)
    (by native_decide)
    (relyAuthHashMem_size I)
    (relyAuthHashMem_read64 I)
    (by simp only [List.length_cons, List.length_nil]; omega)

set_option maxHeartbeats 400000 in
theorem potFileDsrX_rhoOK {cA σ I} {g : Sat256} {s0 : State} {k C : ℕ}
    {sel data what : UInt256}
    (htime : potSlotWord ⟨7⟩ σ I = UInt256.ofNat I.header.timestamp)
    (h : RD potBytecode I g s0 ⟨1149⟩
      [data, what, ⟨301⟩, sel]
      (relyAuthHashMem I) (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    ∃ k' C', RD potBytecode I g s0 ⟨1225⟩
      [data, what, ⟨301⟩, sel]
      (relyAuthHashMem I) (UInt256.ofNat 3) ByteArray.empty (cA, σ) k' C' := by
  have rd1150 := h.jumpdest (by native_decide) (by evm_ov)
  have rd1152 := rd1150.push1 ⟨7⟩ (by native_decide) (by evm_ov)
  obtain ⟨k1153, C1153, rd1153raw⟩ := rd1152.sload (by native_decide) (by evm_ov)
  have rd1153 : RD potBytecode I g s0 ⟨1153⟩
      (potSlotWord ⟨7⟩ σ I :: data :: what :: ⟨301⟩ :: [sel])
      (relyAuthHashMem I) (UInt256.ofNat 3) ByteArray.empty (cA, σ) k1153 C1153 := by
    simpa [potSlotWord] using rd1153raw
  have rd1154 := rd1153.timestamp (by native_decide) (by evm_ov)
  have rd1155 := rd1154.eq (by native_decide) (by evm_ov)
  rw [htime, u256_eq_refl] at rd1155
  have rd1158 := rd1155.pushConst (⟨1225⟩ : UInt256)
    (width := 2) (op := .PUSH2) (by decide) (by native_decide) (by evm_ov)
  exact ⟨_, _, rd1158.jumpiT (by native_decide) one_ne_zero_uint
    (by jump_dest) (by evm_ov)⟩

set_option maxHeartbeats 1000000 in
theorem potFileDsrX_rhoRevert {cA σ I} {g : Sat256} {s0 : State} {k C : ℕ}
    {sel data what : UInt256}
    (htime : UInt256.ofNat I.header.timestamp ≠ potSlotWord ⟨7⟩ σ I)
    (h : RD potBytecode I g s0 ⟨1149⟩
      [data, what, ⟨301⟩, sel]
      (relyAuthHashMem I) (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    RDrev potBytecode g s0 := by
  have rd1150 := h.jumpdest (by native_decide) (by evm_ov)
  have rd1152 := rd1150.push1 ⟨7⟩ (by native_decide) (by evm_ov)
  obtain ⟨k1153, C1153, rd1153raw⟩ := rd1152.sload (by native_decide) (by evm_ov)
  have rd1153 : RD potBytecode I g s0 ⟨1153⟩
      (potSlotWord ⟨7⟩ σ I :: data :: what :: ⟨301⟩ :: [sel])
      (relyAuthHashMem I) (UInt256.ofNat 3) ByteArray.empty (cA, σ) k1153 C1153 := by
    simpa [potSlotWord] using rd1153raw
  have rd1154 := rd1153.timestamp (by native_decide) (by evm_ov)
  have rd1155 := rd1154.eq (by native_decide) (by evm_ov)
  have heq : UInt256.eq (UInt256.ofNat I.header.timestamp) (potSlotWord ⟨7⟩ σ I) = ⟨0⟩ :=
    u256_eq_of_ne htime
  rw [heq] at rd1155
  have rd1158 := rd1155.pushConst (⟨1225⟩ : UInt256)
    (width := 2) (op := .PUSH2) (by decide) (by native_decide) (by evm_ov)
  have rd1159 := rd1158.jumpiNT (by native_decide) rfl (by evm_ov)
  exact RD.solcErrorStringRevertTail
    (pc := ⟨1159⟩)
    (len := ⟨19⟩)
    (rawWord := ⟨0x141bdd0bdc9a1bcb5b9bdd0b5d5c19185d1959⟩)
    (shift := ⟨106⟩)
    (word := ⟨0x506f742f72686f2d6e6f742d7570646174656400000000000000000000000000⟩)
    (op := .PUSH19)
    (width := 19)
    rd1159
    (by
      unfold solcErrorStringRevertTailWf
      repeat' first | apply And.intro | native_decide)
    (by decide)
    (by native_decide)
    (relyAuthHashMem_size I)
    (relyAuthHashMem_read64 I)
    (by simp only [List.length_cons, List.length_nil]; omega)

/-! ### Shared `file-unrecognized-param` revert (`@1249`), reused by `FileVow`. -/

abbrev potFileUnrecognizedRawWord : UInt256 :=
  ⟨0x506f742f66696c652d756e7265636f676e697a65642d706172616d0000000000⟩

theorem RD.potFileUnrecognizedRevert {g : Sat256} {s0 : State} {ee : ExecutionEnv}
    {k C : ℕ} {stk : List UInt256} {mem rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    (h : RD potBytecode ee g s0 ⟨1249⟩ stk mem (UInt256.ofNat 3) rdata acc k C)
    (hmem : mem.size = 96)
    (hread64 : mem.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩)
    (hov : stk.length + 5 ≤ 1024) :
    RDrev potBytecode g s0 := by
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
  have rdRaw := rdPrefix.pushConst potFileUnrecognizedRawWord
    (width := 32) (op := .PUSH32) (by decide) (by native_decide)
    (by simp only [List.length_cons]; omega)
  exact evm_run rdRaw with [
    raw push1 ⟨68⟩ (by native_decide) (by evm_ov),
    raw dup3 (by native_decide) (by evm_ov),
    raw add (by native_decide) (by evm_ov),
    raw mstore 3 (solcErrorStringMem3 ⟨27⟩ potFileUnrecognizedRawWord mem)
      (UInt256.ofNat 8) (by native_decide) mem_cost (by rfl) (by decide) (by evm_ov),
    raw swap1 (by native_decide) (by evm_ov),
    raw mload 0 ⟨128⟩ (UInt256.ofNat 8) (by native_decide)
      mem_cost
      (solcErrorStringMem3_mload64 ⟨27⟩ potFileUnrecognizedRawWord hmem hread64)
      (by decide) (by evm_ov),
    raw swap1 (by native_decide) (by evm_ov),
    raw dup2 (by native_decide) (by evm_ov),
    raw swap1 (by native_decide) (by evm_ov),
    raw sub (by native_decide) (by evm_ov),
    raw push1 ⟨100⟩ (by native_decide) (by evm_ov),
    raw add (by native_decide) (by evm_ov),
    raw swap1 (by native_decide) (by evm_ov),
    raw rev 0 (by native_decide) mem_cost (by evm_ov)]

set_option maxHeartbeats 1000000 in
theorem potFileDsrX_storeAuthorized {cA σ I} {g : Sat256} {s0 : State} {k C : ℕ}
    {sel : UInt256} (hperm : I.perm = true)
    (hmatch : calldataWord I.calldata 4 = ABI.bytesToWord fileDsrBytes)
    (h : RD potBytecode I g s0 ⟨1225⟩
      [fileDsrData I, calldataWord I.calldata 4, ⟨301⟩, sel]
      (relyAuthHashMem I) (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    RDret potBytecode g s0
      (cA, sstoreAccountMap I.codeOwner σ ⟨3⟩ (fileDsrData I))
      ByteArray.empty := by
  have rd1226 := h.jumpdest (by native_decide) (by evm_ov)
  have rd1227 := rd1226.dup2 (by native_decide) (by evm_ov)
  have rd1231 := rd1227.pushConst (⟨0x3239b9⟩ : UInt256)
    (width := 3) (op := .PUSH3) (by decide) (by native_decide) (by evm_ov)
  have rd1233 := rd1231.push1 ⟨233⟩ (by native_decide) (by evm_ov)
  have rd1234 := rd1233.shl (by native_decide) (by evm_ov)
  have hconst : UInt256.shiftLeft (⟨0x3239b9⟩ : UInt256) ⟨233⟩ =
      ABI.bytesToWord fileDsrBytes := by native_decide
  rw [hmatch, ← hconst] at rd1234
  have rd1235 := rd1234.eq (by native_decide) (by evm_ov)
  rw [uInt256_eq_self] at rd1235
  have rd1236 := rd1235.iszero (by native_decide) (by evm_ov)
  rw [show UInt256.isZero (⟨1⟩ : UInt256) = ⟨0⟩ from by decide] at rd1236
  have rd1239 := rd1236.pushConst (⟨1249⟩ : UInt256)
    (width := 2) (op := .PUSH2) (by decide) (by native_decide) (by evm_ov)
  have rd1240 := rd1239.jumpiNT (by native_decide)
    (by decide : (⟨0⟩ : UInt256) = ⟨0⟩) (by evm_ov)
  have rd1242 := rd1240.push1 ⟨3⟩ (by native_decide) (by evm_ov)
  have rd1243 := rd1242.dup2 (by native_decide) (by evm_ov)
  have rd1244 := rd1243.swap1 (by native_decide) (by evm_ov)
  obtain ⟨_, _, rd1245raw⟩ := rd1244.sstore hperm (by native_decide) (by evm_ov)
  have rd1248 := rd1245raw.push2 ⟨1326⟩ (by native_decide) (by evm_ov)
  have rd1326 := rd1248.jump (by native_decide) (by jump_dest) (by evm_ov)
  have rd1327 := rd1326.jumpdest (by native_decide) (by evm_ov)
  have rd1328 := rd1327.pop (by native_decide) (by evm_ov)
  have rd1329 := rd1328.pop (by native_decide) (by evm_ov)
  have rd301 := rd1329.jump (by native_decide) (by jump_dest) (by evm_ov)
  have rd302 := rd301.jumpdest (by native_decide) (by evm_ov)
  exact RD.stop rd302 (by native_decide) (by evm_ov)

set_option maxHeartbeats 1000000 in
theorem potFileDsrX_unrecognized {cA σ I} {g : Sat256} {s0 : State} {k C : ℕ}
    {sel : UInt256}
    (hneq : calldataWord I.calldata 4 ≠ ABI.bytesToWord fileDsrBytes)
    (h : RD potBytecode I g s0 ⟨1225⟩
      [fileDsrData I, calldataWord I.calldata 4, ⟨301⟩, sel]
      (relyAuthHashMem I) (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    RDrev potBytecode g s0 := by
  have rd1226 := h.jumpdest (by native_decide) (by evm_ov)
  have rd1227 := rd1226.dup2 (by native_decide) (by evm_ov)
  have rd1231 := rd1227.pushConst (⟨0x3239b9⟩ : UInt256)
    (width := 3) (op := .PUSH3) (by decide) (by native_decide) (by evm_ov)
  have rd1233 := rd1231.push1 ⟨233⟩ (by native_decide) (by evm_ov)
  have rd1234 := rd1233.shl (by native_decide) (by evm_ov)
  have hconst : UInt256.shiftLeft (⟨0x3239b9⟩ : UInt256) ⟨233⟩ =
      ABI.bytesToWord fileDsrBytes := by native_decide
  rw [hconst] at rd1234
  have rd1235 := rd1234.eq (by native_decide) (by evm_ov)
  have heq0 : UInt256.eq (ABI.bytesToWord fileDsrBytes) (calldataWord I.calldata 4) = ⟨0⟩ :=
    u256_eq_of_ne (fun h => hneq h.symm)
  rw [heq0] at rd1235
  have rd1236 := rd1235.iszero (by native_decide) (by evm_ov)
  rw [show UInt256.isZero (⟨0⟩ : UInt256) = ⟨1⟩ from by decide] at rd1236
  have rd1239 := rd1236.pushConst (⟨1249⟩ : UInt256)
    (width := 2) (op := .PUSH2) (by decide) (by native_decide) (by evm_ov)
  have rd1249 := rd1239.jumpiT (by native_decide) one_ne_zero_uint (by jump_dest)
    (by evm_ov)
  exact RD.potFileUnrecognizedRevert rd1249
    (relyAuthHashMem_size I)
    (relyAuthHashMem_read64 I)
    (by simp only [List.length_cons, List.length_nil]; omega)

theorem potFileDsrX_shortarg {cA gh bl σ σ₀ A I} {g : Sat256} {sel : UInt256}
    (hsz4 : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hshort : I.calldata.size < 68)
    (hreach : ∃ k C, RD potBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨367⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    RDrev potBytecode g (initState cA gh bl σ σ₀ g A I) := by
  have hlt :
      UInt256.lt (UInt256.sub (UInt256.ofNat I.calldata.size) ⟨4⟩) ⟨64⟩ = ⟨1⟩ := by
    apply ult_one
    rw [usub_ofNat_word_toNat (by simpa using hsz4) hsize]
    change I.calldata.size - 4 < 64
    omega
  exact RD.solcExternalStaticArgsShortReverts
    (code := potBytecode) (sel := sel) (entry := ⟨367⟩) (ret := ⟨301⟩)
    (decoded := ⟨389⟩) (need := ⟨64⟩) hreach
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) hlt

/-! ### Body core lemmas -/

theorem potFileDsrBodyCoreOk
    {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256} {sel : UInt256}
    (hcode : I.code = potBytecode) (hsize : I.calldata.size < UInt256.size)
    (hperm : I.perm = true) (hwv : I.weiValue = ⟨0⟩)
    (hsz68 : 68 ≤ I.calldata.size)
    (hauth : relyAuthWord σ_evm I = ⟨1⟩)
    (hlive : potSlotWord ⟨8⟩ σ_evm I = ⟨1⟩)
    (htime : potSlotWord ⟨7⟩ σ_evm I = UInt256.ofNat I.header.timestamp)
    (hwhat : fileDsrWhat I = fileDsrBytes)
    (hdispatch : dispatchMsg contract I.calldata = some fileDsrTransition)
    (hdecode :
      decodeCalldataWithMode config.abiDecodeMode (fileDsrTransition.params.map Param.name)
        (transitionSignature fileDsrTransition).paramTypes I.calldata = some (fileDsrLocals I))
    (hreach : ∃ k C, RD potBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) ⟨367⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ_evm) k C)
    (hAccounts : accountMapEquiv σ_evm σ_solm) :
    runtimeEquivalenceFor config contract cA gh bl σ_evm σ_solm σ₀ g A I := by
  let data := fileDsrData I
  let locals := fileDsrLocals I
  let evm0 := initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I
  let evm1 := Solm.EVM.storageStore evm0 I.codeOwner ⟨3⟩ data
  have hauthSolm : relyAuthWord σ_solm I = ⟨1⟩ := by
    have hword : relyAuthWord σ_evm I = relyAuthWord σ_solm I :=
      accountMapEquiv_storage_findD hAccounts I.codeOwner (relyAuthStorageSlot I) ⟨0⟩
    rw [← hword]; exact hauth
  have hliveSolm : potSlotWord ⟨8⟩ σ_solm I = ⟨1⟩ := by
    have hword : potSlotWord ⟨8⟩ σ_evm I = potSlotWord ⟨8⟩ σ_solm I :=
      accountMapEquiv_storage_findD hAccounts I.codeOwner ⟨8⟩ ⟨0⟩
    rw [← hword]; exact hlive
  have htimeSolm : potSlotWord ⟨7⟩ σ_solm I = UInt256.ofNat I.header.timestamp := by
    have hword : potSlotWord ⟨7⟩ σ_evm I = potSlotWord ⟨7⟩ σ_solm I :=
      accountMapEquiv_storage_findD hAccounts I.codeOwner ⟨7⟩ ⟨0⟩
    rw [← hword]; exact htime
  have hbody :
      ExecTransitionBody config contract evm0 locals fileDsrTransition.body
        (.returned { contract := contract, locals := locals } evm1 none) := by
    simpa [evm0, evm1, locals, data] using
      (potFileDsrSourceBody (cA := cA) (gh := gh) (bl := bl) (σ := σ_solm)
        (σ₀ := σ₀) (A := A) (I := I) (g := g) hwv hauthSolm hliveSolm htimeSolm hwhat)
  obtain ⟨_, _, hdecoded⟩ := potFileDsrX_decoded (g := Sat256.ofUInt256 g) hsz68 hsize hreach
  obtain ⟨_, _, hauthd⟩ := potFileDsrX_authorized (I := I) hauth hdecoded
  obtain ⟨_, _, hlived⟩ := potFileDsrX_liveOK (I := I) hlive hauthd
  obtain ⟨_, _, hrhod⟩ := potFileDsrX_rhoOK (I := I) htime hlived
  have hmatch : calldataWord I.calldata 4 = ABI.bytesToWord fileDsrBytes :=
    fileDsrWhatWord_eq_of_bytes_eq (by omega) hwhat
  have hret := potFileDsrX_storeAuthorized hperm hmatch hrhod
  exact hret.reEquivExecutionGenAccountMapEquiv hcode hdispatch hdecode hbody
    (by simp [evm1, evm0, initState, storageStore_createdAccounts])
    (by
      simpa [evm1, evm0, initState, storageStore_accountMap, data] using
        accountMapEquiv_sstoreAccountMap I.codeOwner ⟨3⟩ data hAccounts)
    (by
      simpa [fileDsrTransition] using
        (returnEquiv.fallthrough (o := ByteArray.empty) (r := none) (t := [])
          (dvs := []) rfl (by native_decide) (by native_decide)))

theorem potFileDsrBodyCoreUnauthorized
    {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256} {sel : UInt256}
    (hcode : I.code = potBytecode) (hsize : I.calldata.size < UInt256.size)
    (hwv : I.weiValue = ⟨0⟩)
    (hsz68 : 68 ≤ I.calldata.size)
    (hauth : relyAuthWord σ_evm I ≠ ⟨1⟩)
    (hdispatch : dispatchMsg contract I.calldata = some fileDsrTransition)
    (hdecode :
      decodeCalldataWithMode config.abiDecodeMode (fileDsrTransition.params.map Param.name)
        (transitionSignature fileDsrTransition).paramTypes I.calldata = some (fileDsrLocals I))
    (hreach : ∃ k C, RD potBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) ⟨367⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ_evm) k C)
    (hAccounts : accountMapEquiv σ_evm σ_solm) :
    runtimeEquivalenceFor config contract cA gh bl σ_evm σ_solm σ₀ g A I := by
  let locals := fileDsrLocals I
  let evm0 := initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I
  have hauthSolm : relyAuthWord σ_solm I ≠ ⟨1⟩ := by
    have hword : relyAuthWord σ_evm I = relyAuthWord σ_solm I :=
      accountMapEquiv_storage_findD hAccounts I.codeOwner (relyAuthStorageSlot I) ⟨0⟩
    intro hbad; exact hauth (by rw [hword, hbad])
  have hbody :
      ExecTransitionBody config contract evm0 locals fileDsrTransition.body .reverted := by
    simpa [evm0, locals] using
      (potFileDsrSourceBodyAuthReverts (cA := cA) (gh := gh) (bl := bl) (σ := σ_solm)
        (σ₀ := σ₀) (A := A) (I := I) (g := g) hwv hauthSolm)
  obtain ⟨_, _, hdecoded⟩ := potFileDsrX_decoded (g := Sat256.ofUInt256 g) hsz68 hsize hreach
  exact (potFileDsrX_unauthorized (I := I) hauth hdecoded)
    |>.reEquivExecutionRevert hcode hdispatch hdecode hbody

theorem potFileDsrBodyCoreLiveRevert
    {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256} {sel : UInt256}
    (hcode : I.code = potBytecode) (hsize : I.calldata.size < UInt256.size)
    (hwv : I.weiValue = ⟨0⟩)
    (hsz68 : 68 ≤ I.calldata.size)
    (hauth : relyAuthWord σ_evm I = ⟨1⟩)
    (hlive : potSlotWord ⟨8⟩ σ_evm I ≠ ⟨1⟩)
    (hdispatch : dispatchMsg contract I.calldata = some fileDsrTransition)
    (hdecode :
      decodeCalldataWithMode config.abiDecodeMode (fileDsrTransition.params.map Param.name)
        (transitionSignature fileDsrTransition).paramTypes I.calldata = some (fileDsrLocals I))
    (hreach : ∃ k C, RD potBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) ⟨367⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ_evm) k C)
    (hAccounts : accountMapEquiv σ_evm σ_solm) :
    runtimeEquivalenceFor config contract cA gh bl σ_evm σ_solm σ₀ g A I := by
  let locals := fileDsrLocals I
  let evm0 := initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I
  have hauthSolm : relyAuthWord σ_solm I = ⟨1⟩ := by
    have hword : relyAuthWord σ_evm I = relyAuthWord σ_solm I :=
      accountMapEquiv_storage_findD hAccounts I.codeOwner (relyAuthStorageSlot I) ⟨0⟩
    rw [← hword]; exact hauth
  have hliveSolm : potSlotWord ⟨8⟩ σ_solm I ≠ ⟨1⟩ := by
    have hword : potSlotWord ⟨8⟩ σ_evm I = potSlotWord ⟨8⟩ σ_solm I :=
      accountMapEquiv_storage_findD hAccounts I.codeOwner ⟨8⟩ ⟨0⟩
    intro hbad; exact hlive (by rw [hword, hbad])
  have hbody :
      ExecTransitionBody config contract evm0 locals fileDsrTransition.body .reverted := by
    simpa [evm0, locals] using
      (potFileDsrSourceBodyLiveReverts (cA := cA) (gh := gh) (bl := bl) (σ := σ_solm)
        (σ₀ := σ₀) (A := A) (I := I) (g := g) hwv hauthSolm hliveSolm)
  obtain ⟨_, _, hdecoded⟩ := potFileDsrX_decoded (g := Sat256.ofUInt256 g) hsz68 hsize hreach
  obtain ⟨_, _, hauthd⟩ := potFileDsrX_authorized (I := I) hauth hdecoded
  exact (potFileDsrX_liveRevert (I := I) hlive hauthd)
    |>.reEquivExecutionRevert hcode hdispatch hdecode hbody

theorem potFileDsrBodyCoreRhoRevert
    {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256} {sel : UInt256}
    (hcode : I.code = potBytecode) (hsize : I.calldata.size < UInt256.size)
    (hwv : I.weiValue = ⟨0⟩)
    (hsz68 : 68 ≤ I.calldata.size)
    (hauth : relyAuthWord σ_evm I = ⟨1⟩)
    (hlive : potSlotWord ⟨8⟩ σ_evm I = ⟨1⟩)
    (htime : UInt256.ofNat I.header.timestamp ≠ potSlotWord ⟨7⟩ σ_evm I)
    (hdispatch : dispatchMsg contract I.calldata = some fileDsrTransition)
    (hdecode :
      decodeCalldataWithMode config.abiDecodeMode (fileDsrTransition.params.map Param.name)
        (transitionSignature fileDsrTransition).paramTypes I.calldata = some (fileDsrLocals I))
    (hreach : ∃ k C, RD potBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) ⟨367⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ_evm) k C)
    (hAccounts : accountMapEquiv σ_evm σ_solm) :
    runtimeEquivalenceFor config contract cA gh bl σ_evm σ_solm σ₀ g A I := by
  let locals := fileDsrLocals I
  let evm0 := initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I
  have hauthSolm : relyAuthWord σ_solm I = ⟨1⟩ := by
    have hword : relyAuthWord σ_evm I = relyAuthWord σ_solm I :=
      accountMapEquiv_storage_findD hAccounts I.codeOwner (relyAuthStorageSlot I) ⟨0⟩
    rw [← hword]; exact hauth
  have hliveSolm : potSlotWord ⟨8⟩ σ_solm I = ⟨1⟩ := by
    have hword : potSlotWord ⟨8⟩ σ_evm I = potSlotWord ⟨8⟩ σ_solm I :=
      accountMapEquiv_storage_findD hAccounts I.codeOwner ⟨8⟩ ⟨0⟩
    rw [← hword]; exact hlive
  have htimeSolm : UInt256.ofNat I.header.timestamp ≠ potSlotWord ⟨7⟩ σ_solm I := by
    have hword : potSlotWord ⟨7⟩ σ_evm I = potSlotWord ⟨7⟩ σ_solm I :=
      accountMapEquiv_storage_findD hAccounts I.codeOwner ⟨7⟩ ⟨0⟩
    rw [← hword]; exact htime
  have hbody :
      ExecTransitionBody config contract evm0 locals fileDsrTransition.body .reverted := by
    simpa [evm0, locals] using
      (potFileDsrSourceBodyRhoReverts (cA := cA) (gh := gh) (bl := bl) (σ := σ_solm)
        (σ₀ := σ₀) (A := A) (I := I) (g := g) hwv hauthSolm hliveSolm htimeSolm)
  obtain ⟨_, _, hdecoded⟩ := potFileDsrX_decoded (g := Sat256.ofUInt256 g) hsz68 hsize hreach
  obtain ⟨_, _, hauthd⟩ := potFileDsrX_authorized (I := I) hauth hdecoded
  obtain ⟨_, _, hlived⟩ := potFileDsrX_liveOK (I := I) hlive hauthd
  exact (potFileDsrX_rhoRevert (I := I) htime hlived)
    |>.reEquivExecutionRevert hcode hdispatch hdecode hbody

theorem potFileDsrBodyCoreUnrecognized
    {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256} {sel : UInt256}
    (hcode : I.code = potBytecode) (hsize : I.calldata.size < UInt256.size)
    (hwv : I.weiValue = ⟨0⟩)
    (hsz68 : 68 ≤ I.calldata.size)
    (hauth : relyAuthWord σ_evm I = ⟨1⟩)
    (hlive : potSlotWord ⟨8⟩ σ_evm I = ⟨1⟩)
    (htime : potSlotWord ⟨7⟩ σ_evm I = UInt256.ofNat I.header.timestamp)
    (hwhat : fileDsrWhat I ≠ fileDsrBytes)
    (hdispatch : dispatchMsg contract I.calldata = some fileDsrTransition)
    (hdecode :
      decodeCalldataWithMode config.abiDecodeMode (fileDsrTransition.params.map Param.name)
        (transitionSignature fileDsrTransition).paramTypes I.calldata = some (fileDsrLocals I))
    (hreach : ∃ k C, RD potBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) ⟨367⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ_evm) k C)
    (hAccounts : accountMapEquiv σ_evm σ_solm) :
    runtimeEquivalenceFor config contract cA gh bl σ_evm σ_solm σ₀ g A I := by
  let locals := fileDsrLocals I
  let evm0 := initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I
  have hauthSolm : relyAuthWord σ_solm I = ⟨1⟩ := by
    have hword : relyAuthWord σ_evm I = relyAuthWord σ_solm I :=
      accountMapEquiv_storage_findD hAccounts I.codeOwner (relyAuthStorageSlot I) ⟨0⟩
    rw [← hword]; exact hauth
  have hliveSolm : potSlotWord ⟨8⟩ σ_solm I = ⟨1⟩ := by
    have hword : potSlotWord ⟨8⟩ σ_evm I = potSlotWord ⟨8⟩ σ_solm I :=
      accountMapEquiv_storage_findD hAccounts I.codeOwner ⟨8⟩ ⟨0⟩
    rw [← hword]; exact hlive
  have htimeSolm : potSlotWord ⟨7⟩ σ_solm I = UInt256.ofNat I.header.timestamp := by
    have hword : potSlotWord ⟨7⟩ σ_evm I = potSlotWord ⟨7⟩ σ_solm I :=
      accountMapEquiv_storage_findD hAccounts I.codeOwner ⟨7⟩ ⟨0⟩
    rw [← hword]; exact htime
  have hbody :
      ExecTransitionBody config contract evm0 locals fileDsrTransition.body .reverted := by
    simpa [evm0, locals] using
      (potFileDsrSourceBodyUnrecognized (cA := cA) (gh := gh) (bl := bl) (σ := σ_solm)
        (σ₀ := σ₀) (A := A) (I := I) (g := g) hwv hauthSolm hliveSolm htimeSolm hwhat)
  obtain ⟨_, _, hdecoded⟩ := potFileDsrX_decoded (g := Sat256.ofUInt256 g) hsz68 hsize hreach
  obtain ⟨_, _, hauthd⟩ := potFileDsrX_authorized (I := I) hauth hdecoded
  obtain ⟨_, _, hlived⟩ := potFileDsrX_liveOK (I := I) hlive hauthd
  obtain ⟨_, _, hrhod⟩ := potFileDsrX_rhoOK (I := I) htime hlived
  have hneq : calldataWord I.calldata 4 ≠ ABI.bytesToWord fileDsrBytes :=
    fileDsrWhatWord_ne_of_bytes_ne (by omega) hwhat (by native_decide)
  exact (potFileDsrX_unrecognized (I := I) hneq hrhod)
    |>.reEquivExecutionRevert hcode hdispatch hdecode hbody

theorem potFileDsrBodyCoreDecodeFailed_short
    {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256} {sel : UInt256}
    (hcode : I.code = potBytecode) (hsize : I.calldata.size < UInt256.size)
    (hsz4 : 4 ≤ I.calldata.size) (hshort : I.calldata.size < 68)
    (hdispatch : dispatchMsg contract I.calldata = some fileDsrTransition)
    (hreach : ∃ k C, RD potBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) ⟨367⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ_evm) k C) :
    runtimeEquivalenceFor config contract cA gh bl σ_evm σ_solm σ₀ g A I := by
  exact (potFileDsrX_shortarg (g := Sat256.ofUInt256 g) hsz4 hsize hshort hreach)
    |>.reEquivDecodingFailed hcode hdispatch (potDecode_fileDsr_none_short hsz4 hshort)

/-- `file(bytes32,uint256)` external (auth): sets `dsr` when `what == "dsr"`. -/
theorem potFileDsrBody {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256}
    (hcode : I.code = potBytecode)
    (hsize : I.calldata.size < UInt256.size)
    (_hperm : I.perm = true)
    (hwv : I.weiValue = ⟨0⟩)
    (hsel : selIs I (potSelBytes 7))
    (hAccounts : accountMapEquiv σ_evm σ_solm) :
    runtimeEquivalenceFor config contract cA gh bl σ_evm σ_solm σ₀ g A I := by
  have hsz4 : 4 ≤ I.calldata.size :=
    calldata_size_ge_of_selIs I (potSelBytes 7) rfl hsel
  have hdispatch : dispatchMsg contract I.calldata = some fileDsrTransition :=
    potDispatchFileDsr hsel
  have hreach := potReachFileDsrBody (cA := cA) (gh := gh) (bl := bl)
    (σ := σ_evm) (σ₀ := σ₀) (A := A) (I := I) (g := Sat256.ofUInt256 g)
    hcode hwv hsz4 hsize hsel
  by_cases hsz68 : 68 ≤ I.calldata.size
  · by_cases hauth : relyAuthWord σ_evm I = ⟨1⟩
    · by_cases hlive : potSlotWord ⟨8⟩ σ_evm I = ⟨1⟩
      · by_cases htime : UInt256.ofNat I.header.timestamp = potSlotWord ⟨7⟩ σ_evm I
        · by_cases hwhat : fileDsrWhat I = fileDsrBytes
          · exact potFileDsrBodyCoreOk hcode hsize _hperm hwv hsz68 hauth hlive htime.symm hwhat
              hdispatch (potDecode_fileDsr_ok hsz68) hreach hAccounts
          · exact potFileDsrBodyCoreUnrecognized hcode hsize hwv hsz68 hauth hlive htime.symm
              hwhat hdispatch (potDecode_fileDsr_ok hsz68) hreach hAccounts
        · exact potFileDsrBodyCoreRhoRevert hcode hsize hwv hsz68 hauth hlive htime
            hdispatch (potDecode_fileDsr_ok hsz68) hreach hAccounts
      · exact potFileDsrBodyCoreLiveRevert hcode hsize hwv hsz68 hauth hlive
          hdispatch (potDecode_fileDsr_ok hsz68) hreach hAccounts
    · exact potFileDsrBodyCoreUnauthorized hcode hsize hwv hsz68 hauth
        hdispatch (potDecode_fileDsr_ok hsz68) hreach hAccounts
  · exact potFileDsrBodyCoreDecodeFailed_short hcode hsize hsz4 (by omega)
      hdispatch hreach

end Benchmarks.Dss.Pot
