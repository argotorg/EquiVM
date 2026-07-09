import Benchmarks.EAS.Attester.MultiRevokeEVM
import Benchmarks.EAS.Attester.MultiSource

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Benchmarks.EAS.Attester.Immutables

namespace Benchmarks.EAS.Attester

def attesterBytes32ValueWord? : Value → Option UInt256
  | .fixedBytes n bytes =>
      if n = bytes32Width ∧ bytes.length = 32 then
        some (ABI.bytesToWord bytes)
      else
        none
  | _ => none

theorem attesterBytes32ValueWord?_of_toBytesBE (w : UInt256) :
    attesterBytes32ValueWord?
        (.fixedBytes bytes32Width (EVM.Word.toBytesBE w)) = some w := by
  have hlen : (EVM.Word.toBytesBE w).length = 32 := by
    simpa using word_toBytesBE_toByteArray_size w
  simp [attesterBytes32ValueWord?, hlen, bytesToWord_toBytesBE]

theorem attesterDecode_multiRevoke_schema_word (v : AttesterImmutables)
    {I : ExecutionEnv} {callargs : Store} {schemas : List Value}
    {idx : Nat} {schema : Value}
    (hdec : decodeCalldataWithMode (config v).abiDecodeMode
        ((multiRevokeTransition v).params.map Param.name)
        (transitionSignature (multiRevokeTransition v)).paramTypes I.calldata =
      some callargs)
    (hSchemas : callargs.get? "schemas" = some (.array schemas))
    (hlookup : lookupNth? schemas idx = some schema) :
    ∃ schemaWord,
      attesterBytes32ValueWord? schema = some schemaWord ∧
      schemaWord =
        calldataWord I.calldata
          (4 + ((calldataWord I.calldata 4).toNat + 32 + 32 * idx)) := by
  have hdec' :
      decodeCalldata ["schemas", "schemaUids"]
        [.dynamicArray bytes32, .dynamicArray (.dynamicArray bytes32)] I.calldata =
      some callargs := by
    simpa [decodeCalldataWithMode, config, multiRevokeTransition, transitionSignature,
      bytes32Array, bytes32NestedArray] using hdec
  obtain ⟨xs, endOffset, hfirst, hget⟩ :=
    attesterDecodeCalldata_twoDynamicArrays_first_decode
      (cd := I.calldata) (callargs := callargs)
      (name0 := "schemas") (name1 := "schemaUids") (elem1 := bytes32)
      (by decide) hdec'
  have hxs : xs = schemas := by
    cases Option.some.inj (hget.symm.trans hSchemas)
    rfl
  have hlookupXs : lookupNth? xs idx = some schema := by
    rw [hxs]
    exact hlookup
  obtain ⟨schemaWord, hshape⟩ :=
    decodeABIValue_dynamicArray_bytes32_lookup_shape
      (bytes := I.calldata.toList.drop 4) (start := (calldataWord I.calldata 4).toNat)
      (endOffset := endOffset) hfirst (lookupNth?_some_length hlookupXs)
  have hread :=
    decodeABIValue_dynamicArray_bytes32_lookup_readNat
      (bytes := I.calldata.toList.drop 4) (start := (calldataWord I.calldata 4).toNat)
      (endOffset := endOffset) hfirst hshape
  have hwordNat :
      schemaWord.toNat =
        (calldataWord I.calldata
          (4 + ((calldataWord I.calldata 4).toNat + 32 + 32 * idx))).toNat :=
    readNat_drop4_at_some_eq_calldataWord (cd := I.calldata) hread
  refine ⟨schemaWord, ?_, ?_⟩
  · rw [hlookupXs] at hshape
    cases hshape
    exact attesterBytes32ValueWord?_of_toBytesBE schemaWord
  · exact u256_inj hwordNat

theorem attesterDecode_multiRevoke_schema_word_at_payload (v : AttesterImmutables)
    {I : ExecutionEnv} {callargs : Store} {schemas : List Value}
    {idx : Nat} {schema : Value}
    (hdec : decodeCalldataWithMode (config v).abiDecodeMode
        ((multiRevokeTransition v).params.map Param.name)
        (transitionSignature (multiRevokeTransition v)).paramTypes I.calldata =
      some callargs)
    (hSchemas : callargs.get? "schemas" = some (.array schemas))
    (hlookup : lookupNth? schemas idx = some schema)
    (hoffMax : ¬ solcMaxU64 < (calldataWord I.calldata 4).toNat)
    (hidxMax : idx ≤ solcMaxU64) :
    ∃ schemaWord,
      attesterBytes32ValueWord? schema = some schemaWord ∧
      schemaWord =
        calldataWord I.calldata
          (attesterMultiRevokePostCopySchemaCalldataOffset
            ((UInt256.add ⟨4⟩ (calldataWord I.calldata 4)) + ⟨32⟩)
            (UInt256.ofNat idx)).toNat := by
  obtain ⟨schemaWord, hschemaWord, hschemaEq⟩ :=
    attesterDecode_multiRevoke_schema_word
      (v := v) (I := I) (callargs := callargs) (schemas := schemas)
      (idx := idx) (schema := schema) hdec hSchemas hlookup
  have hoffLe : (calldataWord I.calldata 4).toNat ≤ solcMaxU64 :=
    Nat.le_of_not_gt hoffMax
  have hidxSize : idx < UInt256.size := by
    norm_num [solcMaxU64, UInt256.size] at hidxMax ⊢
    omega
  have hidxWordToNat : (UInt256.ofNat idx).toNat = idx :=
    ulit_toNat' idx hidxSize
  have hbase4ToNat :
      (UInt256.add ⟨4⟩ (calldataWord I.calldata 4)).toNat =
        4 + (calldataWord I.calldata 4).toNat := by
    change (((⟨4⟩ : UInt256) + calldataWord I.calldata 4).toNat =
      4 + (calldataWord I.calldata 4).toNat)
    rw [uadd_toNat]
    rw [show (⟨4⟩ : UInt256).toNat = 4 by decide]
    exact Nat.mod_eq_of_lt (by
      norm_num [solcMaxU64, UInt256.size] at hoffLe ⊢
      omega)
  have hpayloadToNat :
      (((UInt256.add ⟨4⟩ (calldataWord I.calldata 4)) + ⟨32⟩ : UInt256)).toNat =
        4 + (calldataWord I.calldata 4).toNat + 32 := by
    rw [uadd_toNat, hbase4ToNat]
    rw [show (⟨32⟩ : UInt256).toNat = 32 by decide]
    exact Nat.mod_eq_of_lt (by
      norm_num [solcMaxU64, UInt256.size] at hoffLe ⊢
      omega)
  have hmulToNat :
      (UInt256.mul (⟨32⟩ : UInt256) (UInt256.ofNat idx)).toNat = 32 * idx := by
    rw [u256_mul_toNat]
    rw [show (⟨32⟩ : UInt256).toNat = 32 by decide, hidxWordToNat]
    exact Nat.mod_eq_of_lt (by
      norm_num [solcMaxU64, UInt256.size] at hidxMax ⊢
      omega)
  have hoffToNat :
      (attesterMultiRevokePostCopySchemaCalldataOffset
          ((UInt256.add ⟨4⟩ (calldataWord I.calldata 4)) + ⟨32⟩)
          (UInt256.ofNat idx)).toNat =
        4 + (calldataWord I.calldata 4).toNat + 32 + 32 * idx := by
    unfold attesterMultiRevokePostCopySchemaCalldataOffset
    rw [uadd_toNat, hmulToNat, hpayloadToNat]
    rw [show 32 * idx + (4 + (calldataWord I.calldata 4).toNat + 32) =
        4 + (calldataWord I.calldata 4).toNat + 32 + 32 * idx by omega]
    exact Nat.mod_eq_of_lt (by
      norm_num [solcMaxU64, UInt256.size] at hoffLe hidxMax ⊢
      omega)
  refine ⟨schemaWord, hschemaWord, ?_⟩
  rw [hschemaEq, hoffToNat]
  rw [show
    4 + ((calldataWord I.calldata 4).toNat + 32 + 32 * idx) =
      4 + (calldataWord I.calldata 4).toNat + 32 + 32 * idx by omega]

theorem attesterMultiRevokeInnerArrayCopyCalldataOffset_toNat
    {payload : UInt256} {j : Nat}
    (hj : j < UInt256.size)
    (hbound : payload.toNat + 32 * j < UInt256.size) :
    (attesterMultiRevokeInnerArrayCopyCalldataOffset payload (UInt256.ofNat j)).toNat =
      payload.toNat + 32 * j := by
  unfold attesterMultiRevokeInnerArrayCopyCalldataOffset
  have hjToNat : (UInt256.ofNat j).toNat = j :=
    ulit_toNat' j hj
  have hmul :
      (UInt256.mul (⟨32⟩ : UInt256) (UInt256.ofNat j)).toNat = 32 * j := by
    rw [u256_mul_toNat]
    rw [show (⟨32⟩ : UInt256).toNat = 32 by decide, hjToNat]
    exact Nat.mod_eq_of_lt (by omega)
  rw [uadd_toNat, hmul]
  rw [show 32 * j + payload.toNat = payload.toNat + 32 * j by omega]
  exact Nat.mod_eq_of_lt hbound

theorem attesterDecode_multiRevoke_uid_word (v : AttesterImmutables)
    {I : ExecutionEnv} {callargs : Store} {schemaUids uids : List Value}
    {idx j : Nat} {uid : Value}
    (hdec : decodeCalldataWithMode (config v).abiDecodeMode
        ((multiRevokeTransition v).params.map Param.name)
        (transitionSignature (multiRevokeTransition v)).paramTypes I.calldata =
      some callargs)
    (hSchemaUids : callargs.get? "schemaUids" = some (.array schemaUids))
    (hlookupOuter : lookupNth? schemaUids idx = some (.array uids))
    (hlookupUid : lookupNth? uids j = some uid) :
    ∃ relativeOffset uidWord,
      attesterBytes32ValueWord? uid = some uidWord ∧
      uidWord =
        calldataWord I.calldata
          (4 + ((calldataWord I.calldata 36).toNat + 32 + relativeOffset + 32 +
            32 * j)) := by
  obtain ⟨_len, relativeOffset, innerEnd, _hlen, _hlenMax, _hidx, _hread,
      hinner⟩ :=
    attesterDecode_multiRevoke_inner_decode_at
      (v := v) (I := I) (callargs := callargs) (schemaUids := schemaUids)
      (inner := uids) (idx := idx) hdec hSchemaUids hlookupOuter
  obtain ⟨uidWord, hshape⟩ :=
    decodeABIValue_dynamicArray_bytes32_lookup_shape
      (bytes := I.calldata.toList.drop 4)
      (start := (calldataWord I.calldata 36).toNat + 32 + relativeOffset)
      (endOffset := innerEnd) hinner (lookupNth?_some_length hlookupUid)
  have hreadUid :=
    decodeABIValue_dynamicArray_bytes32_lookup_readNat
      (bytes := I.calldata.toList.drop 4)
      (start := (calldataWord I.calldata 36).toNat + 32 + relativeOffset)
      (endOffset := innerEnd) hinner hshape
  have hwordNat :
      uidWord.toNat =
        (calldataWord I.calldata
          (4 + ((calldataWord I.calldata 36).toNat + 32 + relativeOffset + 32 +
            32 * j))).toNat := by
    simpa [Nat.add_assoc] using
      (readNat_drop4_at_some_eq_calldataWord (cd := I.calldata) hreadUid)
  refine ⟨relativeOffset, uidWord, ?_, ?_⟩
  · rw [hlookupUid] at hshape
    cases hshape
    exact attesterBytes32ValueWord?_of_toBytesBE uidWord
  · exact u256_inj hwordNat

theorem attesterDecode_multiRevoke_uid_word_at_payload (v : AttesterImmutables)
    {I : ExecutionEnv} {callargs : Store} {schemaUids uids : List Value}
    {idx j : Nat} {uid : Value}
    (hdec : decodeCalldataWithMode (config v).abiDecodeMode
        ((multiRevokeTransition v).params.map Param.name)
        (transitionSignature (multiRevokeTransition v)).paramTypes I.calldata =
      some callargs)
    (hSchemaUids : callargs.get? "schemaUids" = some (.array schemaUids))
    (hlookupOuter : lookupNth? schemaUids idx = some (.array uids))
    (hlookupUid : lookupNth? uids j = some uid)
    (hoffMax : ¬ solcMaxU64 < (calldataWord I.calldata 36).toNat)
    (hsizeSigned : I.calldata.size < 2 ^ 255) :
    ∃ uidWord,
      attesterBytes32ValueWord? uid = some uidWord ∧
      uidWord =
        calldataWord I.calldata
          ((attesterMultiRevokeInnerArrayPayloadWord I
              (attesterSecondArrayPayloadStartWord I)
              (attesterMultiRevokeInnerArrayHeadWord
                (attesterSecondArrayPayloadStartWord I) (UInt256.ofNat idx))).toNat +
            32 * j) := by
  obtain ⟨len, relativeOffset, innerEnd, hlenRead, hlenMax, hidx, hreadAt,
      hinner⟩ :=
    attesterDecode_multiRevoke_inner_decode_at
      (v := v) (I := I) (callargs := callargs) (schemaUids := schemaUids)
      (inner := uids) (idx := idx) hdec hSchemaUids hlookupOuter
  obtain ⟨uidWord, hshape⟩ :=
    decodeABIValue_dynamicArray_bytes32_lookup_shape
      (bytes := I.calldata.toList.drop 4)
      (start := (calldataWord I.calldata 36).toNat + 32 + relativeOffset)
      (endOffset := innerEnd) hinner (lookupNth?_some_length hlookupUid)
  have hreadUid :=
    decodeABIValue_dynamicArray_bytes32_lookup_readNat
      (bytes := I.calldata.toList.drop 4)
      (start := (calldataWord I.calldata 36).toNat + 32 + relativeOffset)
      (endOffset := innerEnd) hinner hshape
  have hsize : I.calldata.size < UInt256.size := lt_size_of_lt_sign hsizeSigned
  have hdropLen : (I.calldata.toList.drop 4).length = I.calldata.size - 4 := by
    rw [List.length_drop]
    have htlen : I.calldata.toList.length = I.calldata.size := by
      rw [byteArray_toList_eq, Array.length_toList]
      rfl
    rw [htlen]
  have hreadUidSize := readNat?_some_length hreadUid
  have hlenLeU64 : len ≤ solcMaxU64 :=
    Nat.le_of_not_gt (by simpa [solcMaxLen] using hlenMax)
  have hidxSize : idx < UInt256.size := by
    norm_num [solcMaxU64, UInt256.size] at hlenLeU64 ⊢
    omega
  have hidxWordToNat : (UInt256.ofNat idx).toNat = idx :=
    ulit_toNat' idx hidxSize
  have hoffLe : (calldataWord I.calldata 36).toNat ≤ solcMaxU64 :=
    Nat.le_of_not_gt hoffMax
  have hbaseToNat :
      (attesterSecondArrayPayloadStartWord I).toNat =
        4 + (calldataWord I.calldata 36).toNat + 32 :=
    attesterSecondArrayPayloadStart_toNat (I := I) hoffMax
  have hmulToNat :
      (UInt256.mul (⟨32⟩ : UInt256) (UInt256.ofNat idx)).toNat =
        32 * idx := by
    rw [u256_mul_toNat]
    rw [show (⟨32⟩ : UInt256).toNat = 32 by decide, hidxWordToNat]
    exact Nat.mod_eq_of_lt (by
      norm_num [solcMaxU64, UInt256.size] at hlenLeU64 ⊢
      omega)
  have hheadToNat :
      (attesterMultiRevokeInnerArrayHeadWord
          (attesterSecondArrayPayloadStartWord I) (UInt256.ofNat idx)).toNat =
        4 + (calldataWord I.calldata 36).toNat + 32 + 32 * idx := by
    unfold attesterMultiRevokeInnerArrayHeadWord
    rw [uadd_toNat, hbaseToNat, hmulToNat]
    exact Nat.mod_eq_of_lt (by
      norm_num [solcMaxU64, UInt256.size] at hoffLe hlenLeU64 ⊢
      omega)
  have hoffWordToNat :
      (attesterMultiRevokeInnerArrayOffsetWord I
          (attesterMultiRevokeInnerArrayHeadWord
            (attesterSecondArrayPayloadStartWord I) (UInt256.ofNat idx))).toNat =
        relativeOffset := by
    unfold attesterMultiRevokeInnerArrayOffsetWord
    rw [hheadToNat]
    have hreadEq :=
      readNat_drop4_at_some_eq_calldataWord (cd := I.calldata) hreadAt
    simpa [Nat.add_assoc] using hreadEq.symm
  have hstartToNat :
      (attesterMultiRevokeInnerArrayStartWord I
          (attesterSecondArrayPayloadStartWord I)
          (attesterMultiRevokeInnerArrayHeadWord
            (attesterSecondArrayPayloadStartWord I) (UInt256.ofNat idx))).toNat =
        4 + (calldataWord I.calldata 36).toNat + 32 + relativeOffset := by
    unfold attesterMultiRevokeInnerArrayStartWord
    rw [uadd_toNat, hbaseToNat, hoffWordToNat]
    exact Nat.mod_eq_of_lt (by
      rw [hdropLen] at hreadUidSize
      omega)
  have hpayloadToNat :
      (attesterMultiRevokeInnerArrayPayloadWord I
          (attesterSecondArrayPayloadStartWord I)
          (attesterMultiRevokeInnerArrayHeadWord
            (attesterSecondArrayPayloadStartWord I) (UInt256.ofNat idx))).toNat =
        4 + (calldataWord I.calldata 36).toNat + 32 + relativeOffset + 32 := by
    unfold attesterMultiRevokeInnerArrayPayloadWord
    rw [uadd_toNat, hstartToNat]
    rw [show (⟨32⟩ : UInt256).toNat = 32 from by decide]
    exact Nat.mod_eq_of_lt (by
      rw [hdropLen] at hreadUidSize
      omega)
  have hwordNat :
      uidWord.toNat =
        (calldataWord I.calldata
          ((attesterMultiRevokeInnerArrayPayloadWord I
              (attesterSecondArrayPayloadStartWord I)
              (attesterMultiRevokeInnerArrayHeadWord
                (attesterSecondArrayPayloadStartWord I) (UInt256.ofNat idx))).toNat +
            32 * j)).toNat := by
    rw [hpayloadToNat]
    simpa [Nat.add_assoc] using
      (readNat_drop4_at_some_eq_calldataWord (cd := I.calldata) hreadUid)
  refine ⟨uidWord, ?_, ?_⟩
  · rw [hlookupUid] at hshape
    cases hshape
    exact attesterBytes32ValueWord?_of_toBytesBE uidWord
  · exact u256_inj hwordNat

theorem attesterDecode_multiRevoke_uid_word_at_copy_payload (v : AttesterImmutables)
    {I : ExecutionEnv} {callargs : Store} {schemaUids uids : List Value}
    {idx j : Nat} {uid : Value}
    (hdec : decodeCalldataWithMode (config v).abiDecodeMode
        ((multiRevokeTransition v).params.map Param.name)
        (transitionSignature (multiRevokeTransition v)).paramTypes I.calldata =
      some callargs)
    (hSchemaUids : callargs.get? "schemaUids" = some (.array schemaUids))
    (hlookupOuter : lookupNth? schemaUids idx = some (.array uids))
    (hlookupUid : lookupNth? uids j = some uid)
    (hoffMax : ¬ solcMaxU64 < (calldataWord I.calldata 36).toNat)
    (hsizeSigned : I.calldata.size < 2 ^ 255) :
    ∃ uidWord,
      attesterBytes32ValueWord? uid = some uidWord ∧
      uidWord =
        calldataWord I.calldata
          (attesterMultiRevokeInnerArrayCopyCalldataOffset
            (attesterMultiRevokeInnerArrayPayloadWord I
              (attesterSecondArrayPayloadStartWord I)
              (attesterMultiRevokeInnerArrayHeadWord
                (attesterSecondArrayPayloadStartWord I) (UInt256.ofNat idx)))
            (UInt256.ofNat j)).toNat := by
  obtain ⟨uidWord, huidWord, huidPayloadEq⟩ :=
    attesterDecode_multiRevoke_uid_word_at_payload
      (v := v) (I := I) (callargs := callargs) (schemaUids := schemaUids)
      (uids := uids) (idx := idx) (j := j) (uid := uid)
      hdec hSchemaUids hlookupOuter hlookupUid hoffMax hsizeSigned
  obtain ⟨len, relativeOffset, innerEnd, hlenRead, hlenMax, hidx, hreadAt,
      hinner⟩ :=
    attesterDecode_multiRevoke_inner_decode_at
      (v := v) (I := I) (callargs := callargs) (schemaUids := schemaUids)
      (inner := uids) (idx := idx) hdec hSchemaUids hlookupOuter
  obtain ⟨uidWord', hshape⟩ :=
    decodeABIValue_dynamicArray_bytes32_lookup_shape
      (bytes := I.calldata.toList.drop 4)
      (start := (calldataWord I.calldata 36).toNat + 32 + relativeOffset)
      (endOffset := innerEnd) hinner (lookupNth?_some_length hlookupUid)
  have hreadUid :=
    decodeABIValue_dynamicArray_bytes32_lookup_readNat
      (bytes := I.calldata.toList.drop 4)
      (start := (calldataWord I.calldata 36).toNat + 32 + relativeOffset)
      (endOffset := innerEnd) hinner hshape
  have hsize : I.calldata.size < UInt256.size := lt_size_of_lt_sign hsizeSigned
  have hdropLen : (I.calldata.toList.drop 4).length = I.calldata.size - 4 := by
    rw [List.length_drop]
    have htlen : I.calldata.toList.length = I.calldata.size := by
      rw [byteArray_toList_eq, Array.length_toList]
      rfl
    rw [htlen]
  have hreadUidSize := readNat?_some_length hreadUid
  have hoffLe : (calldataWord I.calldata 36).toNat ≤ solcMaxU64 :=
    Nat.le_of_not_gt hoffMax
  have hlenLeU64 : len ≤ solcMaxU64 :=
    Nat.le_of_not_gt (by simpa [solcMaxLen] using hlenMax)
  have hidxSize : idx < UInt256.size := by
    norm_num [solcMaxU64, UInt256.size] at hlenLeU64 ⊢
    omega
  have hidxWordToNat : (UInt256.ofNat idx).toNat = idx :=
    ulit_toNat' idx hidxSize
  have hbaseToNat :
      (attesterSecondArrayPayloadStartWord I).toNat =
        4 + (calldataWord I.calldata 36).toNat + 32 :=
    attesterSecondArrayPayloadStart_toNat (I := I) hoffMax
  have hmulToNat :
      (UInt256.mul (⟨32⟩ : UInt256) (UInt256.ofNat idx)).toNat =
        32 * idx := by
    rw [u256_mul_toNat]
    rw [show (⟨32⟩ : UInt256).toNat = 32 by decide, hidxWordToNat]
    exact Nat.mod_eq_of_lt (by
      norm_num [solcMaxU64, UInt256.size] at hlenLeU64 ⊢
      omega)
  have hheadToNat :
      (attesterMultiRevokeInnerArrayHeadWord
          (attesterSecondArrayPayloadStartWord I) (UInt256.ofNat idx)).toNat =
        4 + (calldataWord I.calldata 36).toNat + 32 + 32 * idx := by
    unfold attesterMultiRevokeInnerArrayHeadWord
    rw [uadd_toNat, hbaseToNat, hmulToNat]
    exact Nat.mod_eq_of_lt (by
      norm_num [solcMaxU64, UInt256.size] at hoffLe hlenLeU64 ⊢
      omega)
  have hoffWordToNat :
      (attesterMultiRevokeInnerArrayOffsetWord I
          (attesterMultiRevokeInnerArrayHeadWord
            (attesterSecondArrayPayloadStartWord I) (UInt256.ofNat idx))).toNat =
        relativeOffset := by
    unfold attesterMultiRevokeInnerArrayOffsetWord
    rw [hheadToNat]
    have hreadEq :=
      readNat_drop4_at_some_eq_calldataWord (cd := I.calldata) hreadAt
    simpa [Nat.add_assoc] using hreadEq.symm
  have hstartToNat :
      (attesterMultiRevokeInnerArrayStartWord I
          (attesterSecondArrayPayloadStartWord I)
          (attesterMultiRevokeInnerArrayHeadWord
            (attesterSecondArrayPayloadStartWord I) (UInt256.ofNat idx))).toNat =
        4 + (calldataWord I.calldata 36).toNat + 32 + relativeOffset := by
    unfold attesterMultiRevokeInnerArrayStartWord
    rw [uadd_toNat, hbaseToNat, hoffWordToNat]
    exact Nat.mod_eq_of_lt (by
      rw [hdropLen] at hreadUidSize
      omega)
  have hpayloadToNat :
      (attesterMultiRevokeInnerArrayPayloadWord I
          (attesterSecondArrayPayloadStartWord I)
          (attesterMultiRevokeInnerArrayHeadWord
            (attesterSecondArrayPayloadStartWord I) (UInt256.ofNat idx))).toNat =
        4 + (calldataWord I.calldata 36).toNat + 32 + relativeOffset + 32 := by
    unfold attesterMultiRevokeInnerArrayPayloadWord
    rw [uadd_toNat, hstartToNat]
    rw [show (⟨32⟩ : UInt256).toNat = 32 from by decide]
    exact Nat.mod_eq_of_lt (by
      rw [hdropLen] at hreadUidSize
      omega)
  have hpayloadElemBound :
      (attesterMultiRevokeInnerArrayPayloadWord I
          (attesterSecondArrayPayloadStartWord I)
          (attesterMultiRevokeInnerArrayHeadWord
            (attesterSecondArrayPayloadStartWord I) (UInt256.ofNat idx))).toNat +
        32 * j < UInt256.size := by
    rw [hpayloadToNat]
    rw [hdropLen] at hreadUidSize
    omega
  have hjSize : j < UInt256.size := by
    exact lt_of_le_of_lt (by
      show j ≤
        (attesterMultiRevokeInnerArrayPayloadWord I
            (attesterSecondArrayPayloadStartWord I)
            (attesterMultiRevokeInnerArrayHeadWord
              (attesterSecondArrayPayloadStartWord I) (UInt256.ofNat idx))).toNat +
          32 * j
      omega) hpayloadElemBound
  have hcopyOffsetToNat :
      (attesterMultiRevokeInnerArrayCopyCalldataOffset
          (attesterMultiRevokeInnerArrayPayloadWord I
            (attesterSecondArrayPayloadStartWord I)
            (attesterMultiRevokeInnerArrayHeadWord
              (attesterSecondArrayPayloadStartWord I) (UInt256.ofNat idx)))
          (UInt256.ofNat j)).toNat =
        (attesterMultiRevokeInnerArrayPayloadWord I
            (attesterSecondArrayPayloadStartWord I)
            (attesterMultiRevokeInnerArrayHeadWord
              (attesterSecondArrayPayloadStartWord I) (UInt256.ofNat idx))).toNat +
          32 * j :=
    attesterMultiRevokeInnerArrayCopyCalldataOffset_toNat
      (payload :=
        attesterMultiRevokeInnerArrayPayloadWord I
          (attesterSecondArrayPayloadStartWord I)
          (attesterMultiRevokeInnerArrayHeadWord
            (attesterSecondArrayPayloadStartWord I) (UInt256.ofNat idx)))
      (j := j) hjSize hpayloadElemBound
  refine ⟨uidWord, huidWord, ?_⟩
  rw [huidPayloadEq, hcopyOffsetToNat]

def attesterMultiRevokeRequestPtr
    (mem : ByteArray) (aw outerBase : UInt256) (idx : Nat) : UInt256 :=
  attesterMloadWord mem aw
    (attesterMultiRevokePostCopyOuterSlotWord outerBase (UInt256.ofNat idx))

def attesterMultiRevokeRequestDataPtr
    (mem : ByteArray) (aw outerBase : UInt256) (idx : Nat) : UInt256 :=
  attesterMloadWord mem aw
    ((⟨32⟩ : UInt256) + attesterMultiRevokeRequestPtr mem aw outerBase idx)

def attesterMultiRevokeRequestDataElemPtr
    (mem : ByteArray) (aw outerBase : UInt256) (idx j : Nat) : UInt256 :=
  attesterMloadWord mem aw
    ((⟨32⟩ : UInt256) +
      UInt256.mul (⟨32⟩ : UInt256) (UInt256.ofNat j) +
      attesterMultiRevokeRequestDataPtr mem aw outerBase idx)

def attesterMultiRevokeInnerCopyTuplePtrNat
    (base len : UInt256) (j : Nat) : Nat :=
  base.toNat + 32 + 96 * len.toNat + 64 * j

def attesterMultiRevokeInnerCopyTuplePtr
    (base len : UInt256) (j : Nat) : UInt256 :=
  UInt256.ofNat (attesterMultiRevokeInnerCopyTuplePtrNat base len j)

theorem attesterMultiRevokeInnerCopyTuplePtr_toNat
    {base len : UInt256} {j : Nat}
    (hbound : attesterMultiRevokeInnerCopyTuplePtrNat base len j < UInt256.size) :
    (attesterMultiRevokeInnerCopyTuplePtr base len j).toNat =
      attesterMultiRevokeInnerCopyTuplePtrNat base len j := by
  exact ulit_toNat' (attesterMultiRevokeInnerCopyTuplePtrNat base len j) hbound

theorem attesterMultiRevokeInnerCopyTuplePtr_add32_toNat
    {base len : UInt256} {j : Nat}
    (hbound : attesterMultiRevokeInnerCopyTuplePtrNat base len j + 32 < UInt256.size) :
    ((⟨32⟩ : UInt256) + attesterMultiRevokeInnerCopyTuplePtr base len j).toNat =
      attesterMultiRevokeInnerCopyTuplePtrNat base len j + 32 := by
  have hptrBound : attesterMultiRevokeInnerCopyTuplePtrNat base len j < UInt256.size := by
    omega
  rw [uadd_toNat]
  rw [attesterMultiRevokeInnerCopyTuplePtr_toNat hptrBound]
  rw [show (⟨32⟩ : UInt256).toNat = 32 by decide]
  rw [show 32 + attesterMultiRevokeInnerCopyTuplePtrNat base len j =
      attesterMultiRevokeInnerCopyTuplePtrNat base len j + 32 by omega]
  exact Nat.mod_eq_of_lt hbound

def AttesterMultiRevokeInnerCopyReadLayout
    (I : ExecutionEnv) (base len payload : UInt256) (copied : Nat)
    (mem : ByteArray) : Prop :=
  ∀ {j : Nat}, j < copied →
    let slot := attesterMultiRevokeInnerArrayCopySlotWord base (UInt256.ofNat j)
    let ptr := attesterMultiRevokeInnerCopyTuplePtr base len j
    slot.toNat + 32 ≤ mem.size ∧
    ptr.toNat + 32 ≤ mem.size ∧
    ((⟨32⟩ : UInt256) + ptr).toNat + 32 ≤ mem.size ∧
    mem.readWithPadding slot.toNat 32 = UInt256.toByteArray ptr ∧
    mem.readWithPadding ptr.toNat 32 =
      UInt256.toByteArray
        (calldataWord I.calldata
          (attesterMultiRevokeInnerArrayCopyCalldataOffset payload
            (UInt256.ofNat j)).toNat) ∧
    mem.readWithPadding ((⟨32⟩ : UInt256) + ptr).toNat 32 =
      UInt256.toByteArray (⟨0⟩ : UInt256)

theorem AttesterMultiRevokeInnerCopyReadLayout_zero
    (I : ExecutionEnv) (base len payload : UInt256) (mem : ByteArray) :
    AttesterMultiRevokeInnerCopyReadLayout I base len payload 0 mem := by
  intro j hlt
  omega

theorem AttesterMultiRevokeInnerCopyReadLayout_mono
    {I : ExecutionEnv} {base len payload : UInt256} {i j : Nat}
    {mem : ByteArray}
    (hle : i ≤ j)
    (h : AttesterMultiRevokeInnerCopyReadLayout I base len payload j mem) :
    AttesterMultiRevokeInnerCopyReadLayout I base len payload i mem := by
  intro idx hidx
  exact h (by omega)

set_option maxHeartbeats 1000000 in
theorem AttesterMultiRevokeInnerCopyReadLayout_step
    {I : ExecutionEnv} {base len payload idx : UInt256}
    {mem : ByteArray} {aw : UInt256} {n : Nat}
    (hidx : idx = UInt256.ofNat (len.toNat - (n + 1)))
    (hle : n + 1 ≤ len.toNat)
    (hbaseGe : 64 + 32 ≤ base.toNat)
    (hbaseSlot63 : base.toNat + 32 + 32 * len.toNat + 63 < UInt256.size)
    (hfreeExact :
      (attesterMultiRevokeInnerArrayCopyFreeWord mem aw).toNat =
        base.toNat + 32 + 96 * len.toNat + 64 * (len.toNat - (n + 1)))
    (hfreeSpare :
      (attesterMultiRevokeInnerArrayCopyFreeWord mem aw).toNat +
        64 * (n + 1) + 96 < UInt256.size)
    (hLayout :
      AttesterMultiRevokeInnerCopyReadLayout I base len payload
        (len.toNat - (n + 1)) mem) :
    AttesterMultiRevokeInnerCopyReadLayout I base len payload
      (len.toNat - n)
      (attesterMultiRevokeInnerArrayCopyStepMem I base payload idx mem aw) := by
  classical
  let oldCopied := len.toNat - (n + 1)
  let free := attesterMultiRevokeInnerArrayCopyFreeWord mem aw
  let zero := attesterMultiRevokeInnerArrayCopyZeroWord mem aw
  let curSlot := attesterMultiRevokeInnerArrayCopySlotWord base idx
  have hidxToNat : idx.toNat = oldCopied := by
    rw [hidx]
    exact ulit_toNat' oldCopied (by
      unfold oldCopied
      exact lt_of_le_of_lt (Nat.sub_le _ _) len.val.isLt)
  have hcurSlotToNat :
      curSlot.toNat = base.toNat + 32 + 32 * oldCopied := by
    unfold curSlot
    rw [attesterMultiRevokeInnerArrayCopySlotWord_toNat]
    · rw [hidxToNat]
    · rw [hidxToNat]
      unfold oldCopied
      have hmul : 32 * (len.toNat - (n + 1)) ≤ 32 * len.toNat :=
        Nat.mul_le_mul_left 32 (Nat.sub_le _ _)
      omega
  have hfree32 : free.toNat + 32 < UInt256.size := by
    change (attesterMultiRevokeInnerArrayCopyFreeWord mem aw).toNat + 32 <
      UInt256.size
    omega
  have hzeroToNat : zero.toNat = free.toNat + 32 := by
    unfold zero free
    exact attesterMultiRevokeInnerArrayCopyZeroWord_toNat hfree32
  have hnewCopied : len.toNat - n = oldCopied + 1 := by
    unfold oldCopied
    omega
  intro j hj
  by_cases hOld : j < oldCopied
  · have hOldLayout := hLayout (j := j) hOld
    dsimp only [AttesterMultiRevokeInnerCopyReadLayout] at hOldLayout
    let slot := attesterMultiRevokeInnerArrayCopySlotWord base (UInt256.ofNat j)
    let ptr := attesterMultiRevokeInnerCopyTuplePtr base len j
    have hjLtLen : j < len.toNat := by
      exact lt_of_lt_of_le hOld (by
        unfold oldCopied
        exact Nat.sub_le _ _)
    have hslotBound :
        base.toNat + 32 + 32 * j + 63 < UInt256.size := by
      have hjle : j ≤ len.toNat := le_of_lt hjLtLen
      have hmul : 32 * j ≤ 32 * len.toNat := Nat.mul_le_mul_left 32 hjle
      omega
    have hslotToNat : slot.toNat = base.toNat + 32 + 32 * j := by
      unfold slot
      rw [attesterMultiRevokeInnerArrayCopySlotWord_toNat]
      · rw [ulit_toNat' j (lt_trans hjLtLen len.val.isLt)]
      · rw [ulit_toNat' j (lt_trans hjLtLen len.val.isLt)]
        omega
    have hptrToNat :
        ptr.toNat = base.toNat + 32 + 96 * len.toNat + 64 * j := by
      unfold ptr
      exact attesterMultiRevokeInnerCopyTuplePtr_toNat (by
        unfold attesterMultiRevokeInnerCopyTuplePtrNat
        omega)
    have hptr32ToNat :
        ((⟨32⟩ : UInt256) + ptr).toNat =
          base.toNat + 32 + 96 * len.toNat + 64 * j + 32 := by
      rw [attesterMultiRevokeInnerCopyTuplePtr_add32_toNat]
      · unfold attesterMultiRevokeInnerCopyTuplePtrNat
        rfl
      · unfold attesterMultiRevokeInnerCopyTuplePtrNat
        omega
    rcases hOldLayout with
      ⟨hslotMem, hptrMem, hptr32Mem, hslotRead, hptrRead, hptr32Read⟩
    have hslotPreserve :
        (attesterMultiRevokeInnerArrayCopyStepMem I base payload idx mem aw).readWithPadding
            slot.toNat 32 =
          UInt256.toByteArray ptr := by
      exact attesterMultiRevokeInnerArrayCopyStep_readWithPadding_at_nat_disj
        (I := I) (readBase := slot) (base := base) (payload := payload)
        (idx := idx) (len := ptr) (mem := mem) (aw := aw)
        hslotMem hslotRead
        (by rw [hslotToNat]; omega)
        (by rw [hslotToNat, hfreeExact]; unfold oldCopied at hOld; omega)
        (by rw [hslotToNat, hzeroToNat, hfreeExact]; unfold oldCopied at hOld; omega)
        (by
          rw [hslotToNat, hcurSlotToNat]
          exact Or.inl (by unfold oldCopied at hOld; omega))
    have hptrPreserve :
        (attesterMultiRevokeInnerArrayCopyStepMem I base payload idx mem aw).readWithPadding
            ptr.toNat 32 =
          UInt256.toByteArray
            (calldataWord I.calldata
              (attesterMultiRevokeInnerArrayCopyCalldataOffset payload
                (UInt256.ofNat j)).toNat) := by
      exact attesterMultiRevokeInnerArrayCopyStep_readWithPadding_at_nat_disj
        (I := I) (readBase := ptr) (base := base) (payload := payload)
        (idx := idx)
        (len :=
          calldataWord I.calldata
            (attesterMultiRevokeInnerArrayCopyCalldataOffset payload
              (UInt256.ofNat j)).toNat)
        (mem := mem) (aw := aw)
        hptrMem hptrRead
        (by rw [hptrToNat]; omega)
        (by rw [hptrToNat, hfreeExact]; unfold oldCopied at hOld; omega)
        (by rw [hptrToNat, hzeroToNat, hfreeExact]; unfold oldCopied at hOld; omega)
        (by
          rw [hptrToNat, hcurSlotToNat]
          exact Or.inr (by unfold oldCopied at hOld; omega))
    have hptr32Preserve :
        (attesterMultiRevokeInnerArrayCopyStepMem I base payload idx mem aw).readWithPadding
            ((⟨32⟩ : UInt256) + ptr).toNat 32 =
          UInt256.toByteArray (⟨0⟩ : UInt256) := by
      exact attesterMultiRevokeInnerArrayCopyStep_readWithPadding_at_nat_disj
        (I := I) (readBase := ((⟨32⟩ : UInt256) + ptr))
        (base := base) (payload := payload) (idx := idx)
        (len := (⟨0⟩ : UInt256)) (mem := mem) (aw := aw)
        hptr32Mem hptr32Read
        (by rw [hptr32ToNat]; omega)
        (by rw [hptr32ToNat, hfreeExact]; unfold oldCopied at hOld; omega)
        (by rw [hptr32ToNat, hzeroToNat, hfreeExact]; unfold oldCopied at hOld; omega)
        (by
          rw [hptr32ToNat, hcurSlotToNat]
          exact Or.inr (by unfold oldCopied at hOld; omega))
    exact
      ⟨le_trans hslotMem attesterMultiRevokeInnerArrayCopyStep_size_ge,
        le_trans hptrMem attesterMultiRevokeInnerArrayCopyStep_size_ge,
        le_trans hptr32Mem attesterMultiRevokeInnerArrayCopyStep_size_ge,
        hslotPreserve, hptrPreserve, hptr32Preserve⟩
  · have hjEq : j = oldCopied := by
      rw [hnewCopied] at hj
      omega
    subst j
    let slot := attesterMultiRevokeInnerArrayCopySlotWord base (UInt256.ofNat oldCopied)
    let ptr := attesterMultiRevokeInnerCopyTuplePtr base len oldCopied
    have hslotEq : slot = curSlot := by
      unfold slot curSlot
      rw [hidx]
    have hptrToNat : ptr.toNat = free.toNat := by
      unfold ptr free
      rw [attesterMultiRevokeInnerCopyTuplePtr_toNat]
      · rw [hfreeExact]
        unfold attesterMultiRevokeInnerCopyTuplePtrNat oldCopied
        rfl
      · unfold attesterMultiRevokeInnerCopyTuplePtrNat oldCopied
        omega
    have hptrEq : ptr = free := by
      apply u256_inj
      exact hptrToNat
    have hptr32ToNat : ((⟨32⟩ : UInt256) + ptr).toNat = zero.toNat := by
      rw [attesterMultiRevokeInnerCopyTuplePtr_add32_toNat]
      · have hptrNat :
            attesterMultiRevokeInnerCopyTuplePtrNat base len oldCopied = free.toNat := by
          unfold attesterMultiRevokeInnerCopyTuplePtrNat oldCopied free
          rw [hfreeExact]
        rw [hptrNat, hzeroToNat]
      · unfold attesterMultiRevokeInnerCopyTuplePtrNat oldCopied
        omega
    have hslotBelowFree : curSlot.toNat + 32 ≤ free.toNat := by
      rw [hcurSlotToNat, hfreeExact]
      unfold oldCopied
      have hleOld : len.toNat - (n + 1) ≤ len.toNat := Nat.sub_le _ _
      have hmul : 32 * (len.toNat - (n + 1)) ≤ 96 * len.toNat := by
        have hmul32 : 32 * (len.toNat - (n + 1)) ≤ 32 * len.toNat :=
          Nat.mul_le_mul_left 32 hleOld
        nlinarith
      omega
    have hslotBelowZero : curSlot.toNat + 32 ≤ zero.toNat := by
      rw [hzeroToNat]
      omega
    have hstepSizeSlot :
        slot.toNat + 32 ≤
          (attesterMultiRevokeInnerArrayCopyStepMem I base payload idx mem aw).size := by
      rw [hslotEq]
      change curSlot.toNat + 32 ≤
        (Reasoning.Theory.writeWord
          (attesterMultiRevokeInnerArrayCopyZeroMem I payload idx mem aw)
          curSlot.toNat free).size
      rw [attesterWriteWord_size_nat]
      exact Nat.le_max_right _ _
    have hstepSizePtr :
        ptr.toNat + 32 ≤
          (attesterMultiRevokeInnerArrayCopyStepMem I base payload idx mem aw).size := by
      rw [hptrToNat]
      change free.toNat + 32 ≤
        (Reasoning.Theory.writeWord
          (attesterMultiRevokeInnerArrayCopyZeroMem I payload idx mem aw)
          curSlot.toNat free).size
      rw [attesterWriteWord_size_nat]
      apply le_trans _ (Nat.le_max_left _ _)
      change free.toNat + 32 ≤
        (Reasoning.Theory.writeWord
          (attesterMultiRevokeInnerArrayCopyUidMem I payload idx mem aw)
          zero.toNat (⟨0⟩ : UInt256)).size
      exact le_trans
        (by
          change free.toNat + 32 ≤
            (Reasoning.Theory.writeWord
              (attesterMultiRevokeInnerArrayCopyFreeMem mem aw)
              free.toNat (attesterMultiRevokeInnerArrayCopyUidWord I payload idx)).size
          rw [attesterWriteWord_size_nat]
          exact Nat.le_max_right _ _)
        (attesterWriteWord_size_ge_nat
          (attesterMultiRevokeInnerArrayCopyUidMem I payload idx mem aw)
          zero.toNat (⟨0⟩ : UInt256))
    have hstepSizePtr32 :
        ((⟨32⟩ : UInt256) + ptr).toNat + 32 ≤
          (attesterMultiRevokeInnerArrayCopyStepMem I base payload idx mem aw).size := by
      rw [hptr32ToNat]
      change zero.toNat + 32 ≤
        (Reasoning.Theory.writeWord
          (attesterMultiRevokeInnerArrayCopyZeroMem I payload idx mem aw)
          curSlot.toNat free).size
      rw [attesterWriteWord_size_nat]
      apply le_trans _ (Nat.le_max_left _ _)
      change zero.toNat + 32 ≤
        (Reasoning.Theory.writeWord
          (attesterMultiRevokeInnerArrayCopyUidMem I payload idx mem aw)
          zero.toNat (⟨0⟩ : UInt256)).size
      rw [attesterWriteWord_size_nat]
      exact Nat.le_max_right _ _
    have hslotRead :
        (attesterMultiRevokeInnerArrayCopyStepMem I base payload idx mem aw).readWithPadding
            slot.toNat 32 =
          UInt256.toByteArray ptr := by
      rw [hslotEq, hptrEq]
      exact attesterMultiRevokeInnerArrayCopyStep_read_current_slot
        (I := I) (base := base) (payload := payload) (idx := idx)
        (mem := mem) (aw := aw)
    have hptrRead :
        (attesterMultiRevokeInnerArrayCopyStepMem I base payload idx mem aw).readWithPadding
            ptr.toNat 32 =
          UInt256.toByteArray
            (calldataWord I.calldata
              (attesterMultiRevokeInnerArrayCopyCalldataOffset payload
                (UInt256.ofNat oldCopied)).toNat) := by
      rw [hptrToNat]
      have huid :=
        attesterMultiRevokeInnerArrayCopyStep_read_current_uid
          (I := I) (base := base) (payload := payload) (idx := idx)
          (mem := mem) (aw := aw) hzeroToNat (Or.inr hslotBelowFree)
      have hidxEq : idx = UInt256.ofNat oldCopied := by
        simpa [oldCopied] using hidx
      simpa [attesterMultiRevokeInnerArrayCopyUidWord, hidxEq] using huid
    have hptr32Read :
        (attesterMultiRevokeInnerArrayCopyStepMem I base payload idx mem aw).readWithPadding
            ((⟨32⟩ : UInt256) + ptr).toNat 32 =
          UInt256.toByteArray (⟨0⟩ : UInt256) := by
      rw [hptr32ToNat]
      exact attesterMultiRevokeInnerArrayCopyStep_read_current_zero
        (I := I) (base := base) (payload := payload) (idx := idx)
        (mem := mem) (aw := aw) (Or.inr hslotBelowZero)
    exact
      ⟨hstepSizeSlot, hstepSizePtr, hstepSizePtr32,
        hslotRead, hptrRead, hptr32Read⟩

def AttesterMultiRevokeRequestMemoryLayoutAt
    (schemas schemaUids : List Value) (mem : ByteArray) (aw outerBase : UInt256)
    (idx : Nat) : Prop :=
  ∀ {schema uids},
    lookupNth? schemas idx = some schema →
    lookupNth? schemaUids idx = some (.array uids) →
    ∃ schemaWord,
      attesterBytes32ValueWord? schema = some schemaWord ∧
      attesterMloadWord mem aw
          (attesterMultiRevokeRequestPtr mem aw outerBase idx) = schemaWord ∧
      attesterMloadWord mem aw
          (attesterMultiRevokeRequestDataPtr mem aw outerBase idx) =
        UInt256.ofNat uids.length ∧
      ∀ {j uid},
        lookupNth? uids j = some uid →
        ∃ uidWord,
          attesterBytes32ValueWord? uid = some uidWord ∧
          attesterMloadWord mem aw
              (attesterMultiRevokeRequestDataElemPtr mem aw outerBase idx j) =
            uidWord ∧
          attesterMloadWord mem aw
              ((⟨32⟩ : UInt256) +
                attesterMultiRevokeRequestDataElemPtr mem aw outerBase idx j) =
            (⟨0⟩ : UInt256)

def AttesterMultiRevokeRequestsMemoryLayout
    (schemas schemaUids : List Value) (i : Nat)
    (mem : ByteArray) (aw outerBase : UInt256) : Prop :=
  ∀ {idx}, idx < i →
    AttesterMultiRevokeRequestMemoryLayoutAt schemas schemaUids mem aw outerBase idx

def AttesterMultiRevokeRequestReadLayoutAt
    (schemas schemaUids : List Value) (mem : ByteArray) (outerBase : UInt256)
    (idx : Nat) : Prop :=
  ∀ {schema uids},
    lookupNth? schemas idx = some schema →
    lookupNth? schemaUids idx = some (.array uids) →
    ∃ schemaWord reqPtr dataPtr,
      attesterBytes32ValueWord? schema = some schemaWord ∧
      let slot := attesterMultiRevokePostCopyOuterSlotWord outerBase (UInt256.ofNat idx)
      slot.toNat + 32 ≤ mem.size ∧
      mem.readWithPadding slot.toNat 32 = UInt256.toByteArray reqPtr ∧
      reqPtr.toNat + 32 ≤ mem.size ∧
      ((⟨32⟩ : UInt256) + reqPtr).toNat + 32 ≤ mem.size ∧
      mem.readWithPadding reqPtr.toNat 32 = UInt256.toByteArray schemaWord ∧
      mem.readWithPadding ((⟨32⟩ : UInt256) + reqPtr).toNat 32 =
        UInt256.toByteArray dataPtr ∧
      dataPtr.toNat + 32 ≤ mem.size ∧
      mem.readWithPadding dataPtr.toNat 32 =
        UInt256.toByteArray (UInt256.ofNat uids.length) ∧
      ∀ {j uid},
        lookupNth? uids j = some uid →
        ∃ uidWord elemPtr,
          attesterBytes32ValueWord? uid = some uidWord ∧
          let elemSlot := (⟨32⟩ : UInt256) +
            UInt256.mul (⟨32⟩ : UInt256) (UInt256.ofNat j) + dataPtr
          elemSlot.toNat + 32 ≤ mem.size ∧
          mem.readWithPadding elemSlot.toNat 32 = UInt256.toByteArray elemPtr ∧
          elemPtr.toNat + 32 ≤ mem.size ∧
          ((⟨32⟩ : UInt256) + elemPtr).toNat + 32 ≤ mem.size ∧
          mem.readWithPadding elemPtr.toNat 32 = UInt256.toByteArray uidWord ∧
          mem.readWithPadding ((⟨32⟩ : UInt256) + elemPtr).toNat 32 =
            UInt256.toByteArray (⟨0⟩ : UInt256)

def AttesterMultiRevokeRequestsReadLayout
    (schemas schemaUids : List Value) (i : Nat)
    (mem : ByteArray) (outerBase : UInt256) : Prop :=
  ∀ {idx}, idx < i →
    AttesterMultiRevokeRequestReadLayoutAt schemas schemaUids mem outerBase idx

def AttesterMultiRevokeRequestReadLayoutAtBounded
    (schemas schemaUids : List Value) (mem : ByteArray) (outerBase : UInt256)
    (contentLo bound idx : Nat) : Prop :=
  ∀ {schema uids},
    lookupNth? schemas idx = some schema →
    lookupNth? schemaUids idx = some (.array uids) →
    ∃ schemaWord reqPtr dataPtr,
      attesterBytes32ValueWord? schema = some schemaWord ∧
      let slot := attesterMultiRevokePostCopyOuterSlotWord outerBase (UInt256.ofNat idx)
      64 + 32 ≤ slot.toNat ∧
      slot.toNat + 32 ≤ bound ∧
      slot.toNat + 32 ≤ mem.size ∧
      mem.readWithPadding slot.toNat 32 = UInt256.toByteArray reqPtr ∧
      contentLo ≤ reqPtr.toNat ∧
      reqPtr.toNat + 32 ≤ bound ∧
      reqPtr.toNat + 32 ≤ mem.size ∧
      contentLo ≤ ((⟨32⟩ : UInt256) + reqPtr).toNat ∧
      ((⟨32⟩ : UInt256) + reqPtr).toNat + 32 ≤ bound ∧
      ((⟨32⟩ : UInt256) + reqPtr).toNat + 32 ≤ mem.size ∧
      mem.readWithPadding reqPtr.toNat 32 = UInt256.toByteArray schemaWord ∧
      mem.readWithPadding ((⟨32⟩ : UInt256) + reqPtr).toNat 32 =
        UInt256.toByteArray dataPtr ∧
      contentLo ≤ dataPtr.toNat ∧
      dataPtr.toNat + 32 ≤ bound ∧
      dataPtr.toNat + 32 ≤ mem.size ∧
      mem.readWithPadding dataPtr.toNat 32 =
        UInt256.toByteArray (UInt256.ofNat uids.length) ∧
      ∀ {j uid},
        lookupNth? uids j = some uid →
        ∃ uidWord elemPtr,
          attesterBytes32ValueWord? uid = some uidWord ∧
          let elemSlot := (⟨32⟩ : UInt256) +
            UInt256.mul (⟨32⟩ : UInt256) (UInt256.ofNat j) + dataPtr
          contentLo ≤ elemSlot.toNat ∧
          elemSlot.toNat + 32 ≤ bound ∧
          elemSlot.toNat + 32 ≤ mem.size ∧
          mem.readWithPadding elemSlot.toNat 32 = UInt256.toByteArray elemPtr ∧
          contentLo ≤ elemPtr.toNat ∧
          elemPtr.toNat + 32 ≤ bound ∧
          elemPtr.toNat + 32 ≤ mem.size ∧
          contentLo ≤ ((⟨32⟩ : UInt256) + elemPtr).toNat ∧
          ((⟨32⟩ : UInt256) + elemPtr).toNat + 32 ≤ bound ∧
          ((⟨32⟩ : UInt256) + elemPtr).toNat + 32 ≤ mem.size ∧
          mem.readWithPadding elemPtr.toNat 32 = UInt256.toByteArray uidWord ∧
          mem.readWithPadding ((⟨32⟩ : UInt256) + elemPtr).toNat 32 =
            UInt256.toByteArray (⟨0⟩ : UInt256)

def AttesterMultiRevokeRequestsReadLayoutBounded
    (schemas schemaUids : List Value) (i : Nat)
    (mem : ByteArray) (outerBase : UInt256) (contentLo bound : Nat) : Prop :=
  ∀ {idx}, idx < i →
    AttesterMultiRevokeRequestReadLayoutAtBounded
      schemas schemaUids mem outerBase contentLo bound idx

theorem AttesterMultiRevokeRequestReadLayoutAtBounded.to_readLayout
    {schemas schemaUids : List Value} {mem : ByteArray} {outerBase : UInt256}
    {contentLo bound idx : Nat}
    (h :
      AttesterMultiRevokeRequestReadLayoutAtBounded
        schemas schemaUids mem outerBase contentLo bound idx) :
    AttesterMultiRevokeRequestReadLayoutAt schemas schemaUids mem outerBase idx := by
  intro schema uids hschema huids
  rcases h hschema huids with
    ⟨schemaWord, reqPtr, dataPtr, hschemaWord, hslot64, hslotBound, hslotMem,
      hslotRead, hreqLo, hreqBound, hreqMem, hreq32Lo, hreq32Bound, hreq32Mem,
      hschemaRead, hdataPtrRead, hdataLo, hdataBound, hdataMem, hdataRead,
      huidsRead⟩
  refine ⟨schemaWord, reqPtr, dataPtr, hschemaWord, hslotMem, hslotRead,
    hreqMem, hreq32Mem, hschemaRead, hdataPtrRead, hdataMem, hdataRead, ?_⟩
  intro j uid huid
  rcases huidsRead huid with
    ⟨uidWord, elemPtr, huidWord, helemSlotLo, helemSlotBound, helemSlotMem,
      helemSlotRead, helemPtrLo, helemPtrBound, helemPtrMem, helemPtr32Lo,
      helemPtr32Bound, helemPtr32Mem, helemRead, helemExtraRead⟩
  exact ⟨uidWord, elemPtr, huidWord, helemSlotMem, helemSlotRead,
    helemPtrMem, helemPtr32Mem, helemRead, helemExtraRead⟩

theorem AttesterMultiRevokeRequestsReadLayoutBounded.to_readLayout
    {schemas schemaUids : List Value} {i : Nat}
    {mem : ByteArray} {outerBase : UInt256} {contentLo bound : Nat}
    (h :
      AttesterMultiRevokeRequestsReadLayoutBounded
        schemas schemaUids i mem outerBase contentLo bound) :
    AttesterMultiRevokeRequestsReadLayout schemas schemaUids i mem outerBase := by
  intro idx hidx
  exact AttesterMultiRevokeRequestReadLayoutAtBounded.to_readLayout (h hidx)

theorem AttesterMultiRevokeRequestsReadLayout_zero
    (schemas schemaUids : List Value) (mem : ByteArray) (outerBase : UInt256) :
    AttesterMultiRevokeRequestsReadLayout schemas schemaUids 0 mem outerBase := by
  intro idx hidx
  omega

theorem AttesterMultiRevokeRequestsReadLayoutBounded_zero
    (schemas schemaUids : List Value) (mem : ByteArray) (outerBase : UInt256)
    (contentLo bound : Nat) :
    AttesterMultiRevokeRequestsReadLayoutBounded
      schemas schemaUids 0 mem outerBase contentLo bound := by
  intro idx hidx
  omega

theorem AttesterMultiRevokeRequestsReadLayout_mono
    {schemas schemaUids : List Value} {i j : Nat}
    {mem : ByteArray} {outerBase : UInt256}
    (hle : i ≤ j)
    (h : AttesterMultiRevokeRequestsReadLayout schemas schemaUids j mem outerBase) :
    AttesterMultiRevokeRequestsReadLayout schemas schemaUids i mem outerBase := by
  intro idx hidx
  exact h (by omega)

theorem AttesterMultiRevokeRequestsReadLayoutBounded_mono
    {schemas schemaUids : List Value} {i j : Nat}
    {mem : ByteArray} {outerBase : UInt256} {contentLo bound : Nat}
    (hle : i ≤ j)
    (h :
      AttesterMultiRevokeRequestsReadLayoutBounded
        schemas schemaUids j mem outerBase contentLo bound) :
    AttesterMultiRevokeRequestsReadLayoutBounded
      schemas schemaUids i mem outerBase contentLo bound := by
  intro idx hidx
  exact h (by omega)

def AttesterReadPreservedBeforeExcept
    (mem₀ mem₁ : ByteArray) (bound protectedSlot : Nat) : Prop :=
  ∀ {read : Nat} {word : UInt256},
    read + 32 ≤ mem₀.size →
    mem₀.readWithPadding read 32 = UInt256.toByteArray word →
    64 + 32 ≤ read →
    read + 32 ≤ bound →
    (read + 32 ≤ protectedSlot ∨ protectedSlot + 32 ≤ read) →
      read + 32 ≤ mem₁.size ∧
      mem₁.readWithPadding read 32 = UInt256.toByteArray word

set_option maxHeartbeats 1000000 in
theorem AttesterMultiRevokeRequestReadLayoutAtBounded.preserve_except
    {schemas schemaUids : List Value}
    {mem mem' : ByteArray} {outerBase : UInt256}
    {contentLo bound bound' protectedSlot idx : Nat}
    (hcontentLo64 : 64 + 32 ≤ contentLo)
    (hboundLe : bound ≤ bound')
    (hownSlotDisj :
      (attesterMultiRevokePostCopyOuterSlotWord outerBase (UInt256.ofNat idx)).toNat + 32 ≤
        protectedSlot)
    (hcontentDisj : protectedSlot + 32 ≤ contentLo)
    (hpres : AttesterReadPreservedBeforeExcept mem mem' bound protectedSlot)
    (h :
      AttesterMultiRevokeRequestReadLayoutAtBounded
        schemas schemaUids mem outerBase contentLo bound idx) :
    AttesterMultiRevokeRequestReadLayoutAtBounded
      schemas schemaUids mem' outerBase contentLo bound' idx := by
  intro schema uids hschema huids
  rcases h hschema huids with
    ⟨schemaWord, reqPtr, dataPtr, hschemaWord, hslot64, hslotBound, hslotMem,
      hslotRead, hreqLo, hreqBound, hreqMem, hreq32Lo, hreq32Bound, hreq32Mem,
      hschemaRead, hdataPtrRead, hdataLo, hdataBound, hdataMem, hdataRead,
      huidsRead⟩
  let slot := attesterMultiRevokePostCopyOuterSlotWord outerBase (UInt256.ofNat idx)
  have hslotPres :=
    hpres hslotMem hslotRead hslot64 hslotBound
      (Or.inl (by simpa [slot] using hownSlotDisj))
  have hreq64 : 64 + 32 ≤ reqPtr.toNat := le_trans hcontentLo64 hreqLo
  have hreqPres :=
    hpres hreqMem hschemaRead hreq64 hreqBound
      (Or.inr (le_trans hcontentDisj hreqLo))
  have hreq32_64 : 64 + 32 ≤ ((⟨32⟩ : UInt256) + reqPtr).toNat :=
    le_trans hcontentLo64 hreq32Lo
  have hreq32Pres :=
    hpres hreq32Mem hdataPtrRead hreq32_64 hreq32Bound
      (Or.inr (le_trans hcontentDisj hreq32Lo))
  have hdata64 : 64 + 32 ≤ dataPtr.toNat := le_trans hcontentLo64 hdataLo
  have hdataPres :=
    hpres hdataMem hdataRead hdata64 hdataBound
      (Or.inr (le_trans hcontentDisj hdataLo))
  refine ⟨schemaWord, reqPtr, dataPtr, hschemaWord, hslot64,
    le_trans hslotBound hboundLe, hslotPres.1, hslotPres.2,
    hreqLo, le_trans hreqBound hboundLe, hreqPres.1,
    hreq32Lo, le_trans hreq32Bound hboundLe, hreq32Pres.1,
    hreqPres.2, hreq32Pres.2,
    hdataLo, le_trans hdataBound hboundLe, hdataPres.1, hdataPres.2, ?_⟩
  intro j uid huid
  rcases huidsRead huid with
    ⟨uidWord, elemPtr, huidWord, helemSlotLo, helemSlotBound, helemSlotMem,
      helemSlotRead, helemPtrLo, helemPtrBound, helemPtrMem, helemPtr32Lo,
      helemPtr32Bound, helemPtr32Mem, helemRead, helemExtraRead⟩
  let elemSlot := (⟨32⟩ : UInt256) +
    UInt256.mul (⟨32⟩ : UInt256) (UInt256.ofNat j) + dataPtr
  have helemSlot64 : 64 + 32 ≤ elemSlot.toNat :=
    le_trans hcontentLo64 helemSlotLo
  have helemSlotPres :=
    hpres helemSlotMem helemSlotRead helemSlot64 helemSlotBound
      (Or.inr (le_trans hcontentDisj helemSlotLo))
  have helemPtr64 : 64 + 32 ≤ elemPtr.toNat :=
    le_trans hcontentLo64 helemPtrLo
  have helemPtrPres :=
    hpres helemPtrMem helemRead helemPtr64 helemPtrBound
      (Or.inr (le_trans hcontentDisj helemPtrLo))
  have helemPtr32_64 : 64 + 32 ≤ ((⟨32⟩ : UInt256) + elemPtr).toNat :=
    le_trans hcontentLo64 helemPtr32Lo
  have helemPtr32Pres :=
    hpres helemPtr32Mem helemExtraRead helemPtr32_64 helemPtr32Bound
      (Or.inr (le_trans hcontentDisj helemPtr32Lo))
  exact ⟨uidWord, elemPtr, huidWord, helemSlotLo,
    le_trans helemSlotBound hboundLe, helemSlotPres.1, helemSlotPres.2,
    helemPtrLo, le_trans helemPtrBound hboundLe, helemPtrPres.1,
    helemPtr32Lo, le_trans helemPtr32Bound hboundLe, helemPtr32Pres.1,
    helemPtrPres.2, helemPtr32Pres.2⟩

theorem AttesterMultiRevokeRequestReadLayoutAt.to_mload
    {schemas schemaUids : List Value} {mem : ByteArray} {aw outerBase : UInt256}
    {idx : Nat}
    (hactive : ∀ {off : UInt256}, off.toNat + 32 ≤ mem.size → ¬ off ≥ aw * (⟨32⟩ : UInt256))
    (hread : AttesterMultiRevokeRequestReadLayoutAt schemas schemaUids mem outerBase idx) :
    AttesterMultiRevokeRequestMemoryLayoutAt schemas schemaUids mem aw outerBase idx := by
  intro schema uids hschema huids
  rcases hread hschema huids with
    ⟨schemaWord, reqPtr, dataPtr, hschemaWord, hslotMem, hslotRead,
      hreqMem, hreqDataMem, hschemaRead, hdataPtrRead, hdataMem, hdataRead, huidsRead⟩
  let slot := attesterMultiRevokePostCopyOuterSlotWord outerBase (UInt256.ofNat idx)
  have hreqMload :
      attesterMultiRevokeRequestPtr mem aw outerBase idx = reqPtr := by
    dsimp [attesterMultiRevokeRequestPtr, slot] at hslotMem hslotRead ⊢
    exact attesterMloadWord_of_readWithPadding hslotMem (hactive hslotMem) hslotRead
  have hschemaMload :
      attesterMloadWord mem aw (attesterMultiRevokeRequestPtr mem aw outerBase idx) =
        schemaWord := by
    rw [hreqMload]
    exact attesterMloadWord_of_readWithPadding hreqMem (hactive hreqMem) hschemaRead
  have hdataPtrMload :
      attesterMultiRevokeRequestDataPtr mem aw outerBase idx = dataPtr := by
    dsimp [attesterMultiRevokeRequestDataPtr]
    rw [hreqMload]
    exact attesterMloadWord_of_readWithPadding hreqDataMem (hactive hreqDataMem)
      hdataPtrRead
  have hdataLenMload :
      attesterMloadWord mem aw (attesterMultiRevokeRequestDataPtr mem aw outerBase idx) =
        UInt256.ofNat uids.length := by
    rw [hdataPtrMload]
    exact attesterMloadWord_of_readWithPadding hdataMem (hactive hdataMem) hdataRead
  refine ⟨schemaWord, hschemaWord, hschemaMload, hdataLenMload, ?_⟩
  intro j uid huid
  rcases huidsRead huid with
    ⟨uidWord, elemPtr, huidWord, helemSlotMem, helemSlotRead,
      helemMem, helemExtraMem, helemRead, helemExtraRead⟩
  let elemSlot := (⟨32⟩ : UInt256) +
    UInt256.mul (⟨32⟩ : UInt256) (UInt256.ofNat j) + dataPtr
  have helemPtrMload :
      attesterMultiRevokeRequestDataElemPtr mem aw outerBase idx j = elemPtr := by
    dsimp [attesterMultiRevokeRequestDataElemPtr, elemSlot]
    rw [hdataPtrMload]
    exact attesterMloadWord_of_readWithPadding helemSlotMem (hactive helemSlotMem)
      helemSlotRead
  have huidMload :
      attesterMloadWord mem aw
          (attesterMultiRevokeRequestDataElemPtr mem aw outerBase idx j) =
        uidWord := by
    rw [helemPtrMload]
    exact attesterMloadWord_of_readWithPadding helemMem (hactive helemMem) helemRead
  have hextraMload :
      attesterMloadWord mem aw
          ((⟨32⟩ : UInt256) +
            attesterMultiRevokeRequestDataElemPtr mem aw outerBase idx j) =
        (⟨0⟩ : UInt256) := by
    rw [helemPtrMload]
    exact attesterMloadWord_of_readWithPadding helemExtraMem (hactive helemExtraMem)
      helemExtraRead
  exact ⟨uidWord, huidWord, huidMload, hextraMload⟩

theorem AttesterMultiRevokeRequestsMemoryLayout_zero
    (schemas schemaUids : List Value) (mem : ByteArray) (aw outerBase : UInt256) :
    AttesterMultiRevokeRequestsMemoryLayout schemas schemaUids 0 mem aw outerBase := by
  intro idx hidx
  omega

theorem AttesterMultiRevokeRequestsMemoryLayout_mono
    {schemas schemaUids : List Value} {i j : Nat}
    {mem : ByteArray} {aw outerBase : UInt256}
    (hle : i ≤ j)
    (h : AttesterMultiRevokeRequestsMemoryLayout schemas schemaUids j mem aw outerBase) :
    AttesterMultiRevokeRequestsMemoryLayout schemas schemaUids i mem aw outerBase := by
  intro idx hidx
  exact h (by omega)

theorem attesterMultiRevokePostCopyOuterMem_read_current_slot
    {I : ExecutionEnv} {base outerBase schemaPayload idx : UInt256}
    {mem : ByteArray} {aw : UInt256} :
    (attesterMultiRevokePostCopyOuterMem base outerBase I schemaPayload idx mem aw).readWithPadding
        (attesterMultiRevokePostCopyOuterSlotWord outerBase idx).toNat 32 =
      UInt256.toByteArray (attesterMultiRevokePostCopyFreeWord mem aw) := by
  change (Reasoning.Theory.writeWord
      (attesterMultiRevokePostCopyDataMem base I schemaPayload idx mem aw)
      (attesterMultiRevokePostCopyOuterSlotWord outerBase idx).toNat
      (attesterMultiRevokePostCopyFreeWord mem aw)).readWithPadding
        (attesterMultiRevokePostCopyOuterSlotWord outerBase idx).toNat 32 =
      UInt256.toByteArray (attesterMultiRevokePostCopyFreeWord mem aw)
  exact attesterWriteWord_read_back_nat
    (attesterMultiRevokePostCopyDataMem base I schemaPayload idx mem aw)
    (attesterMultiRevokePostCopyOuterSlotWord outerBase idx).toNat
    (attesterMultiRevokePostCopyFreeWord mem aw)

theorem attesterMultiRevokePostCopyOuterMem_size_ge
    {I : ExecutionEnv} {base outerBase schemaPayload idx : UInt256}
    {mem : ByteArray} {aw : UInt256} {n : Nat}
    (hmem : n ≤ mem.size) :
    n ≤ (attesterMultiRevokePostCopyOuterMem base outerBase I schemaPayload idx mem aw).size := by
  change n ≤
    (Reasoning.Theory.writeWord
      (attesterMultiRevokePostCopyDataMem base I schemaPayload idx mem aw)
      (attesterMultiRevokePostCopyOuterSlotWord outerBase idx).toNat
      (attesterMultiRevokePostCopyFreeWord mem aw)).size
  apply le_trans _ (attesterWriteWord_size_ge_nat
    (attesterMultiRevokePostCopyDataMem base I schemaPayload idx mem aw)
    (attesterMultiRevokePostCopyOuterSlotWord outerBase idx).toNat
    (attesterMultiRevokePostCopyFreeWord mem aw))
  change n ≤
    (Reasoning.Theory.writeWord
      (attesterMultiRevokePostCopySchemaMem I schemaPayload idx mem aw)
      (attesterMultiRevokePostCopyDataOffsetWord mem aw).toNat base).size
  apply le_trans _ (attesterWriteWord_size_ge_nat
    (attesterMultiRevokePostCopySchemaMem I schemaPayload idx mem aw)
    (attesterMultiRevokePostCopyDataOffsetWord mem aw).toNat base)
  change n ≤
    (Reasoning.Theory.writeWord
      (attesterMultiRevokePostCopyFreeMem mem aw)
      (attesterMultiRevokePostCopyFreeWord mem aw).toNat
      (attesterMultiRevokePostCopySchemaWord I schemaPayload idx)).size
  apply le_trans _ (attesterWriteWord_size_ge_nat
    (attesterMultiRevokePostCopyFreeMem mem aw)
    (attesterMultiRevokePostCopyFreeWord mem aw).toNat
    (attesterMultiRevokePostCopySchemaWord I schemaPayload idx))
  change n ≤
    (Reasoning.Theory.writeWord mem 64
      (attesterMultiRevokePostCopyFreeBumpWord mem aw)).size
  exact le_trans hmem
    (attesterWriteWord_size_ge_nat mem 64
      (attesterMultiRevokePostCopyFreeBumpWord mem aw))

theorem attesterMultiRevokePostCopyOuterMem_current_schema_size
    {I : ExecutionEnv} {base outerBase schemaPayload idx : UInt256}
    {mem : ByteArray} {aw : UInt256} :
    (attesterMultiRevokePostCopyFreeWord mem aw).toNat + 32 ≤
      (attesterMultiRevokePostCopyOuterMem base outerBase I schemaPayload idx mem aw).size := by
  change (attesterMultiRevokePostCopyFreeWord mem aw).toNat + 32 ≤
    (Reasoning.Theory.writeWord
      (attesterMultiRevokePostCopyDataMem base I schemaPayload idx mem aw)
      (attesterMultiRevokePostCopyOuterSlotWord outerBase idx).toNat
      (attesterMultiRevokePostCopyFreeWord mem aw)).size
  apply le_trans _ (attesterWriteWord_size_ge_nat
    (attesterMultiRevokePostCopyDataMem base I schemaPayload idx mem aw)
    (attesterMultiRevokePostCopyOuterSlotWord outerBase idx).toNat
    (attesterMultiRevokePostCopyFreeWord mem aw))
  change (attesterMultiRevokePostCopyFreeWord mem aw).toNat + 32 ≤
    (Reasoning.Theory.writeWord
      (attesterMultiRevokePostCopySchemaMem I schemaPayload idx mem aw)
      (attesterMultiRevokePostCopyDataOffsetWord mem aw).toNat base).size
  apply le_trans _ (attesterWriteWord_size_ge_nat
    (attesterMultiRevokePostCopySchemaMem I schemaPayload idx mem aw)
    (attesterMultiRevokePostCopyDataOffsetWord mem aw).toNat base)
  change (attesterMultiRevokePostCopyFreeWord mem aw).toNat + 32 ≤
    (Reasoning.Theory.writeWord
      (attesterMultiRevokePostCopyFreeMem mem aw)
      (attesterMultiRevokePostCopyFreeWord mem aw).toNat
      (attesterMultiRevokePostCopySchemaWord I schemaPayload idx)).size
  rw [attesterWriteWord_size_nat]
  exact Nat.le_max_right _ _

theorem attesterMultiRevokePostCopyOuterMem_current_data_size
    {I : ExecutionEnv} {base outerBase schemaPayload idx : UInt256}
    {mem : ByteArray} {aw : UInt256} :
    (attesterMultiRevokePostCopyDataOffsetWord mem aw).toNat + 32 ≤
      (attesterMultiRevokePostCopyOuterMem base outerBase I schemaPayload idx mem aw).size := by
  change (attesterMultiRevokePostCopyDataOffsetWord mem aw).toNat + 32 ≤
    (Reasoning.Theory.writeWord
      (attesterMultiRevokePostCopyDataMem base I schemaPayload idx mem aw)
      (attesterMultiRevokePostCopyOuterSlotWord outerBase idx).toNat
      (attesterMultiRevokePostCopyFreeWord mem aw)).size
  apply le_trans _ (attesterWriteWord_size_ge_nat
    (attesterMultiRevokePostCopyDataMem base I schemaPayload idx mem aw)
    (attesterMultiRevokePostCopyOuterSlotWord outerBase idx).toNat
    (attesterMultiRevokePostCopyFreeWord mem aw))
  change (attesterMultiRevokePostCopyDataOffsetWord mem aw).toNat + 32 ≤
    (Reasoning.Theory.writeWord
      (attesterMultiRevokePostCopySchemaMem I schemaPayload idx mem aw)
      (attesterMultiRevokePostCopyDataOffsetWord mem aw).toNat base).size
  rw [attesterWriteWord_size_nat]
  exact Nat.le_max_right _ _

theorem attesterMultiRevokePostCopyOuterMem_current_slot_size
    {I : ExecutionEnv} {base outerBase schemaPayload idx : UInt256}
    {mem : ByteArray} {aw : UInt256} :
    (attesterMultiRevokePostCopyOuterSlotWord outerBase idx).toNat + 32 ≤
      (attesterMultiRevokePostCopyOuterMem base outerBase I schemaPayload idx mem aw).size := by
  change (attesterMultiRevokePostCopyOuterSlotWord outerBase idx).toNat + 32 ≤
    (Reasoning.Theory.writeWord
      (attesterMultiRevokePostCopyDataMem base I schemaPayload idx mem aw)
      (attesterMultiRevokePostCopyOuterSlotWord outerBase idx).toNat
      (attesterMultiRevokePostCopyFreeWord mem aw)).size
  rw [attesterWriteWord_size_nat]
  exact Nat.le_max_right _ _

theorem attesterMultiRevokePostCopyOuterMem_mload_current_slot
    {I : ExecutionEnv} {base outerBase schemaPayload idx : UInt256}
    {mem : ByteArray} {aw : UInt256}
    (haw :
      ¬ attesterMultiRevokePostCopyOuterSlotWord outerBase idx ≥
        attesterMultiRevokePostCopyOuterAw base outerBase I schemaPayload idx mem aw *
          (⟨32⟩ : UInt256)) :
    attesterMloadWord
        (attesterMultiRevokePostCopyOuterMem base outerBase I schemaPayload idx mem aw)
        (attesterMultiRevokePostCopyOuterAw base outerBase I schemaPayload idx mem aw)
        (attesterMultiRevokePostCopyOuterSlotWord outerBase idx) =
      attesterMultiRevokePostCopyFreeWord mem aw := by
  have hmem :
      (attesterMultiRevokePostCopyOuterSlotWord outerBase idx).toNat + 32 ≤
        (attesterMultiRevokePostCopyOuterMem base outerBase I schemaPayload idx mem aw).size := by
    change (attesterMultiRevokePostCopyOuterSlotWord outerBase idx).toNat + 32 ≤
      (Reasoning.Theory.writeWord
        (attesterMultiRevokePostCopyDataMem base I schemaPayload idx mem aw)
        (attesterMultiRevokePostCopyOuterSlotWord outerBase idx).toNat
        (attesterMultiRevokePostCopyFreeWord mem aw)).size
    rw [attesterWriteWord_size_nat
      (attesterMultiRevokePostCopyDataMem base I schemaPayload idx mem aw)
      (attesterMultiRevokePostCopyOuterSlotWord outerBase idx).toNat
      (attesterMultiRevokePostCopyFreeWord mem aw)]
    exact Nat.le_max_right _ _
  exact attesterMloadWord_of_readWithPadding hmem haw
    (attesterMultiRevokePostCopyOuterMem_read_current_slot
      (I := I) (base := base) (outerBase := outerBase)
      (schemaPayload := schemaPayload) (idx := idx) (mem := mem) (aw := aw))

theorem attesterMultiRevokePostCopyOuterMem_read_current_schema
    {I : ExecutionEnv} {base outerBase schemaPayload idx : UInt256}
    {mem : ByteArray} {aw : UInt256}
    (hdataToNat :
      (attesterMultiRevokePostCopyDataOffsetWord mem aw).toNat =
        (attesterMultiRevokePostCopyFreeWord mem aw).toNat + 32)
    (hslotDisj :
      (attesterMultiRevokePostCopyFreeWord mem aw).toNat + 32 ≤
          (attesterMultiRevokePostCopyOuterSlotWord outerBase idx).toNat ∨
        (attesterMultiRevokePostCopyOuterSlotWord outerBase idx).toNat + 32 ≤
          (attesterMultiRevokePostCopyFreeWord mem aw).toNat) :
    (attesterMultiRevokePostCopyOuterMem base outerBase I schemaPayload idx mem aw).readWithPadding
        (attesterMultiRevokePostCopyFreeWord mem aw).toNat 32 =
      UInt256.toByteArray
        (attesterMultiRevokePostCopySchemaWord I schemaPayload idx) := by
  let free := attesterMultiRevokePostCopyFreeWord mem aw
  let dataOff := attesterMultiRevokePostCopyDataOffsetWord mem aw
  let slot := attesterMultiRevokePostCopyOuterSlotWord outerBase idx
  let schemaWord := attesterMultiRevokePostCopySchemaWord I schemaPayload idx
  have hreadSchema :
      (attesterMultiRevokePostCopySchemaMem I schemaPayload idx mem aw).readWithPadding
          free.toNat 32 =
        UInt256.toByteArray schemaWord := by
    change (Reasoning.Theory.writeWord
        (attesterMultiRevokePostCopyFreeMem mem aw)
        free.toNat schemaWord).readWithPadding free.toNat 32 =
      UInt256.toByteArray schemaWord
    exact attesterWriteWord_read_back_nat
      (attesterMultiRevokePostCopyFreeMem mem aw) free.toNat schemaWord
  have hmemSchema :
      free.toNat + 32 ≤
        (attesterMultiRevokePostCopySchemaMem I schemaPayload idx mem aw).size := by
    change free.toNat + 32 ≤
      (Reasoning.Theory.writeWord
        (attesterMultiRevokePostCopyFreeMem mem aw)
        free.toNat schemaWord).size
    rw [attesterWriteWord_size_nat
      (attesterMultiRevokePostCopyFreeMem mem aw) free.toNat schemaWord]
    exact Nat.le_max_right _ _
  have hreadData :
      (attesterMultiRevokePostCopyDataMem base I schemaPayload idx mem aw).readWithPadding
          free.toNat 32 =
        UInt256.toByteArray schemaWord := by
    change (Reasoning.Theory.writeWord
        (attesterMultiRevokePostCopySchemaMem I schemaPayload idx mem aw)
        dataOff.toNat base).readWithPadding free.toNat 32 =
      UInt256.toByteArray schemaWord
    exact attesterReadWithPadding_writeWord_preserved_above_nat
      (mem := attesterMultiRevokePostCopySchemaMem I schemaPayload idx mem aw)
      (base := free.toNat) (writeOff := dataOff.toNat)
      (len := schemaWord) (writeVal := base)
      hmemSchema (by rw [hdataToNat]) hreadSchema
  have hmemData :
      free.toNat + 32 ≤
        (attesterMultiRevokePostCopyDataMem base I schemaPayload idx mem aw).size := by
    change free.toNat + 32 ≤
      (Reasoning.Theory.writeWord
        (attesterMultiRevokePostCopySchemaMem I schemaPayload idx mem aw)
        dataOff.toNat base).size
    rw [attesterWriteWord_size_nat
      (attesterMultiRevokePostCopySchemaMem I schemaPayload idx mem aw)
      dataOff.toNat base]
    exact le_trans hmemSchema (Nat.le_max_left _ _)
  change (Reasoning.Theory.writeWord
      (attesterMultiRevokePostCopyDataMem base I schemaPayload idx mem aw)
      slot.toNat free).readWithPadding free.toNat 32 =
    UInt256.toByteArray schemaWord
  rcases hslotDisj with hslotAbove | hslotBelow
  · exact attesterReadWithPadding_writeWord_preserved_above_nat
      (mem := attesterMultiRevokePostCopyDataMem base I schemaPayload idx mem aw)
      (base := free.toNat) (writeOff := slot.toNat)
      (len := schemaWord) (writeVal := free)
      hmemData hslotAbove hreadData
  · exact attesterReadWithPadding_writeWord_preserved_below_nat
      (mem := attesterMultiRevokePostCopyDataMem base I schemaPayload idx mem aw)
      (base := free.toNat) (writeOff := slot.toNat)
      (len := schemaWord) (writeVal := free)
      hmemData hslotBelow hreadData

theorem attesterMultiRevokePostCopyOuterMem_read_current_data_ptr
    {I : ExecutionEnv} {base outerBase schemaPayload idx : UInt256}
    {mem : ByteArray} {aw : UInt256}
    (hslotDisj :
      (attesterMultiRevokePostCopyDataOffsetWord mem aw).toNat + 32 ≤
          (attesterMultiRevokePostCopyOuterSlotWord outerBase idx).toNat ∨
        (attesterMultiRevokePostCopyOuterSlotWord outerBase idx).toNat + 32 ≤
          (attesterMultiRevokePostCopyDataOffsetWord mem aw).toNat) :
    (attesterMultiRevokePostCopyOuterMem base outerBase I schemaPayload idx mem aw).readWithPadding
        (attesterMultiRevokePostCopyDataOffsetWord mem aw).toNat 32 =
      UInt256.toByteArray base := by
  let dataOff := attesterMultiRevokePostCopyDataOffsetWord mem aw
  let slot := attesterMultiRevokePostCopyOuterSlotWord outerBase idx
  have hreadData :
      (attesterMultiRevokePostCopyDataMem base I schemaPayload idx mem aw).readWithPadding
          dataOff.toNat 32 =
        UInt256.toByteArray base := by
    change (Reasoning.Theory.writeWord
        (attesterMultiRevokePostCopySchemaMem I schemaPayload idx mem aw)
        dataOff.toNat base).readWithPadding dataOff.toNat 32 =
      UInt256.toByteArray base
    exact attesterWriteWord_read_back_nat
      (attesterMultiRevokePostCopySchemaMem I schemaPayload idx mem aw) dataOff.toNat base
  have hmemData :
      dataOff.toNat + 32 ≤
        (attesterMultiRevokePostCopyDataMem base I schemaPayload idx mem aw).size := by
    change dataOff.toNat + 32 ≤
      (Reasoning.Theory.writeWord
        (attesterMultiRevokePostCopySchemaMem I schemaPayload idx mem aw)
        dataOff.toNat base).size
    rw [attesterWriteWord_size_nat
      (attesterMultiRevokePostCopySchemaMem I schemaPayload idx mem aw)
      dataOff.toNat base]
    exact Nat.le_max_right _ _
  change (Reasoning.Theory.writeWord
      (attesterMultiRevokePostCopyDataMem base I schemaPayload idx mem aw)
      slot.toNat (attesterMultiRevokePostCopyFreeWord mem aw)).readWithPadding
        dataOff.toNat 32 =
    UInt256.toByteArray base
  rcases hslotDisj with hslotAbove | hslotBelow
  · exact attesterReadWithPadding_writeWord_preserved_above_nat
      (mem := attesterMultiRevokePostCopyDataMem base I schemaPayload idx mem aw)
      (base := dataOff.toNat) (writeOff := slot.toNat)
      (len := base) (writeVal := attesterMultiRevokePostCopyFreeWord mem aw)
      hmemData hslotAbove hreadData
  · exact attesterReadWithPadding_writeWord_preserved_below_nat
      (mem := attesterMultiRevokePostCopyDataMem base I schemaPayload idx mem aw)
      (base := dataOff.toNat) (writeOff := slot.toNat)
      (len := base) (writeVal := attesterMultiRevokePostCopyFreeWord mem aw)
      hmemData hslotBelow hreadData

theorem attesterMultiRevokePostCopyOuterMem_read_preserved_before_free
    {I : ExecutionEnv} {base outerBase schemaPayload idx : UInt256}
    {mem : ByteArray} {aw : UInt256} {read : Nat} {word : UInt256}
    (hmem : read + 32 ≤ mem.size)
    (hread : mem.readWithPadding read 32 = UInt256.toByteArray word)
    (hread64 : 64 + 32 ≤ read)
    (hbeforeFree : read + 32 ≤ (attesterMultiRevokePostCopyFreeWord mem aw).toNat)
    (hdataToNat :
      (attesterMultiRevokePostCopyDataOffsetWord mem aw).toNat =
        (attesterMultiRevokePostCopyFreeWord mem aw).toNat + 32)
    (hslotDisj :
      read + 32 ≤ (attesterMultiRevokePostCopyOuterSlotWord outerBase idx).toNat ∨
        (attesterMultiRevokePostCopyOuterSlotWord outerBase idx).toNat + 32 ≤ read) :
    (attesterMultiRevokePostCopyOuterMem base outerBase I schemaPayload idx mem aw).readWithPadding
        read 32 =
      UInt256.toByteArray word := by
  let free := attesterMultiRevokePostCopyFreeWord mem aw
  let dataOff := attesterMultiRevokePostCopyDataOffsetWord mem aw
  let slot := attesterMultiRevokePostCopyOuterSlotWord outerBase idx
  have hreadFree :
      (attesterMultiRevokePostCopyFreeMem mem aw).readWithPadding read 32 =
        UInt256.toByteArray word := by
    change (Reasoning.Theory.writeWord mem 64
      (attesterMultiRevokePostCopyFreeBumpWord mem aw)).readWithPadding read 32 =
        UInt256.toByteArray word
    exact attesterReadWithPadding_writeWord_preserved_below_nat
      (mem := mem) (base := read) (writeOff := 64)
      (len := word) (writeVal := attesterMultiRevokePostCopyFreeBumpWord mem aw)
      hmem hread64 hread
  have hmemFree :
      read + 32 ≤ (attesterMultiRevokePostCopyFreeMem mem aw).size := by
    change read + 32 ≤
      (Reasoning.Theory.writeWord mem 64
        (attesterMultiRevokePostCopyFreeBumpWord mem aw)).size
    exact le_trans hmem
      (attesterWriteWord_size_ge_nat mem 64
        (attesterMultiRevokePostCopyFreeBumpWord mem aw))
  have hreadSchema :
      (attesterMultiRevokePostCopySchemaMem I schemaPayload idx mem aw).readWithPadding
          read 32 =
        UInt256.toByteArray word := by
    change (Reasoning.Theory.writeWord
      (attesterMultiRevokePostCopyFreeMem mem aw)
      free.toNat (attesterMultiRevokePostCopySchemaWord I schemaPayload idx)).readWithPadding
        read 32 =
      UInt256.toByteArray word
    exact attesterReadWithPadding_writeWord_preserved_above_nat
      (mem := attesterMultiRevokePostCopyFreeMem mem aw)
      (base := read) (writeOff := free.toNat)
      (len := word) (writeVal := attesterMultiRevokePostCopySchemaWord I schemaPayload idx)
      hmemFree hbeforeFree hreadFree
  have hmemSchema :
      read + 32 ≤
        (attesterMultiRevokePostCopySchemaMem I schemaPayload idx mem aw).size := by
    change read + 32 ≤
      (Reasoning.Theory.writeWord
        (attesterMultiRevokePostCopyFreeMem mem aw)
        free.toNat (attesterMultiRevokePostCopySchemaWord I schemaPayload idx)).size
    exact le_trans hmemFree
      (attesterWriteWord_size_ge_nat
        (attesterMultiRevokePostCopyFreeMem mem aw)
        free.toNat (attesterMultiRevokePostCopySchemaWord I schemaPayload idx))
  have hreadData :
      (attesterMultiRevokePostCopyDataMem base I schemaPayload idx mem aw).readWithPadding
          read 32 =
        UInt256.toByteArray word := by
    change (Reasoning.Theory.writeWord
      (attesterMultiRevokePostCopySchemaMem I schemaPayload idx mem aw)
      dataOff.toNat base).readWithPadding read 32 =
      UInt256.toByteArray word
    exact attesterReadWithPadding_writeWord_preserved_above_nat
      (mem := attesterMultiRevokePostCopySchemaMem I schemaPayload idx mem aw)
      (base := read) (writeOff := dataOff.toNat)
      (len := word) (writeVal := base)
      hmemSchema (by rw [hdataToNat]; omega) hreadSchema
  have hmemData :
      read + 32 ≤
        (attesterMultiRevokePostCopyDataMem base I schemaPayload idx mem aw).size := by
    change read + 32 ≤
      (Reasoning.Theory.writeWord
        (attesterMultiRevokePostCopySchemaMem I schemaPayload idx mem aw)
        dataOff.toNat base).size
    exact le_trans hmemSchema
      (attesterWriteWord_size_ge_nat
        (attesterMultiRevokePostCopySchemaMem I schemaPayload idx mem aw)
        dataOff.toNat base)
  change (Reasoning.Theory.writeWord
      (attesterMultiRevokePostCopyDataMem base I schemaPayload idx mem aw)
      slot.toNat (attesterMultiRevokePostCopyFreeWord mem aw)).readWithPadding read 32 =
    UInt256.toByteArray word
  rcases hslotDisj with hslotAbove | hslotBelow
  · exact attesterReadWithPadding_writeWord_preserved_above_nat
      (mem := attesterMultiRevokePostCopyDataMem base I schemaPayload idx mem aw)
      (base := read) (writeOff := slot.toNat)
      (len := word) (writeVal := attesterMultiRevokePostCopyFreeWord mem aw)
      hmemData hslotAbove hreadData
  · exact attesterReadWithPadding_writeWord_preserved_below_nat
      (mem := attesterMultiRevokePostCopyDataMem base I schemaPayload idx mem aw)
      (base := read) (writeOff := slot.toNat)
      (len := word) (writeVal := attesterMultiRevokePostCopyFreeWord mem aw)
      hmemData hslotBelow hreadData

end Benchmarks.EAS.Attester
