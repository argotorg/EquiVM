import Examples.UniswapV2Pair.MutatorDispatch

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

set_option maxRecDepth 2000000
set_option maxHeartbeats 2000000

namespace UniswapV2Pair

/-! ## `swap(uint256,uint256,address,bytes)` source slice -/

abbrev solcLegacyMaxU32 : Nat := ABI.solcMaxLenV1

theorem solcMaxLen_legacySolc05 :
    ABI.solcMaxLen DecodeMode.legacySolc05 = solcLegacyMaxU32 := rfl

/-- The raw ABI word for `swap`'s `amount0Out` argument. -/
abbrev swapAmount0OutWord (I : ExecutionEnv) : UInt256 :=
  calldataWord I.calldata 4

/-- The raw ABI word for `swap`'s `amount1Out` argument. -/
abbrev swapAmount1OutWord (I : ExecutionEnv) : UInt256 :=
  calldataWord I.calldata 36

/-- The raw ABI word for `swap`'s `to` argument. -/
abbrev swapToWord (I : ExecutionEnv) : UInt256 :=
  calldataWord I.calldata 68

abbrev swapToMaskedWord (I : ExecutionEnv) : UInt256 :=
  UInt256.land solcAddrMask (swapToWord I)

/-- The ABI head word holding `swap`'s dynamic `data` offset. -/
abbrev swapDataOffsetWord (I : ExecutionEnv) : UInt256 :=
  calldataWord I.calldata 100

abbrev swapDataOffset (I : ExecutionEnv) : Nat :=
  (swapDataOffsetWord I).toNat

/-- The ABI word holding `swap`'s dynamic `data` byte length. -/
abbrev swapDataSizeWord (I : ExecutionEnv) : UInt256 :=
  calldataWord I.calldata (4 + swapDataOffset I)

abbrev swapDataSize (I : ExecutionEnv) : Nat :=
  (swapDataSizeWord I).toNat

abbrev swapDataBytes (I : ExecutionEnv) : ByteArray :=
  ByteArray.mk (((I.calldata.toList.drop 4).drop (swapDataOffset I + 32)).take
    (swapDataSize I)).toArray

abbrev swapAmount0OutValue (I : ExecutionEnv) : Value :=
  .int (Int.ofNat (swapAmount0OutWord I).toNat)

abbrev swapAmount1OutValue (I : ExecutionEnv) : Value :=
  .int (Int.ofNat (swapAmount1OutWord I).toNat)

abbrev swapToValue (I : ExecutionEnv) : Value :=
  .address (AccountAddress.ofNat (swapToWord I).toNat)

abbrev swapDataValue (I : ExecutionEnv) : Value :=
  .bytes (swapDataBytes I)

abbrev swapStore (I : ExecutionEnv) : Store :=
  let s0 : Store := ∅
  let s1 := s0.insert "amount0Out" (swapAmount0OutValue I)
  let s2 := s1.insert "amount1Out" (swapAmount1OutValue I)
  let s3 := s2.insert "to" (swapToValue I)
  s3.insert "data" (swapDataValue I)

theorem swapStore_amount0Out (I : ExecutionEnv) :
    (swapStore I).get? "amount0Out" = some (swapAmount0OutValue I) := by
  rw [swapStore]
  rw [store_get_ne _ _ (by decide), store_get_ne _ _ (by decide),
    store_get_ne _ _ (by decide), store_get_self]

theorem swapStore_amount1Out (I : ExecutionEnv) :
    (swapStore I).get? "amount1Out" = some (swapAmount1OutValue I) := by
  rw [swapStore]
  rw [store_get_ne _ _ (by decide), store_get_ne _ _ (by decide), store_get_self]

theorem swapStore_to (I : ExecutionEnv) :
    (swapStore I).get? "to" = some (swapToValue I) := by
  rw [swapStore]
  rw [store_get_ne _ _ (by decide), store_get_self]

theorem swapStore_data (I : ExecutionEnv) :
    (swapStore I).get? "data" = some (swapDataValue I) := by
  rw [swapStore, store_get_self]

theorem swapStore_balanceOf (I : ExecutionEnv) :
    (swapStore I).get? "balanceOf" = none := by
  rw [swapStore]
  repeat rw [store_get_ne _ _ (by decide)]
  simp

theorem swapReadNat_drop4_eq_calldataWord {I : ExecutionEnv} {headOff : Nat}
    (h : 4 + headOff + 32 ≤ I.calldata.size) :
    readNat? (I.calldata.toList.drop 4) headOff =
      some (calldataWord I.calldata (4 + headOff)).toNat := by
  unfold readNat? readWord? readBytes?
  have htlen : I.calldata.toList.length = I.calldata.size := by
    rw [byteArray_toList_eq, Array.length_toList]
    rfl
  have hslice : (((I.calldata.toList.drop 4).drop headOff).take 32).length = 32 := by
    rw [List.length_take, List.length_drop, List.length_drop, htlen]
    omega
  rw [if_pos hslice]
  rw [calldataWord]
  rw [← decode_word_at_eq_any I.calldata (4 + headOff) h]
  simp [UInt256.toNat, List.drop_drop, Nat.add_comm]

theorem swapDecodeABIValue_uint256_legacy_ok {bytes : List UInt8} {start : Nat}
    (hlen : ((bytes.drop start).take 32).length = 32) :
    decodeABIValue? uint256 bytes start DecodeMode.legacySolc05 =
      some (.int (Int.ofNat (ABI.bytesToWord ((bytes.drop start).take 32)).toNat),
        start + 32) := by
  rw [decodeABIValue_scalarWordWithMode_eq (mode := DecodeMode.legacySolc05)
    (ty := uint256) (bytes := bytes) (start := start) (by decide)]
  simpa [uint256, uint256Int, abiUInt256] using
    (decodeScalarWordWithMode_uint256_ok (mode := DecodeMode.legacySolc05)
      (bytes := bytes) (start := start) hlen)

theorem swapDecodeABIValue_legacyAddress_ok {bytes : List UInt8} {start : Nat}
    (hlen : ((bytes.drop start).take 32).length = 32) :
    decodeABIValue? legacyAddr bytes start DecodeMode.legacySolc05 =
      some (.address (AccountAddress.ofNat
        (ABI.bytesToWord ((bytes.drop start).take 32)).toNat), start + 32) := by
  rw [decodeABIValue_scalarWordWithMode_eq (mode := DecodeMode.legacySolc05)
    (ty := legacyAddr) (bytes := bytes) (start := start) (by decide)]
  simpa [legacyAddr, addr, abiAddress] using
    (decodeScalarWord_legacyAddress_ok (bytes := bytes) (start := start) hlen)

theorem swapDecodeABIValue_bytes_ok {I : ExecutionEnv}
    (hlenWord : 4 + swapDataOffset I + 32 ≤ I.calldata.size)
    (hlenMax : ¬ solcLegacyMaxU32 < swapDataSize I)
    (hpayload : (((I.calldata.toList.drop 4).drop (swapDataOffset I + 32)).take
      (swapDataSize I)).length = swapDataSize I) :
    decodeABIValue? ABIType.bytes (I.calldata.toList.drop 4) (swapDataOffset I)
        DecodeMode.legacySolc05 =
      some (swapDataValue I, swapDataOffset I + 32 + paddedSize (swapDataSize I)) := by
  have hreadLen := swapReadNat_drop4_eq_calldataWord (I := I)
    (headOff := swapDataOffset I) hlenWord
  have hpayloadRead :
      readBytes? (I.calldata.toList.drop 4) (swapDataOffset I + 32) (swapDataSize I) =
        some (((I.calldata.toList.drop 4).drop (swapDataOffset I + 32)).take
          (swapDataSize I)) := by
    unfold readBytes?
    rw [if_pos hpayload]
  have hlenMax' :
      ¬ ABI.solcMaxLen DecodeMode.legacySolc05 <
        (calldataWord I.calldata (4 + (swapDataOffsetWord I).toNat)).toNat := by
    simpa [solcMaxLen_legacySolc05, swapDataSize, swapDataSizeWord,
      swapDataOffset] using hlenMax
  simp [decodeABIValue?, hreadLen, hlenMax', hpayloadRead, swapDataValue, swapDataBytes,
    swapDataSize, swapDataSizeWord, swapDataOffset]

theorem swapDecodeABIValues_ok {I : ExecutionEnv} (hsz132 : 132 ≤ I.calldata.size)
    (hoffMax : ¬ solcLegacyMaxU32 < swapDataOffset I)
    (hlenWord : 4 + swapDataOffset I + 32 ≤ I.calldata.size)
    (hlenMax : ¬ solcLegacyMaxU32 < swapDataSize I)
    (hpayload : (((I.calldata.toList.drop 4).drop (swapDataOffset I + 32)).take
      (swapDataSize I)).length = swapDataSize I) :
    decodeABIValues? [uint256, uint256, legacyAddr, ABIType.bytes]
      (I.calldata.toList.drop 4) 0 0 128 128 DecodeMode.legacySolc05 =
      some ([swapAmount0OutValue I, swapAmount1OutValue I, swapToValue I, swapDataValue I],
        max 128 (swapDataOffset I + 32 + paddedSize (swapDataSize I))) := by
  have htlen : I.calldata.toList.length = I.calldata.size := by
    rw [byteArray_toList_eq, Array.length_toList]
    rfl
  have htake0 : (((I.calldata.toList.drop 4).drop 0).take 32).length = 32 := by
    rw [List.drop_zero, List.length_take, List.length_drop, htlen]
    omega
  have htake32 : (((I.calldata.toList.drop 4).drop 32).take 32).length = 32 := by
    rw [List.length_take, List.length_drop, List.length_drop, htlen]
    omega
  have htake64 : (((I.calldata.toList.drop 4).drop 64).take 32).length = 32 := by
    rw [List.length_take, List.length_drop, List.length_drop, htlen]
    omega
  have hdec0 : decodeABIValue? uint256 (I.calldata.toList.drop 4) 0
      DecodeMode.legacySolc05 = some (.int (Int.ofNat
        (ABI.bytesToWord ((I.calldata.toList.drop 4).take 32)).toNat), 0 + 32) := by
    simpa [List.drop_zero] using
      swapDecodeABIValue_uint256_legacy_ok (bytes := I.calldata.toList.drop 4)
        (start := 0) htake0
  have hdec32 : decodeABIValue? uint256 (I.calldata.toList.drop 4) 32
      DecodeMode.legacySolc05 = some (.int (Int.ofNat
        (ABI.bytesToWord (((I.calldata.toList.drop 4).drop 32).take 32)).toNat), 32 + 32) := by
    exact swapDecodeABIValue_uint256_legacy_ok (bytes := I.calldata.toList.drop 4)
      (start := 32) htake32
  have hdec64 : decodeABIValue? legacyAddr (I.calldata.toList.drop 4) 64
      DecodeMode.legacySolc05 = some (.address (AccountAddress.ofNat
        (ABI.bytesToWord (((I.calldata.toList.drop 4).drop 64).take 32)).toNat),
        64 + 32) := by
    exact swapDecodeABIValue_legacyAddress_ok (bytes := I.calldata.toList.drop 4)
      (start := 64) htake64
  have hreadOff : readNat? (I.calldata.toList.drop 4) 96 = some (swapDataOffset I) := by
    simpa [swapDataOffset, swapDataOffsetWord] using
      swapReadNat_drop4_eq_calldataWord (I := I) (headOff := 96) (by omega)
  have hdecData := swapDecodeABIValue_bytes_ok (I := I) hlenWord hlenMax hpayload
  have hword4 : ABI.bytesToWord ((I.calldata.toList.drop 4).take 32) =
      swapAmount0OutWord I := by
    simpa [swapAmount0OutWord] using decode_word_at_eq I.calldata 4 (by omega) (by norm_num)
  have hword36 : ABI.bytesToWord (((I.calldata.toList.drop 4).drop 32).take 32) =
      swapAmount1OutWord I := by
    simpa [swapAmount1OutWord, List.drop_drop, Nat.add_comm, Nat.add_left_comm,
      Nat.add_assoc] using decode_word_at_eq I.calldata 36 (by omega) (by norm_num)
  have hword68 : ABI.bytesToWord (((I.calldata.toList.drop 4).drop 64).take 32) =
      swapToWord I := by
    simpa [swapToWord, List.drop_drop, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc]
      using decode_word_at_eq I.calldata 68 (by omega) (by norm_num)
  have hdec0r : decodeABIValue? (.elem (.int (.uint ⟨256, by decide⟩)))
      (I.calldata.toList.drop 4) 0 DecodeMode.legacySolc05 =
      some (.int (Int.ofNat (ABI.bytesToWord ((I.calldata.toList.drop 4).take 32)).toNat),
        0 + 32) := by
    simpa [uint256, uint256Int] using hdec0
  have hdec32r : decodeABIValue? (.elem (.int (.uint ⟨256, by decide⟩)))
      (I.calldata.toList.drop 4) 32 DecodeMode.legacySolc05 =
      some (.int (Int.ofNat
        (ABI.bytesToWord (((I.calldata.toList.drop 4).drop 32).take 32)).toNat), 32 + 32) := by
    simpa [uint256, uint256Int] using hdec32
  have hdec64r : decodeABIValue? (.elem .address) (I.calldata.toList.drop 4) 64
      DecodeMode.legacySolc05 = some (.address (AccountAddress.ofNat
        (ABI.bytesToWord (((I.calldata.toList.drop 4).drop 64).take 32)).toNat), 64 + 32) := by
    simpa [legacyAddr, addr] using hdec64
  have hword36' : bytesToWord (List.take 32 (List.drop 36 I.calldata.toList)) =
      swapAmount1OutWord I := by
    simpa [List.drop_drop, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using hword36
  have hword68' : bytesToWord (List.take 32 (List.drop 68 I.calldata.toList)) =
      swapToWord I := by
    simpa [List.drop_drop, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using hword68
  have hoffMax' : ¬ ABI.solcMaxLen DecodeMode.legacySolc05 < swapDataOffset I := by
    simpa [solcMaxLen_legacySolc05] using hoffMax
  have hmaxEnd :
      max 128 (max 96 (swapDataOffset I + 32 + paddedSize (swapDataSize I))) =
        max 128 (swapDataOffset I + 32 + paddedSize (swapDataSize I)) := by
    omega
  simp [decodeABIValues?, uint256, uint256Int, legacyAddr, addr, isDynamicABIType,
    staticABIEncodedSize?, hdec0r, hdec32r, hdec64r, hreadOff, hoffMax', hdecData, hword4,
    hword36', hword68', hmaxEnd, swapAmount0OutValue, swapAmount1OutValue, swapToValue]

theorem uniswapDecode_swap_ok {I : ExecutionEnv} (hsz132 : 132 ≤ I.calldata.size)
    (hoffMax : ¬ solcLegacyMaxU32 < swapDataOffset I)
    (hlenWord : 4 + swapDataOffset I + 32 ≤ I.calldata.size)
    (hlenMax : ¬ solcLegacyMaxU32 < swapDataSize I)
    (hpayload : (((I.calldata.toList.drop 4).drop (swapDataOffset I + 32)).take
      (swapDataSize I)).length = swapDataSize I) :
    decodeCalldataWithMode config.abiDecodeMode (swapTransition.params.map Param.name)
      (transitionSignature swapTransition).paramTypes I.calldata = some (swapStore I) := by
  show decodeCalldataWithMode DecodeMode.legacySolc05
    ["amount0Out", "amount1Out", "to", "data"] [uint256, uint256, legacyAddr, ABIType.bytes]
      I.calldata = _
  have htlen : I.calldata.toList.length = I.calldata.size := by
    rw [byteArray_toList_eq, Array.length_toList]
    rfl
  have hvals := swapDecodeABIValues_ok (I := I) hsz132 hoffMax hlenWord hlenMax hpayload
  unfold decodeCalldataWithMode decodeCalldata
  rw [if_neg (by rw [htlen]; omega : ¬ I.calldata.toList.length < 4)]
  by_cases hdyn :
      [uint256, uint256, legacyAddr, ABIType.bytes].any isDynamicABIType = true ∧
        2 ^ 255 ≤ I.calldata.toList.length
  all_goals
    first | rw [if_pos hdyn] | rw [if_neg hdyn]
    change (match decodeCalldata.decodeArgs DecodeMode.legacySolc05
        ["amount0Out", "amount1Out", "to", "data"]
        [uint256, uint256, legacyAddr, ABIType.bytes] (I.calldata.toList.drop 4) ∅ with
      | some (store, _) => some store
      | none => none) = some (swapStore I)
    unfold decodeCalldata.decodeArgs
    rw [show abiTupleHeadSize? [uint256, uint256, legacyAddr, ABIType.bytes] = some 128 by
      native_decide]
    simp only [bind, Option.bind]
    rw [if_neg (by
      rw [List.length_drop, htlen]
      omega : ¬ (I.calldata.toList.drop 4).length < 128)]
    rw [hvals]
    change decodeCalldata.insertValues ["amount0Out", "amount1Out", "to", "data"]
        [swapAmount0OutValue I, swapAmount1OutValue I, swapToValue I, swapDataValue I] ∅ =
      some (swapStore I)
    simp [decodeCalldata.insertValues, swapStore]

theorem uniswapDecode_swap_none_head_short {I : ExecutionEnv}
    (hsz4 : 4 ≤ I.calldata.size) (hshort : I.calldata.size < 132) :
    decodeCalldataWithMode config.abiDecodeMode (swapTransition.params.map Param.name)
      (transitionSignature swapTransition).paramTypes I.calldata = none := by
  show decodeCalldataWithMode DecodeMode.legacySolc05
    ["amount0Out", "amount1Out", "to", "data"] [uint256, uint256, legacyAddr, ABIType.bytes]
      I.calldata = none
  have htlen : I.calldata.toList.length = I.calldata.size := by
    rw [byteArray_toList_eq, Array.length_toList]
    rfl
  unfold decodeCalldataWithMode decodeCalldata
  rw [if_neg (by rw [htlen]; omega : ¬ I.calldata.toList.length < 4)]
  by_cases hdyn :
      [uint256, uint256, legacyAddr, ABIType.bytes].any isDynamicABIType = true ∧
        2 ^ 255 ≤ I.calldata.toList.length
  all_goals
    first | rw [if_pos hdyn] | rw [if_neg hdyn]
    change (match decodeCalldata.decodeArgs DecodeMode.legacySolc05
        ["amount0Out", "amount1Out", "to", "data"]
        [uint256, uint256, legacyAddr, ABIType.bytes] (I.calldata.toList.drop 4) ∅ with
      | some (store, _) => some store
      | none => none) = none
    unfold decodeCalldata.decodeArgs
    rw [show abiTupleHeadSize? [uint256, uint256, legacyAddr, ABIType.bytes] = some 128 by
      native_decide]
    simp only [bind, Option.bind]
    rw [if_pos (by
      rw [List.length_drop, htlen]
      omega : (I.calldata.toList.drop 4).length < 128)]

theorem swapDecodeABIValues_none_offset_huge {I : ExecutionEnv}
    (hsz132 : 132 ≤ I.calldata.size) (hoff : solcLegacyMaxU32 < swapDataOffset I) :
    decodeABIValues? [uint256, uint256, legacyAddr, ABIType.bytes]
      (I.calldata.toList.drop 4) 0 0 128 128 DecodeMode.legacySolc05 = none := by
  have htlen : I.calldata.toList.length = I.calldata.size := by
    rw [byteArray_toList_eq, Array.length_toList]
    rfl
  have htake0 : (((I.calldata.toList.drop 4).drop 0).take 32).length = 32 := by
    rw [List.drop_zero, List.length_take, List.length_drop, htlen]
    omega
  have htake32 : (((I.calldata.toList.drop 4).drop 32).take 32).length = 32 := by
    rw [List.length_take, List.length_drop, List.length_drop, htlen]
    omega
  have htake64 : (((I.calldata.toList.drop 4).drop 64).take 32).length = 32 := by
    rw [List.length_take, List.length_drop, List.length_drop, htlen]
    omega
  have hdec0 : decodeABIValue? uint256 (I.calldata.toList.drop 4) 0
      DecodeMode.legacySolc05 = some (.int (Int.ofNat
        (ABI.bytesToWord ((I.calldata.toList.drop 4).take 32)).toNat), 0 + 32) := by
    simpa [List.drop_zero] using
      swapDecodeABIValue_uint256_legacy_ok (bytes := I.calldata.toList.drop 4)
        (start := 0) htake0
  have hdec32 : decodeABIValue? uint256 (I.calldata.toList.drop 4) 32
      DecodeMode.legacySolc05 = some (.int (Int.ofNat
        (ABI.bytesToWord (((I.calldata.toList.drop 4).drop 32).take 32)).toNat), 32 + 32) := by
    exact swapDecodeABIValue_uint256_legacy_ok (bytes := I.calldata.toList.drop 4)
      (start := 32) htake32
  have hdec64 : decodeABIValue? legacyAddr (I.calldata.toList.drop 4) 64
      DecodeMode.legacySolc05 = some (.address (AccountAddress.ofNat
        (ABI.bytesToWord (((I.calldata.toList.drop 4).drop 64).take 32)).toNat),
        64 + 32) := by
    exact swapDecodeABIValue_legacyAddress_ok (bytes := I.calldata.toList.drop 4)
      (start := 64) htake64
  have hreadOff : readNat? (I.calldata.toList.drop 4) 96 = some (swapDataOffset I) := by
    simpa [swapDataOffset, swapDataOffsetWord] using
      swapReadNat_drop4_eq_calldataWord (I := I) (headOff := 96) (by omega)
  have hoff' : ABI.solcMaxLen DecodeMode.legacySolc05 < swapDataOffset I := by
    simpa [solcMaxLen_legacySolc05] using hoff
  have hdec0r : decodeABIValue? (.elem (.int (.uint ⟨256, by decide⟩)))
      (I.calldata.toList.drop 4) 0 DecodeMode.legacySolc05 =
      some (.int (Int.ofNat (ABI.bytesToWord ((I.calldata.toList.drop 4).take 32)).toNat),
        0 + 32) := by
    simpa [uint256, uint256Int] using hdec0
  have hdec32r : decodeABIValue? (.elem (.int (.uint ⟨256, by decide⟩)))
      (I.calldata.toList.drop 4) 32 DecodeMode.legacySolc05 =
      some (.int (Int.ofNat
        (ABI.bytesToWord (((I.calldata.toList.drop 4).drop 32).take 32)).toNat), 32 + 32) := by
    simpa [uint256, uint256Int] using hdec32
  have hdec64r : decodeABIValue? (.elem .address) (I.calldata.toList.drop 4) 64
      DecodeMode.legacySolc05 = some (.address (AccountAddress.ofNat
        (ABI.bytesToWord (((I.calldata.toList.drop 4).drop 64).take 32)).toNat), 64 + 32) := by
    simpa [legacyAddr, addr] using hdec64
  simp [decodeABIValues?, uint256, uint256Int, legacyAddr, addr, isDynamicABIType,
    staticABIEncodedSize?, hdec0r, hdec32r, hdec64r, hreadOff, hoff']

theorem swapDecodeABIValue_bytes_none_length_short {I : ExecutionEnv}
    (hshort : I.calldata.size < 4 + swapDataOffset I + 32) :
    decodeABIValue? ABIType.bytes (I.calldata.toList.drop 4) (swapDataOffset I)
      DecodeMode.legacySolc05 = none := by
  have htlen : I.calldata.toList.length = I.calldata.size := by
    rw [byteArray_toList_eq, Array.length_toList]
    rfl
  have hreadLen : readNat? (I.calldata.toList.drop 4) (swapDataOffset I) = none := by
    unfold readNat? readWord? readBytes?
    have hlen :
        ¬ (((I.calldata.toList.drop 4).drop (swapDataOffset I)).take 32).length = 32 := by
      rw [List.length_take, List.length_drop, List.length_drop, htlen]
      omega
    rw [if_neg hlen]
    simp
  simp [decodeABIValue?, hreadLen]

theorem swapDecodeABIValue_bytes_none_length_huge {I : ExecutionEnv}
    (hlenWord : 4 + swapDataOffset I + 32 ≤ I.calldata.size)
    (hlenHuge : solcLegacyMaxU32 < swapDataSize I) :
    decodeABIValue? ABIType.bytes (I.calldata.toList.drop 4) (swapDataOffset I)
      DecodeMode.legacySolc05 = none := by
  have hreadLen := swapReadNat_drop4_eq_calldataWord (I := I)
    (headOff := swapDataOffset I) hlenWord
  have hlenHuge' :
      ABI.solcMaxLen DecodeMode.legacySolc05 <
        (calldataWord I.calldata (4 + (swapDataOffsetWord I).toNat)).toNat := by
    simpa [solcMaxLen_legacySolc05, swapDataSize, swapDataSizeWord,
      swapDataOffset] using hlenHuge
  simp [decodeABIValue?, hreadLen, hlenHuge', swapDataOffset]

theorem swapDecodeABIValue_bytes_none_payload_short {I : ExecutionEnv}
    (hlenWord : 4 + swapDataOffset I + 32 ≤ I.calldata.size)
    (hlenMax : ¬ solcLegacyMaxU32 < swapDataSize I)
    (hpayload : (((I.calldata.toList.drop 4).drop (swapDataOffset I + 32)).take
      (swapDataSize I)).length ≠ swapDataSize I) :
    decodeABIValue? ABIType.bytes (I.calldata.toList.drop 4) (swapDataOffset I)
      DecodeMode.legacySolc05 = none := by
  have hreadLen := swapReadNat_drop4_eq_calldataWord (I := I)
    (headOff := swapDataOffset I) hlenWord
  have hpayloadRead :
      readBytes? (I.calldata.toList.drop 4) (swapDataOffset I + 32) (swapDataSize I) =
        none := by
    unfold readBytes?
    rw [if_neg hpayload]
  have hlenMax' :
      ¬ ABI.solcMaxLen DecodeMode.legacySolc05 <
        (calldataWord I.calldata (4 + (swapDataOffsetWord I).toNat)).toNat := by
    simpa [solcMaxLen_legacySolc05, swapDataSize, swapDataSizeWord,
      swapDataOffset] using hlenMax
  simp [decodeABIValue?, hreadLen, hlenMax', hpayloadRead, swapDataOffset]

theorem swapDecodeABIValues_none_data {I : ExecutionEnv} (hsz132 : 132 ≤ I.calldata.size)
    (_hoffMax : ¬ solcLegacyMaxU32 < swapDataOffset I)
    (hdecData : decodeABIValue? ABIType.bytes (I.calldata.toList.drop 4) (swapDataOffset I)
      DecodeMode.legacySolc05 = none) :
    decodeABIValues? [uint256, uint256, legacyAddr, ABIType.bytes]
      (I.calldata.toList.drop 4) 0 0 128 128 DecodeMode.legacySolc05 = none := by
  have htlen : I.calldata.toList.length = I.calldata.size := by
    rw [byteArray_toList_eq, Array.length_toList]
    rfl
  have htake0 : (((I.calldata.toList.drop 4).drop 0).take 32).length = 32 := by
    rw [List.drop_zero, List.length_take, List.length_drop, htlen]
    omega
  have htake32 : (((I.calldata.toList.drop 4).drop 32).take 32).length = 32 := by
    rw [List.length_take, List.length_drop, List.length_drop, htlen]
    omega
  have htake64 : (((I.calldata.toList.drop 4).drop 64).take 32).length = 32 := by
    rw [List.length_take, List.length_drop, List.length_drop, htlen]
    omega
  have hdec0 : decodeABIValue? uint256 (I.calldata.toList.drop 4) 0
      DecodeMode.legacySolc05 = some (.int (Int.ofNat
        (ABI.bytesToWord ((I.calldata.toList.drop 4).take 32)).toNat), 0 + 32) := by
    simpa [List.drop_zero] using
      swapDecodeABIValue_uint256_legacy_ok (bytes := I.calldata.toList.drop 4)
        (start := 0) htake0
  have hdec32 : decodeABIValue? uint256 (I.calldata.toList.drop 4) 32
      DecodeMode.legacySolc05 = some (.int (Int.ofNat
        (ABI.bytesToWord (((I.calldata.toList.drop 4).drop 32).take 32)).toNat), 32 + 32) := by
    exact swapDecodeABIValue_uint256_legacy_ok (bytes := I.calldata.toList.drop 4)
      (start := 32) htake32
  have hdec64 : decodeABIValue? legacyAddr (I.calldata.toList.drop 4) 64
      DecodeMode.legacySolc05 = some (.address (AccountAddress.ofNat
        (ABI.bytesToWord (((I.calldata.toList.drop 4).drop 64).take 32)).toNat),
        64 + 32) := by
    exact swapDecodeABIValue_legacyAddress_ok (bytes := I.calldata.toList.drop 4)
      (start := 64) htake64
  have hreadOff : readNat? (I.calldata.toList.drop 4) 96 = some (swapDataOffset I) := by
    simpa [swapDataOffset, swapDataOffsetWord] using
      swapReadNat_drop4_eq_calldataWord (I := I) (headOff := 96) (by omega)
  have hdec0r : decodeABIValue? (.elem (.int (.uint ⟨256, by decide⟩)))
      (I.calldata.toList.drop 4) 0 DecodeMode.legacySolc05 =
      some (.int (Int.ofNat (ABI.bytesToWord ((I.calldata.toList.drop 4).take 32)).toNat),
        0 + 32) := by
    simpa [uint256, uint256Int] using hdec0
  have hdec32r : decodeABIValue? (.elem (.int (.uint ⟨256, by decide⟩)))
      (I.calldata.toList.drop 4) 32 DecodeMode.legacySolc05 =
      some (.int (Int.ofNat
        (ABI.bytesToWord (((I.calldata.toList.drop 4).drop 32).take 32)).toNat), 32 + 32) := by
    simpa [uint256, uint256Int] using hdec32
  have hdec64r : decodeABIValue? (.elem .address) (I.calldata.toList.drop 4) 64
      DecodeMode.legacySolc05 = some (.address (AccountAddress.ofNat
        (ABI.bytesToWord (((I.calldata.toList.drop 4).drop 64).take 32)).toNat), 64 + 32) := by
    simpa [legacyAddr, addr] using hdec64
  simp [decodeABIValues?, uint256, uint256Int, legacyAddr, addr, isDynamicABIType,
    staticABIEncodedSize?, hdec0r, hdec32r, hdec64r, hreadOff, hdecData]

theorem uniswapDecode_swap_none_of_values_none {I : ExecutionEnv}
    (hsz132 : 132 ≤ I.calldata.size)
    (hvals : decodeABIValues? [uint256, uint256, legacyAddr, ABIType.bytes]
      (I.calldata.toList.drop 4) 0 0 128 128 DecodeMode.legacySolc05 = none) :
    decodeCalldataWithMode config.abiDecodeMode (swapTransition.params.map Param.name)
      (transitionSignature swapTransition).paramTypes I.calldata = none := by
  show decodeCalldataWithMode DecodeMode.legacySolc05
    ["amount0Out", "amount1Out", "to", "data"] [uint256, uint256, legacyAddr, ABIType.bytes]
      I.calldata = none
  have htlen : I.calldata.toList.length = I.calldata.size := by
    rw [byteArray_toList_eq, Array.length_toList]
    rfl
  unfold decodeCalldataWithMode decodeCalldata
  rw [if_neg (by rw [htlen]; omega : ¬ I.calldata.toList.length < 4)]
  by_cases hdyn :
      [uint256, uint256, legacyAddr, ABIType.bytes].any isDynamicABIType = true ∧
        2 ^ 255 ≤ I.calldata.toList.length
  all_goals
    first | rw [if_pos hdyn] | rw [if_neg hdyn]
    change (match decodeCalldata.decodeArgs DecodeMode.legacySolc05
        ["amount0Out", "amount1Out", "to", "data"]
        [uint256, uint256, legacyAddr, ABIType.bytes] (I.calldata.toList.drop 4) ∅ with
      | some (store, _) => some store
      | none => none) = none
    unfold decodeCalldata.decodeArgs
    rw [show abiTupleHeadSize? [uint256, uint256, legacyAddr, ABIType.bytes] = some 128 by
      native_decide]
    simp only [bind, Option.bind]
    rw [if_neg (by
      rw [List.length_drop, htlen]
      omega : ¬ (I.calldata.toList.drop 4).length < 128)]
    rw [hvals]

theorem uniswapDecode_swap_none_offset_huge {I : ExecutionEnv}
    (hsz132 : 132 ≤ I.calldata.size) (hoff : solcLegacyMaxU32 < swapDataOffset I) :
    decodeCalldataWithMode config.abiDecodeMode (swapTransition.params.map Param.name)
      (transitionSignature swapTransition).paramTypes I.calldata = none :=
  uniswapDecode_swap_none_of_values_none hsz132
    (swapDecodeABIValues_none_offset_huge (I := I) hsz132 hoff)

theorem uniswapDecode_swap_none_length_short {I : ExecutionEnv}
    (hsz132 : 132 ≤ I.calldata.size) (hoffMax : ¬ solcLegacyMaxU32 < swapDataOffset I)
    (hshort : I.calldata.size < 4 + swapDataOffset I + 32) :
    decodeCalldataWithMode config.abiDecodeMode (swapTransition.params.map Param.name)
      (transitionSignature swapTransition).paramTypes I.calldata = none :=
  uniswapDecode_swap_none_of_values_none hsz132
    (swapDecodeABIValues_none_data (I := I) hsz132 hoffMax
      (swapDecodeABIValue_bytes_none_length_short (I := I) hshort))

theorem uniswapDecode_swap_none_length_huge {I : ExecutionEnv}
    (hsz132 : 132 ≤ I.calldata.size) (hoffMax : ¬ solcLegacyMaxU32 < swapDataOffset I)
    (hlenWord : 4 + swapDataOffset I + 32 ≤ I.calldata.size)
    (hlenHuge : solcLegacyMaxU32 < swapDataSize I) :
    decodeCalldataWithMode config.abiDecodeMode (swapTransition.params.map Param.name)
      (transitionSignature swapTransition).paramTypes I.calldata = none :=
  uniswapDecode_swap_none_of_values_none hsz132
    (swapDecodeABIValues_none_data (I := I) hsz132 hoffMax
      (swapDecodeABIValue_bytes_none_length_huge (I := I) hlenWord hlenHuge))

theorem uniswapDecode_swap_none_payload_short {I : ExecutionEnv}
    (hsz132 : 132 ≤ I.calldata.size) (hoffMax : ¬ solcLegacyMaxU32 < swapDataOffset I)
    (hlenWord : 4 + swapDataOffset I + 32 ≤ I.calldata.size)
    (hlenMax : ¬ solcLegacyMaxU32 < swapDataSize I)
    (hpayload : (((I.calldata.toList.drop 4).drop (swapDataOffset I + 32)).take
      (swapDataSize I)).length ≠ swapDataSize I) :
    decodeCalldataWithMode config.abiDecodeMode (swapTransition.params.map Param.name)
      (transitionSignature swapTransition).paramTypes I.calldata = none :=
  uniswapDecode_swap_none_of_values_none hsz132
    (swapDecodeABIValues_none_data (I := I) hsz132 hoffMax
      (swapDecodeABIValue_bytes_none_payload_short (I := I) hlenWord hlenMax hpayload))

theorem swapU256_lor_one_ne_zero_left (w : UInt256) :
    UInt256.lor ⟨1⟩ w ≠ ⟨0⟩ := by
  intro h
  have hval : (UInt256.lor ⟨1⟩ w).toNat = 0 := by
    simpa using congrArg UInt256.toNat h
  rw [u256_lor_toNat] at hval
  change Nat.lor 1 w.toNat % UInt256.size = 0 at hval
  have hlt : Nat.lor 1 w.toNat < UInt256.size := by
    have hw : w.toNat < 2 ^ 256 := by
      simp [UInt256.toNat, UInt256.size]
    simpa [UInt256.size] using Nat.or_lt_two_pow (by norm_num : 1 < 2 ^ 256) hw
  rw [Nat.mod_eq_of_lt hlt] at hval
  have hbitTrue : Nat.testBit (Nat.lor 1 w.toNat) 0 = true := by
    change Nat.testBit (1 ||| w.toNat) 0 = true
    rw [Nat.testBit_lor]
    norm_num
  rw [hval] at hbitTrue
  simp at hbitTrue

theorem swapU256_lor_one_ne_zero_right (w : UInt256) :
    UInt256.lor w ⟨1⟩ ≠ ⟨0⟩ := by
  rw [u256_lor_comm]
  exact swapU256_lor_one_ne_zero_left w

theorem swapPayloadShort_lt {I : ExecutionEnv}
    (hpayload : (((I.calldata.toList.drop 4).drop (swapDataOffset I + 32)).take
      (swapDataSize I)).length ≠ swapDataSize I) :
    I.calldata.size < 4 + swapDataOffset I + 32 + swapDataSize I := by
  by_contra hnot
  have htlen : I.calldata.toList.length = I.calldata.size := by
    rw [byteArray_toList_eq, Array.length_toList]
    rfl
  have htake :
      (((I.calldata.toList.drop 4).drop (swapDataOffset I + 32)).take
        (swapDataSize I)).length = swapDataSize I := by
    rw [List.length_take, List.length_drop, List.length_drop, htlen]
    rw [min_eq_left]
    omega
  exact hpayload htake

theorem swapPayloadPresent_le {I : ExecutionEnv}
    (hlenWord : 4 + swapDataOffset I + 32 ≤ I.calldata.size)
    (hpayload : (((I.calldata.toList.drop 4).drop (swapDataOffset I + 32)).take
      (swapDataSize I)).length = swapDataSize I) :
    4 + swapDataOffset I + 32 + swapDataSize I ≤ I.calldata.size := by
  have htlen : I.calldata.toList.length = I.calldata.size := by
    rw [byteArray_toList_eq, Array.length_toList]
    rfl
  have hlenDrop :
      (I.calldata.toList.drop 4).length = I.calldata.size - 4 := by
    rw [List.length_drop, htlen]
  have hdropLen :
      ((I.calldata.toList.drop 4).drop (swapDataOffset I + 32)).length =
        I.calldata.size - 4 - (swapDataOffset I + 32) := by
    rw [List.length_drop, hlenDrop]
  have htakeLen :
      (((I.calldata.toList.drop 4).drop (swapDataOffset I + 32)).take
        (swapDataSize I)).length =
        min (swapDataSize I) (I.calldata.size - 4 - (swapDataOffset I + 32)) := by
    rw [List.length_take, hdropLen]
  rw [htakeLen] at hpayload
  have hle : swapDataSize I ≤ I.calldata.size - 4 - (swapDataOffset I + 32) := by
    have hmin :
        min (swapDataSize I) (I.calldata.size - 4 - (swapDataOffset I + 32)) ≤
          I.calldata.size - 4 - (swapDataOffset I + 32) :=
      Nat.min_le_right _ _
    rwa [hpayload] at hmin
  omega

end UniswapV2Pair
