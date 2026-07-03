import Examples.UniswapV2Pair.MutatorDispatch
import Reasoning.Refinement

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach Reasoning.Refinement

set_option maxRecDepth 2000000
set_option maxHeartbeats 2000000

namespace UniswapV2Pair

/-! ## `swap(uint256,uint256,address,bytes)` source slice -/

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
  simp [decodeABIValue?, hreadLen, hlenMax, hpayloadRead, swapDataValue, swapDataBytes,
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
  simp [decodeABIValues?, uint256, uint256Int, legacyAddr, addr, isDynamicABIType,
    staticABIEncodedSize?, hdec0r, hdec32r, hdec64r, hreadOff, hoffMax, hdecData, hword4,
    hword36', hword68', swapAmount0OutValue, swapAmount1OutValue, swapToValue]
  all_goals omega

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
  rw [if_neg (by simp [calldataDynamicGuard])]
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
  rw [if_neg (by simp [calldataDynamicGuard])]
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
    staticABIEncodedSize?, hdec0r, hdec32r, hdec64r, hreadOff, hoff]

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
  simp [decodeABIValue?, hreadLen, hlenHuge, swapDataOffset]

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
  simp [decodeABIValue?, hreadLen, hlenMax, hpayloadRead, swapDataOffset]

theorem swapDecodeABIValues_none_data {I : ExecutionEnv} (hsz132 : 132 ≤ I.calldata.size)
    (hoffMax : ¬ solcLegacyMaxU32 < swapDataOffset I)
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
    staticABIEncodedSize?, hdec0r, hdec32r, hdec64r, hreadOff, hoffMax, hdecData]

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
  rw [if_neg (by simp [calldataDynamicGuard])]
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

theorem uniswapSwapX_shortHead {cA gh bl σ σ₀ A I} {g : Sat256} {sel : UInt256}
    (hsz4 : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hshort : I.calldata.size < 132)
    (hreach : ∃ k C, RD uniswapV2PairBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨430⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    RDrev uniswapV2PairBytecode g (initState cA gh bl σ σ₀ g A I) := by
  have hlt :
      UInt256.lt (UInt256.sub (UInt256.ofNat I.calldata.size) ⟨4⟩) ⟨128⟩ = ⟨1⟩ := by
    apply ult_one
    rw [show (⟨128⟩ : UInt256).toNat = 128 from by decide,
      usub_ofNat_word_toNat (c := (⟨4⟩ : UInt256)) (by simpa using hsz4) hsize,
      show (⟨4⟩ : UInt256).toNat = 4 from by decide]
    omega
  exact RD.solcExternalStaticArgsShortReverts
    (code := uniswapV2PairBytecode) (entry := ⟨430⟩) (ret := ⟨570⟩)
    (decoded := ⟨452⟩) (need := ⟨128⟩)
    hreach
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) hlt

theorem uniswapSwapX_offsetHuge {cA gh bl σ σ₀ A I} {g : Sat256} {sel : UInt256}
    (hsize : I.calldata.size < UInt256.size) (hsz132 : 132 ≤ I.calldata.size)
    (hoff : solcLegacyMaxU32 < swapDataOffset I)
    (hreach : ∃ k C, RD uniswapV2PairBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨430⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    RDrev uniswapV2PairBytecode g (initState cA gh bl σ σ₀ g A I) := by
  have hlt :
      UInt256.lt (UInt256.sub (UInt256.ofNat I.calldata.size) ⟨4⟩) ⟨128⟩ = ⟨0⟩ := by
    exact solcDecodeLenCheckOkUnsigned (by simpa using hsz132) hsize
  obtain ⟨_, _, rd452⟩ := RD.solcExternalStaticArgsLenOk
    (code := uniswapV2PairBytecode) (entry := ⟨430⟩) (ret := ⟨570⟩)
    (decoded := ⟨452⟩) (need := ⟨128⟩)
    hreach
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) hlt
  have rd490 := evm_run rd452 with [
    jumpdest, dup2, calldataload, swap2, push1 ⟨32⟩, dup2, add, calldataload,
    swap2, push1 ⟨1⟩, push1 ⟨1⟩, push1 ⟨160⟩, shl, sub, push1 ⟨64⟩,
    dup4, add, calldataload, and, swap2, swap1, dup2, add, swap1, push1 ⟨128⟩,
    dup2, add, push1 ⟨96⟩, dup3, add, calldataload]
  have hgt :
      UInt256.gt
        (uInt256OfByteArray (I.calldata.readBytes ((⟨4⟩ : UInt256) + ⟨96⟩).toNat 32))
        ⟨4294967296⟩ = ⟨1⟩ := by
    apply ugt_one
    rw [show (⟨4294967296⟩ : UInt256).toNat = 4294967296 from by decide]
    have hoff' : 4294967296 < swapDataOffset I := by
      simpa [solcLegacyMaxU32] using hoff
    simpa [swapDataOffset, swapDataOffsetWord, calldataWord,
      show (((⟨4⟩ : UInt256) + ⟨96⟩).toNat) = 100 from by decide] using hoff'
  have rd496 := rd490.pushConst ⟨4294967296⟩ (width := 5) (op := .PUSH5)
    (by decide) (by native_decide) (by evm_ov)
  have rd497 := rd496.dup2 (by native_decide) (by evm_ov)
  have rd498₀ := rd497.gt (by native_decide) (by evm_ov)
  have rd498 := rd498₀
  rw [hgt] at rd498
  have rd499₀ := rd498.iszero (by native_decide) (by evm_ov)
  have rd499 := rd499₀
  rw [show UInt256.isZero (⟨1⟩ : UInt256) = ⟨0⟩ from by decide] at rd499
  have rd502 := rd499.push2 ⟨507⟩ (by native_decide) (by evm_ov)
  have rd503 := rd502.jumpiNT (by native_decide) (by decide : (⟨0⟩ : UInt256) = ⟨0⟩)
    (by evm_ov)
  have rd505 := rd503.push1 ⟨0⟩ (by native_decide) (by evm_ov)
  have rd506 := rd505.dup1 (by native_decide) (by evm_ov)
  exact rd506.rev 0 (by native_decide) mem_cost (by evm_ov)

theorem uniswapSwapX_lengthShort {cA gh bl σ σ₀ A I} {g : Sat256} {sel : UInt256}
    (hsize : I.calldata.size < UInt256.size) (hsz132 : 132 ≤ I.calldata.size)
    (hoffMax : ¬ solcLegacyMaxU32 < swapDataOffset I)
    (hlenShort : I.calldata.size < 4 + swapDataOffset I + 32)
    (hreach : ∃ k C, RD uniswapV2PairBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨430⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    RDrev uniswapV2PairBytecode g (initState cA gh bl σ σ₀ g A I) := by
  have hlt :
      UInt256.lt (UInt256.sub (UInt256.ofNat I.calldata.size) ⟨4⟩) ⟨128⟩ = ⟨0⟩ := by
    exact solcDecodeLenCheckOkUnsigned (by simpa using hsz132) hsize
  obtain ⟨_, _, rd452⟩ := RD.solcExternalStaticArgsLenOk
    (code := uniswapV2PairBytecode) (entry := ⟨430⟩) (ret := ⟨570⟩)
    (decoded := ⟨452⟩) (need := ⟨128⟩)
    hreach
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) hlt
  have rd490 := evm_run rd452 with [
    jumpdest, dup2, calldataload, swap2, push1 ⟨32⟩, dup2, add, calldataload,
    swap2, push1 ⟨1⟩, push1 ⟨1⟩, push1 ⟨160⟩, shl, sub, push1 ⟨64⟩,
    dup4, add, calldataload, and, swap2, swap1, dup2, add, swap1, push1 ⟨128⟩,
    dup2, add, push1 ⟨96⟩, dup3, add, calldataload]
  have hoffPass :
      UInt256.gt
        (uInt256OfByteArray (I.calldata.readBytes ((⟨4⟩ : UInt256) + ⟨96⟩).toNat 32))
        ⟨4294967296⟩ = ⟨0⟩ := by
    apply ugt_zero
    rw [show (⟨4294967296⟩ : UInt256).toNat = 4294967296 from by decide]
    have hoffLe : swapDataOffset I ≤ 4294967296 := by
      have : ¬ 4294967296 < swapDataOffset I := by
        simpa [solcLegacyMaxU32] using hoffMax
      omega
    simpa [swapDataOffset, swapDataOffsetWord, calldataWord,
      show (((⟨4⟩ : UInt256) + ⟨96⟩).toNat) = 100 from by decide] using hoffLe
  have rd496 := rd490.pushConst ⟨4294967296⟩ (width := 5) (op := .PUSH5)
    (by decide) (by native_decide) (by evm_ov)
  have rd497 := rd496.dup2 (by native_decide) (by evm_ov)
  have rd498₀ := rd497.gt (by native_decide) (by evm_ov)
  have rd498 := rd498₀
  rw [hoffPass] at rd498
  have rd499₀ := rd498.iszero (by native_decide) (by evm_ov)
  have rd499 := rd499₀
  rw [show UInt256.isZero (⟨0⟩ : UInt256) = ⟨1⟩ from by decide] at rd499
  have rd502 := rd499.push2 ⟨507⟩ (by native_decide) (by evm_ov)
  have rd507 := rd502.jumpiT (by native_decide) (by decide : (⟨1⟩ : UInt256) ≠ ⟨0⟩)
    (by native_decide) (by evm_ov)
  have rd516 := evm_run rd507 with [
    jumpdest, dup3, add, dup4, push1 ⟨32⟩, dup3, add, gt]
  have hgtLen :
      UInt256.gt
        (((⟨4⟩ : UInt256) +
            uInt256OfByteArray (I.calldata.readBytes ((⟨4⟩ : UInt256) + ⟨96⟩).toNat 32)) +
          ⟨32⟩)
        ((⟨4⟩ : UInt256) + UInt256.sub (UInt256.ofNat I.calldata.size) ⟨4⟩) =
        ⟨1⟩ := by
    apply ugt_one
    have hoffWord :
        (uInt256OfByteArray
          (I.calldata.readBytes ((⟨4⟩ : UInt256) + ⟨96⟩).toNat 32)).toNat =
          swapDataOffset I := by
      simp [swapDataOffset, swapDataOffsetWord, calldataWord,
        show (((⟨4⟩ : UInt256) + ⟨96⟩).toNat) = 100 from by decide]
    have hoffLe : swapDataOffset I ≤ 4294967296 := by
      have : ¬ 4294967296 < swapDataOffset I := by
        simpa [solcLegacyMaxU32] using hoffMax
      omega
    have hleft1 :
        (((⟨4⟩ : UInt256) +
          uInt256OfByteArray
            (I.calldata.readBytes ((⟨4⟩ : UInt256) + ⟨96⟩).toNat 32)).toNat) =
          4 + swapDataOffset I := by
      rw [uadd_toNat, show (⟨4⟩ : UInt256).toNat = 4 from by decide, hoffWord]
      rw [Nat.mod_eq_of_lt]
      have hcap : 4 + 4294967296 < UInt256.size := by norm_num [UInt256.size]
      omega
    have hleft :
        ((((⟨4⟩ : UInt256) +
            uInt256OfByteArray
              (I.calldata.readBytes ((⟨4⟩ : UInt256) + ⟨96⟩).toNat 32)) +
          ⟨32⟩).toNat) = 4 + swapDataOffset I + 32 := by
      rw [uadd_toNat, hleft1, show (⟨32⟩ : UInt256).toNat = 32 from by decide]
      rw [Nat.mod_eq_of_lt]
      have hcap : 4 + 4294967296 + 32 < UInt256.size := by norm_num [UInt256.size]
      omega
    have hright :
        (((⟨4⟩ : UInt256) + UInt256.sub (UInt256.ofNat I.calldata.size) ⟨4⟩).toNat) =
          I.calldata.size := by
      have hword :
          (⟨4⟩ : UInt256) + UInt256.sub (UInt256.ofNat I.calldata.size) ⟨4⟩ =
            UInt256.ofNat I.calldata.size :=
        uadd_word_usub_ofNat_word (n := I.calldata.size) (c := (⟨4⟩ : UInt256))
          (by
            rw [show ((⟨4⟩ : UInt256).toNat) = 4 from by decide]
            omega)
          hsize
      rw [hword, ulit_toNat' I.calldata.size hsize]
    rw [hleft, hright]
    exact hlenShort
  have rd516' := rd516
  rw [hgtLen] at rd516'
  have rd517₀ := rd516'.iszero (by native_decide) (by evm_ov)
  have rd517 := rd517₀
  rw [show UInt256.isZero (⟨1⟩ : UInt256) = ⟨0⟩ from by decide] at rd517
  have rd520 := rd517.push2 ⟨525⟩ (by native_decide) (by evm_ov)
  have rd521 := rd520.jumpiNT (by native_decide) (by decide : (⟨0⟩ : UInt256) = ⟨0⟩)
    (by evm_ov)
  have rd523 := rd521.push1 ⟨0⟩ (by native_decide) (by evm_ov)
  have rd524 := rd523.dup1 (by native_decide) (by evm_ov)
  exact rd524.rev 0 (by native_decide) mem_cost (by evm_ov)

private theorem swapU256_lor_one_ne_zero_left (w : UInt256) :
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

private theorem swapU256_lor_one_ne_zero_right (w : UInt256) :
    UInt256.lor w ⟨1⟩ ≠ ⟨0⟩ := by
  rw [u256_lor_comm]
  exact swapU256_lor_one_ne_zero_left w

private theorem swapPayloadShort_lt {I : ExecutionEnv}
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

theorem uniswapSwapX_lengthHuge {cA gh bl σ σ₀ A I} {g : Sat256} {sel : UInt256}
    (hsize : I.calldata.size < UInt256.size) (hsz132 : 132 ≤ I.calldata.size)
    (hoffMax : ¬ solcLegacyMaxU32 < swapDataOffset I)
    (hlenWord : 4 + swapDataOffset I + 32 ≤ I.calldata.size)
    (hlenHuge : solcLegacyMaxU32 < swapDataSize I)
    (hreach : ∃ k C, RD uniswapV2PairBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨430⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    RDrev uniswapV2PairBytecode g (initState cA gh bl σ σ₀ g A I) := by
  have hlt :
      UInt256.lt (UInt256.sub (UInt256.ofNat I.calldata.size) ⟨4⟩) ⟨128⟩ = ⟨0⟩ := by
    exact solcDecodeLenCheckOkUnsigned (by simpa using hsz132) hsize
  obtain ⟨_, _, rd452⟩ := RD.solcExternalStaticArgsLenOk
    (code := uniswapV2PairBytecode) (entry := ⟨430⟩) (ret := ⟨570⟩)
    (decoded := ⟨452⟩) (need := ⟨128⟩)
    hreach
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) hlt
  have rd490 := evm_run rd452 with [
    jumpdest, dup2, calldataload, swap2, push1 ⟨32⟩, dup2, add, calldataload,
    swap2, push1 ⟨1⟩, push1 ⟨1⟩, push1 ⟨160⟩, shl, sub, push1 ⟨64⟩,
    dup4, add, calldataload, and, swap2, swap1, dup2, add, swap1, push1 ⟨128⟩,
    dup2, add, push1 ⟨96⟩, dup3, add, calldataload]
  have hoffPass :
      UInt256.gt
        (uInt256OfByteArray (I.calldata.readBytes ((⟨4⟩ : UInt256) + ⟨96⟩).toNat 32))
        ⟨4294967296⟩ = ⟨0⟩ := by
    apply ugt_zero
    rw [show (⟨4294967296⟩ : UInt256).toNat = 4294967296 from by decide]
    have hoffLe : swapDataOffset I ≤ 4294967296 := by
      have : ¬ 4294967296 < swapDataOffset I := by
        simpa [solcLegacyMaxU32] using hoffMax
      omega
    simpa [swapDataOffset, swapDataOffsetWord, calldataWord,
      show (((⟨4⟩ : UInt256) + ⟨96⟩).toNat) = 100 from by decide] using hoffLe
  have rd496 := rd490.pushConst ⟨4294967296⟩ (width := 5) (op := .PUSH5)
    (by decide) (by native_decide) (by evm_ov)
  have rd497 := rd496.dup2 (by native_decide) (by evm_ov)
  have rd498₀ := rd497.gt (by native_decide) (by evm_ov)
  have rd498 := rd498₀
  rw [hoffPass] at rd498
  have rd499₀ := rd498.iszero (by native_decide) (by evm_ov)
  have rd499 := rd499₀
  rw [show UInt256.isZero (⟨0⟩ : UInt256) = ⟨1⟩ from by decide] at rd499
  have rd502 := rd499.push2 ⟨507⟩ (by native_decide) (by evm_ov)
  have rd507 := rd502.jumpiT (by native_decide) (by decide : (⟨1⟩ : UInt256) ≠ ⟨0⟩)
    (by native_decide) (by evm_ov)
  have rd516 := evm_run rd507 with [
    jumpdest, dup3, add, dup4, push1 ⟨32⟩, dup3, add, gt]
  have hgtLen :
      UInt256.gt
        (((⟨4⟩ : UInt256) +
            uInt256OfByteArray (I.calldata.readBytes ((⟨4⟩ : UInt256) + ⟨96⟩).toNat 32)) +
          ⟨32⟩)
        ((⟨4⟩ : UInt256) + UInt256.sub (UInt256.ofNat I.calldata.size) ⟨4⟩) =
        ⟨0⟩ := by
    apply ugt_zero
    have hoffWord :
        (uInt256OfByteArray
          (I.calldata.readBytes ((⟨4⟩ : UInt256) + ⟨96⟩).toNat 32)).toNat =
          swapDataOffset I := by
      simp [swapDataOffset, swapDataOffsetWord, calldataWord,
        show (((⟨4⟩ : UInt256) + ⟨96⟩).toNat) = 100 from by decide]
    have hoffLe : swapDataOffset I ≤ 4294967296 := by
      have : ¬ 4294967296 < swapDataOffset I := by
        simpa [solcLegacyMaxU32] using hoffMax
      omega
    have hleft1 :
        (((⟨4⟩ : UInt256) +
          uInt256OfByteArray
            (I.calldata.readBytes ((⟨4⟩ : UInt256) + ⟨96⟩).toNat 32)).toNat) =
          4 + swapDataOffset I := by
      rw [uadd_toNat, show (⟨4⟩ : UInt256).toNat = 4 from by decide, hoffWord]
      rw [Nat.mod_eq_of_lt]
      have hcap : 4 + 4294967296 < UInt256.size := by norm_num [UInt256.size]
      omega
    have hleft :
        ((((⟨4⟩ : UInt256) +
            uInt256OfByteArray
              (I.calldata.readBytes ((⟨4⟩ : UInt256) + ⟨96⟩).toNat 32)) +
          ⟨32⟩).toNat) = 4 + swapDataOffset I + 32 := by
      rw [uadd_toNat, hleft1, show (⟨32⟩ : UInt256).toNat = 32 from by decide]
      rw [Nat.mod_eq_of_lt]
      have hcap : 4 + 4294967296 + 32 < UInt256.size := by norm_num [UInt256.size]
      omega
    have hright :
        (((⟨4⟩ : UInt256) + UInt256.sub (UInt256.ofNat I.calldata.size) ⟨4⟩).toNat) =
          I.calldata.size := by
      have hword :
          (⟨4⟩ : UInt256) + UInt256.sub (UInt256.ofNat I.calldata.size) ⟨4⟩ =
            UInt256.ofNat I.calldata.size :=
        uadd_word_usub_ofNat_word (n := I.calldata.size) (c := (⟨4⟩ : UInt256))
          (by
            rw [show ((⟨4⟩ : UInt256).toNat) = 4 from by decide]
            omega)
          hsize
      rw [hword, ulit_toNat' I.calldata.size hsize]
    rw [hleft, hright]
    exact hlenWord
  have rd516' := rd516
  rw [hgtLen] at rd516'
  have rd517₀ := rd516'.iszero (by native_decide) (by evm_ov)
  have rd517 := rd517₀
  rw [show UInt256.isZero (⟨0⟩ : UInt256) = ⟨1⟩ from by decide] at rd517
  have rd520 := rd517.push2 ⟨525⟩ (by native_decide) (by evm_ov)
  have rd525 := rd520.jumpiT (by native_decide) (by decide : (⟨1⟩ : UInt256) ≠ ⟨0⟩)
    (by native_decide) (by evm_ov)
  have rd540 := evm_run rd525 with [
    jumpdest, dup1, calldataload, swap1, push1 ⟨32⟩, add, swap2, dup5,
    push1 ⟨1⟩, dup4, mul, dup5, add, gt]
  have rd546 := rd540.pushConst ⟨4294967296⟩ (width := 5) (op := .PUSH5)
    (by decide) (by native_decide) (by evm_ov)
  have rd547 := rd546.dup4 (by native_decide) (by evm_ov)
  have rd548₀ := rd547.gt (by native_decide) (by evm_ov)
  have hgtHuge :
      UInt256.gt
        (uInt256OfByteArray
          (I.calldata.readBytes
            (((⟨4⟩ : UInt256) +
              uInt256OfByteArray
                (I.calldata.readBytes ((⟨4⟩ : UInt256) + ⟨96⟩).toNat 32)).toNat)
            32))
        ⟨4294967296⟩ = ⟨1⟩ := by
    apply ugt_one
    have hoffWord :
        (uInt256OfByteArray
          (I.calldata.readBytes ((⟨4⟩ : UInt256) + ⟨96⟩).toNat 32)).toNat =
          swapDataOffset I := by
      simp [swapDataOffset, swapDataOffsetWord, calldataWord,
        show (((⟨4⟩ : UInt256) + ⟨96⟩).toNat) = 100 from by decide]
    have hoffLe : swapDataOffset I ≤ 4294967296 := by
      have : ¬ 4294967296 < swapDataOffset I := by
        simpa [solcLegacyMaxU32] using hoffMax
      omega
    have hlenOffset :
        (((⟨4⟩ : UInt256) +
          uInt256OfByteArray
            (I.calldata.readBytes ((⟨4⟩ : UInt256) + ⟨96⟩).toNat 32)).toNat) =
          4 + swapDataOffset I := by
      rw [uadd_toNat, show (⟨4⟩ : UInt256).toNat = 4 from by decide, hoffWord]
      rw [Nat.mod_eq_of_lt]
      have hcap : 4 + 4294967296 < UInt256.size := by norm_num [UInt256.size]
      omega
    rw [show (⟨4294967296⟩ : UInt256).toNat = 4294967296 from by decide]
    have hread :
        (uInt256OfByteArray
          (I.calldata.readBytes
            (((⟨4⟩ : UInt256) +
              uInt256OfByteArray
                (I.calldata.readBytes ((⟨4⟩ : UInt256) + ⟨96⟩).toNat 32)).toNat)
            32)).toNat = swapDataSize I := by
      simp [swapDataSize, swapDataSizeWord, calldataWord, hlenOffset]
    rw [hread]
    simpa [solcLegacyMaxU32] using hlenHuge
  have rd548 := rd548₀
  rw [hgtHuge] at rd548
  have rd549 := RD.lor rd548 (by native_decide) (by evm_ov)
  have rd550₀ := rd549.iszero (by native_decide) (by evm_ov)
  have rd550 := rd550₀
  rw [isZero_eq_zero_of_ne (swapU256_lor_one_ne_zero_left _)] at rd550
  have rd553 := rd550.push2 ⟨559⟩ (by native_decide) (by evm_ov)
  have rd554 := rd553.jumpiNT (by native_decide) (by decide : (⟨0⟩ : UInt256) = ⟨0⟩)
    (by evm_ov)
  have rd556 := rd554.push1 ⟨0⟩ (by native_decide) (by evm_ov)
  have rd557 := rd556.dup1 (by native_decide) (by evm_ov)
  exact rd557.rev 0 (by native_decide) mem_cost (by evm_ov)

theorem uniswapSwapX_payloadShort {cA gh bl σ σ₀ A I} {g : Sat256} {sel : UInt256}
    (hsize : I.calldata.size < UInt256.size) (hsz132 : 132 ≤ I.calldata.size)
    (hoffMax : ¬ solcLegacyMaxU32 < swapDataOffset I)
    (hlenWord : 4 + swapDataOffset I + 32 ≤ I.calldata.size)
    (hlenMax : ¬ solcLegacyMaxU32 < swapDataSize I)
    (hpayload : (((I.calldata.toList.drop 4).drop (swapDataOffset I + 32)).take
      (swapDataSize I)).length ≠ swapDataSize I)
    (hreach : ∃ k C, RD uniswapV2PairBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨430⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    RDrev uniswapV2PairBytecode g (initState cA gh bl σ σ₀ g A I) := by
  have hlt :
      UInt256.lt (UInt256.sub (UInt256.ofNat I.calldata.size) ⟨4⟩) ⟨128⟩ = ⟨0⟩ := by
    exact solcDecodeLenCheckOkUnsigned (by simpa using hsz132) hsize
  obtain ⟨_, _, rd452⟩ := RD.solcExternalStaticArgsLenOk
    (code := uniswapV2PairBytecode) (entry := ⟨430⟩) (ret := ⟨570⟩)
    (decoded := ⟨452⟩) (need := ⟨128⟩)
    hreach
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) hlt
  have rd490 := evm_run rd452 with [
    jumpdest, dup2, calldataload, swap2, push1 ⟨32⟩, dup2, add, calldataload,
    swap2, push1 ⟨1⟩, push1 ⟨1⟩, push1 ⟨160⟩, shl, sub, push1 ⟨64⟩,
    dup4, add, calldataload, and, swap2, swap1, dup2, add, swap1, push1 ⟨128⟩,
    dup2, add, push1 ⟨96⟩, dup3, add, calldataload]
  have hoffPass :
      UInt256.gt
        (uInt256OfByteArray (I.calldata.readBytes ((⟨4⟩ : UInt256) + ⟨96⟩).toNat 32))
        ⟨4294967296⟩ = ⟨0⟩ := by
    apply ugt_zero
    rw [show (⟨4294967296⟩ : UInt256).toNat = 4294967296 from by decide]
    have hoffLe : swapDataOffset I ≤ 4294967296 := by
      have : ¬ 4294967296 < swapDataOffset I := by
        simpa [solcLegacyMaxU32] using hoffMax
      omega
    simpa [swapDataOffset, swapDataOffsetWord, calldataWord,
      show (((⟨4⟩ : UInt256) + ⟨96⟩).toNat) = 100 from by decide] using hoffLe
  have rd496 := rd490.pushConst ⟨4294967296⟩ (width := 5) (op := .PUSH5)
    (by decide) (by native_decide) (by evm_ov)
  have rd497 := rd496.dup2 (by native_decide) (by evm_ov)
  have rd498₀ := rd497.gt (by native_decide) (by evm_ov)
  have rd498 := rd498₀
  rw [hoffPass] at rd498
  have rd499₀ := rd498.iszero (by native_decide) (by evm_ov)
  have rd499 := rd499₀
  rw [show UInt256.isZero (⟨0⟩ : UInt256) = ⟨1⟩ from by decide] at rd499
  have rd502 := rd499.push2 ⟨507⟩ (by native_decide) (by evm_ov)
  have rd507 := rd502.jumpiT (by native_decide) (by decide : (⟨1⟩ : UInt256) ≠ ⟨0⟩)
    (by native_decide) (by evm_ov)
  have rd516 := evm_run rd507 with [
    jumpdest, dup3, add, dup4, push1 ⟨32⟩, dup3, add, gt]
  have hgtLen :
      UInt256.gt
        (((⟨4⟩ : UInt256) +
            uInt256OfByteArray (I.calldata.readBytes ((⟨4⟩ : UInt256) + ⟨96⟩).toNat 32)) +
          ⟨32⟩)
        ((⟨4⟩ : UInt256) + UInt256.sub (UInt256.ofNat I.calldata.size) ⟨4⟩) =
        ⟨0⟩ := by
    apply ugt_zero
    have hoffWord :
        (uInt256OfByteArray
          (I.calldata.readBytes ((⟨4⟩ : UInt256) + ⟨96⟩).toNat 32)).toNat =
          swapDataOffset I := by
      simp [swapDataOffset, swapDataOffsetWord, calldataWord,
        show (((⟨4⟩ : UInt256) + ⟨96⟩).toNat) = 100 from by decide]
    have hoffLe : swapDataOffset I ≤ 4294967296 := by
      have : ¬ 4294967296 < swapDataOffset I := by
        simpa [solcLegacyMaxU32] using hoffMax
      omega
    have hleft1 :
        (((⟨4⟩ : UInt256) +
          uInt256OfByteArray
            (I.calldata.readBytes ((⟨4⟩ : UInt256) + ⟨96⟩).toNat 32)).toNat) =
          4 + swapDataOffset I := by
      rw [uadd_toNat, show (⟨4⟩ : UInt256).toNat = 4 from by decide, hoffWord]
      rw [Nat.mod_eq_of_lt]
      have hcap : 4 + 4294967296 < UInt256.size := by norm_num [UInt256.size]
      omega
    have hleft :
        ((((⟨4⟩ : UInt256) +
            uInt256OfByteArray
              (I.calldata.readBytes ((⟨4⟩ : UInt256) + ⟨96⟩).toNat 32)) +
          ⟨32⟩).toNat) = 4 + swapDataOffset I + 32 := by
      rw [uadd_toNat, hleft1, show (⟨32⟩ : UInt256).toNat = 32 from by decide]
      rw [Nat.mod_eq_of_lt]
      have hcap : 4 + 4294967296 + 32 < UInt256.size := by norm_num [UInt256.size]
      omega
    have hright :
        (((⟨4⟩ : UInt256) + UInt256.sub (UInt256.ofNat I.calldata.size) ⟨4⟩).toNat) =
          I.calldata.size := by
      have hword :
          (⟨4⟩ : UInt256) + UInt256.sub (UInt256.ofNat I.calldata.size) ⟨4⟩ =
            UInt256.ofNat I.calldata.size :=
        uadd_word_usub_ofNat_word (n := I.calldata.size) (c := (⟨4⟩ : UInt256))
          (by
            rw [show ((⟨4⟩ : UInt256).toNat) = 4 from by decide]
            omega)
          hsize
      rw [hword, ulit_toNat' I.calldata.size hsize]
    rw [hleft, hright]
    exact hlenWord
  have rd516' := rd516
  rw [hgtLen] at rd516'
  have rd517₀ := rd516'.iszero (by native_decide) (by evm_ov)
  have rd517 := rd517₀
  rw [show UInt256.isZero (⟨0⟩ : UInt256) = ⟨1⟩ from by decide] at rd517
  have rd520 := rd517.push2 ⟨525⟩ (by native_decide) (by evm_ov)
  have rd525 := rd520.jumpiT (by native_decide) (by decide : (⟨1⟩ : UInt256) ≠ ⟨0⟩)
    (by native_decide) (by evm_ov)
  have rd540 := evm_run rd525 with [
    jumpdest, dup1, calldataload, swap1, push1 ⟨32⟩, add, swap2, dup5,
    push1 ⟨1⟩, dup4, mul, dup5, add, gt]
  have hgtPayload :
      UInt256.gt
        (((⟨32⟩ : UInt256) +
          ((⟨4⟩ : UInt256) +
            uInt256OfByteArray
              (I.calldata.readBytes ((⟨4⟩ : UInt256) + ⟨96⟩).toNat 32))) +
          UInt256.mul
            (uInt256OfByteArray
              (I.calldata.readBytes
                (((⟨4⟩ : UInt256) +
                  uInt256OfByteArray
                    (I.calldata.readBytes ((⟨4⟩ : UInt256) + ⟨96⟩).toNat 32)).toNat)
                32))
            ⟨1⟩)
        ((⟨4⟩ : UInt256) + UInt256.sub (UInt256.ofNat I.calldata.size) ⟨4⟩) =
        ⟨1⟩ := by
    apply ugt_one
    have hpayloadNat := swapPayloadShort_lt (I := I) hpayload
    have hoffWord :
        (uInt256OfByteArray
          (I.calldata.readBytes ((⟨4⟩ : UInt256) + ⟨96⟩).toNat 32)).toNat =
          swapDataOffset I := by
      simp [swapDataOffset, swapDataOffsetWord, calldataWord,
        show (((⟨4⟩ : UInt256) + ⟨96⟩).toNat) = 100 from by decide]
    have hoffLe : swapDataOffset I ≤ 4294967296 := by
      have : ¬ 4294967296 < swapDataOffset I := by
        simpa [solcLegacyMaxU32] using hoffMax
      omega
    have hlenLe : swapDataSize I ≤ 4294967296 := by
      have : ¬ 4294967296 < swapDataSize I := by
        simpa [solcLegacyMaxU32] using hlenMax
      omega
    have hlenOffset :
        (((⟨4⟩ : UInt256) +
          uInt256OfByteArray
            (I.calldata.readBytes ((⟨4⟩ : UInt256) + ⟨96⟩).toNat 32)).toNat) =
          4 + swapDataOffset I := by
      rw [uadd_toNat, show (⟨4⟩ : UInt256).toNat = 4 from by decide, hoffWord]
      rw [Nat.mod_eq_of_lt]
      have hcap : 4 + 4294967296 < UInt256.size := by norm_num [UInt256.size]
      omega
    have hbase :
        (((⟨32⟩ : UInt256) +
          ((⟨4⟩ : UInt256) +
            uInt256OfByteArray
              (I.calldata.readBytes ((⟨4⟩ : UInt256) + ⟨96⟩).toNat 32))).toNat) =
          4 + swapDataOffset I + 32 := by
      rw [uadd_toNat, hlenOffset, show (⟨32⟩ : UInt256).toNat = 32 from by decide]
      rw [Nat.mod_eq_of_lt (by
        have hcap : 32 + (4 + 4294967296) < UInt256.size := by norm_num [UInt256.size]
        omega)]
      omega
    have hread :
        (uInt256OfByteArray
          (I.calldata.readBytes
            (((⟨4⟩ : UInt256) +
              uInt256OfByteArray
                (I.calldata.readBytes ((⟨4⟩ : UInt256) + ⟨96⟩).toNat 32)).toNat)
            32)).toNat = swapDataSize I := by
      simp [swapDataSize, swapDataSizeWord, calldataWord, hlenOffset]
    have hmul :
        (UInt256.mul
          (uInt256OfByteArray
            (I.calldata.readBytes
              (((⟨4⟩ : UInt256) +
                uInt256OfByteArray
                  (I.calldata.readBytes ((⟨4⟩ : UInt256) + ⟨96⟩).toNat 32)).toNat)
              32))
          ⟨1⟩).toNat = swapDataSize I := by
      rw [u256_mul_toNat, hread, show (⟨1⟩ : UInt256).toNat = 1 from by decide]
      rw [Nat.mul_one, Nat.mod_eq_of_lt]
      have hcap : 4294967296 < UInt256.size := by norm_num [UInt256.size]
      omega
    have hleft :
        ((((⟨32⟩ : UInt256) +
          ((⟨4⟩ : UInt256) +
            uInt256OfByteArray
              (I.calldata.readBytes ((⟨4⟩ : UInt256) + ⟨96⟩).toNat 32))) +
          UInt256.mul
            (uInt256OfByteArray
              (I.calldata.readBytes
                (((⟨4⟩ : UInt256) +
                  uInt256OfByteArray
                    (I.calldata.readBytes ((⟨4⟩ : UInt256) + ⟨96⟩).toNat 32)).toNat)
                32))
            ⟨1⟩).toNat) = 4 + swapDataOffset I + 32 + swapDataSize I := by
      rw [uadd_toNat, hbase, hmul]
      rw [Nat.mod_eq_of_lt]
      have hcap : 4 + 4294967296 + 32 + 4294967296 < UInt256.size := by
        norm_num [UInt256.size]
      omega
    have hright :
        (((⟨4⟩ : UInt256) + UInt256.sub (UInt256.ofNat I.calldata.size) ⟨4⟩).toNat) =
          I.calldata.size := by
      have hword :
          (⟨4⟩ : UInt256) + UInt256.sub (UInt256.ofNat I.calldata.size) ⟨4⟩ =
            UInt256.ofNat I.calldata.size :=
        uadd_word_usub_ofNat_word (n := I.calldata.size) (c := (⟨4⟩ : UInt256))
          (by
            rw [show ((⟨4⟩ : UInt256).toNat) = 4 from by decide]
            omega)
          hsize
      rw [hword, ulit_toNat' I.calldata.size hsize]
    rw [hleft, hright]
    exact hpayloadNat
  have rd540' := rd540
  rw [hgtPayload] at rd540'
  have rd546 := rd540'.pushConst ⟨4294967296⟩ (width := 5) (op := .PUSH5)
    (by decide) (by native_decide) (by evm_ov)
  have rd547 := rd546.dup4 (by native_decide) (by evm_ov)
  have rd548 := rd547.gt (by native_decide) (by evm_ov)
  have rd549 := RD.lor rd548 (by native_decide) (by evm_ov)
  have rd550₀ := rd549.iszero (by native_decide) (by evm_ov)
  have rd550 := rd550₀
  rw [isZero_eq_zero_of_ne (swapU256_lor_one_ne_zero_right _)] at rd550
  have rd553 := rd550.push2 ⟨559⟩ (by native_decide) (by evm_ov)
  have rd554 := rd553.jumpiNT (by native_decide) (by decide : (⟨0⟩ : UInt256) = ⟨0⟩)
    (by evm_ov)
  have rd556 := rd554.push1 ⟨0⟩ (by native_decide) (by evm_ov)
  have rd557 := rd556.dup1 (by native_decide) (by evm_ov)
  exact rd557.rev 0 (by native_decide) mem_cost (by evm_ov)

theorem uniswapSwapBodyCoreDecodeFailed_headShort
    {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256} {sel : UInt256}
    (hcode : I.code = uniswapV2PairBytecode) (hsize : I.calldata.size < UInt256.size)
    (hsz4 : 4 ≤ I.calldata.size) (hshort : I.calldata.size < 132)
    (hdispatch : dispatchMsg contract I.calldata = some swapTransition)
    (hreach : ∃ k C, RD uniswapV2PairBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) ⟨430⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ_evm) k C) :
    runtimeEquivalenceFor config contract cA gh bl σ_evm σ_solm σ₀ g A I := by
  have hdec := uniswapDecode_swap_none_head_short (I := I) hsz4 hshort
  exact (uniswapSwapX_shortHead (g := Sat256.ofUInt256 g) hsz4 hsize hshort hreach)
    |>.reEquivDecodingFailed hcode hdispatch hdec

theorem uniswapSwapBodyDecodeFailed_headShort
    {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256}
    (hcode : I.code = uniswapV2PairBytecode) (hsize : I.calldata.size < UInt256.size)
    (hwv : I.weiValue = ⟨0⟩) (hsel : selIs I ⟨#[0x02, 0x2c, 0x0d, 0x9f]⟩)
    (hshort : I.calldata.size < 132)
    (hdispatch : dispatchMsg contract I.calldata = some swapTransition) :
    runtimeEquivalenceFor config contract cA gh bl σ_evm σ_solm σ₀ g A I := by
  have hsz4 : 4 ≤ I.calldata.size :=
    calldata_size_ge_of_selIs I ⟨#[0x02, 0x2c, 0x0d, 0x9f]⟩ rfl hsel
  exact uniswapSwapBodyCoreDecodeFailed_headShort hcode hsize hsz4 hshort hdispatch
    (uniswapReachSwapBody (g := Sat256.ofUInt256 g) hcode hwv hsz4 hsize hsel)

theorem uniswapSwapBodyCoreDecodeFailed_offsetHuge
    {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256} {sel : UInt256}
    (hcode : I.code = uniswapV2PairBytecode) (hsize : I.calldata.size < UInt256.size)
    (hsz132 : 132 ≤ I.calldata.size) (hoff : solcLegacyMaxU32 < swapDataOffset I)
    (hdispatch : dispatchMsg contract I.calldata = some swapTransition)
    (hreach : ∃ k C, RD uniswapV2PairBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) ⟨430⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ_evm) k C) :
    runtimeEquivalenceFor config contract cA gh bl σ_evm σ_solm σ₀ g A I := by
  have hdec := uniswapDecode_swap_none_offset_huge (I := I) hsz132 hoff
  exact (uniswapSwapX_offsetHuge (g := Sat256.ofUInt256 g)
      hsize hsz132 hoff hreach)
    |>.reEquivDecodingFailed hcode hdispatch hdec

theorem uniswapSwapBodyDecodeFailed_offsetHuge
    {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256}
    (hcode : I.code = uniswapV2PairBytecode) (hsize : I.calldata.size < UInt256.size)
    (hwv : I.weiValue = ⟨0⟩) (hsel : selIs I ⟨#[0x02, 0x2c, 0x0d, 0x9f]⟩)
    (hsz132 : 132 ≤ I.calldata.size) (hoff : solcLegacyMaxU32 < swapDataOffset I)
    (hdispatch : dispatchMsg contract I.calldata = some swapTransition) :
    runtimeEquivalenceFor config contract cA gh bl σ_evm σ_solm σ₀ g A I := by
  have hsz4 : 4 ≤ I.calldata.size :=
    calldata_size_ge_of_selIs I ⟨#[0x02, 0x2c, 0x0d, 0x9f]⟩ rfl hsel
  exact uniswapSwapBodyCoreDecodeFailed_offsetHuge hcode hsize hsz132 hoff hdispatch
    (uniswapReachSwapBody (g := Sat256.ofUInt256 g) hcode hwv hsz4 hsize hsel)

theorem uniswapSwapBodyCoreDecodeFailed_lengthShort
    {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256} {sel : UInt256}
    (hcode : I.code = uniswapV2PairBytecode) (hsize : I.calldata.size < UInt256.size)
    (hsz132 : 132 ≤ I.calldata.size)
    (hoffMax : ¬ solcLegacyMaxU32 < swapDataOffset I)
    (hlenShort : I.calldata.size < 4 + swapDataOffset I + 32)
    (hdispatch : dispatchMsg contract I.calldata = some swapTransition)
    (hreach : ∃ k C, RD uniswapV2PairBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) ⟨430⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ_evm) k C) :
    runtimeEquivalenceFor config contract cA gh bl σ_evm σ_solm σ₀ g A I := by
  have hdec := uniswapDecode_swap_none_length_short (I := I) hsz132 hoffMax hlenShort
  exact (uniswapSwapX_lengthShort (g := Sat256.ofUInt256 g)
      hsize hsz132 hoffMax hlenShort hreach)
    |>.reEquivDecodingFailed hcode hdispatch hdec

theorem uniswapSwapBodyDecodeFailed_lengthShort
    {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256}
    (hcode : I.code = uniswapV2PairBytecode) (hsize : I.calldata.size < UInt256.size)
    (hwv : I.weiValue = ⟨0⟩) (hsel : selIs I ⟨#[0x02, 0x2c, 0x0d, 0x9f]⟩)
    (hsz132 : 132 ≤ I.calldata.size) (hoffMax : ¬ solcLegacyMaxU32 < swapDataOffset I)
    (hlenShort : I.calldata.size < 4 + swapDataOffset I + 32)
    (hdispatch : dispatchMsg contract I.calldata = some swapTransition) :
    runtimeEquivalenceFor config contract cA gh bl σ_evm σ_solm σ₀ g A I := by
  have hsz4 : 4 ≤ I.calldata.size :=
    calldata_size_ge_of_selIs I ⟨#[0x02, 0x2c, 0x0d, 0x9f]⟩ rfl hsel
  exact uniswapSwapBodyCoreDecodeFailed_lengthShort hcode hsize hsz132 hoffMax hlenShort
    hdispatch
    (uniswapReachSwapBody (g := Sat256.ofUInt256 g) hcode hwv hsz4 hsize hsel)

theorem uniswapSwapBodyCoreDecodeFailed_lengthHuge
    {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256} {sel : UInt256}
    (hcode : I.code = uniswapV2PairBytecode) (hsize : I.calldata.size < UInt256.size)
    (hsz132 : 132 ≤ I.calldata.size)
    (hoffMax : ¬ solcLegacyMaxU32 < swapDataOffset I)
    (hlenWord : 4 + swapDataOffset I + 32 ≤ I.calldata.size)
    (hlenHuge : solcLegacyMaxU32 < swapDataSize I)
    (hdispatch : dispatchMsg contract I.calldata = some swapTransition)
    (hreach : ∃ k C, RD uniswapV2PairBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) ⟨430⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ_evm) k C) :
    runtimeEquivalenceFor config contract cA gh bl σ_evm σ_solm σ₀ g A I := by
  have hdec := uniswapDecode_swap_none_length_huge (I := I) hsz132 hoffMax hlenWord hlenHuge
  exact (uniswapSwapX_lengthHuge (g := Sat256.ofUInt256 g)
      hsize hsz132 hoffMax hlenWord hlenHuge hreach)
    |>.reEquivDecodingFailed hcode hdispatch hdec

theorem uniswapSwapBodyDecodeFailed_lengthHuge
    {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256}
    (hcode : I.code = uniswapV2PairBytecode) (hsize : I.calldata.size < UInt256.size)
    (hwv : I.weiValue = ⟨0⟩) (hsel : selIs I ⟨#[0x02, 0x2c, 0x0d, 0x9f]⟩)
    (hsz132 : 132 ≤ I.calldata.size) (hoffMax : ¬ solcLegacyMaxU32 < swapDataOffset I)
    (hlenWord : 4 + swapDataOffset I + 32 ≤ I.calldata.size)
    (hlenHuge : solcLegacyMaxU32 < swapDataSize I)
    (hdispatch : dispatchMsg contract I.calldata = some swapTransition) :
    runtimeEquivalenceFor config contract cA gh bl σ_evm σ_solm σ₀ g A I := by
  have hsz4 : 4 ≤ I.calldata.size :=
    calldata_size_ge_of_selIs I ⟨#[0x02, 0x2c, 0x0d, 0x9f]⟩ rfl hsel
  exact uniswapSwapBodyCoreDecodeFailed_lengthHuge hcode hsize hsz132 hoffMax hlenWord
    hlenHuge hdispatch
    (uniswapReachSwapBody (g := Sat256.ofUInt256 g) hcode hwv hsz4 hsize hsel)

theorem uniswapSwapBodyCoreDecodeFailed_payloadShort
    {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256} {sel : UInt256}
    (hcode : I.code = uniswapV2PairBytecode) (hsize : I.calldata.size < UInt256.size)
    (hsz132 : 132 ≤ I.calldata.size)
    (hoffMax : ¬ solcLegacyMaxU32 < swapDataOffset I)
    (hlenWord : 4 + swapDataOffset I + 32 ≤ I.calldata.size)
    (hlenMax : ¬ solcLegacyMaxU32 < swapDataSize I)
    (hpayload : (((I.calldata.toList.drop 4).drop (swapDataOffset I + 32)).take
      (swapDataSize I)).length ≠ swapDataSize I)
    (hdispatch : dispatchMsg contract I.calldata = some swapTransition)
    (hreach : ∃ k C, RD uniswapV2PairBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) ⟨430⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ_evm) k C) :
    runtimeEquivalenceFor config contract cA gh bl σ_evm σ_solm σ₀ g A I := by
  have hdec := uniswapDecode_swap_none_payload_short (I := I) hsz132 hoffMax hlenWord
    hlenMax hpayload
  exact (uniswapSwapX_payloadShort (g := Sat256.ofUInt256 g)
      hsize hsz132 hoffMax hlenWord hlenMax hpayload hreach)
    |>.reEquivDecodingFailed hcode hdispatch hdec

theorem uniswapSwapBodyDecodeFailed_payloadShort
    {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256}
    (hcode : I.code = uniswapV2PairBytecode) (hsize : I.calldata.size < UInt256.size)
    (hwv : I.weiValue = ⟨0⟩) (hsel : selIs I ⟨#[0x02, 0x2c, 0x0d, 0x9f]⟩)
    (hsz132 : 132 ≤ I.calldata.size) (hoffMax : ¬ solcLegacyMaxU32 < swapDataOffset I)
    (hlenWord : 4 + swapDataOffset I + 32 ≤ I.calldata.size)
    (hlenMax : ¬ solcLegacyMaxU32 < swapDataSize I)
    (hpayload : (((I.calldata.toList.drop 4).drop (swapDataOffset I + 32)).take
      (swapDataSize I)).length ≠ swapDataSize I)
    (hdispatch : dispatchMsg contract I.calldata = some swapTransition) :
    runtimeEquivalenceFor config contract cA gh bl σ_evm σ_solm σ₀ g A I := by
  have hsz4 : 4 ≤ I.calldata.size :=
    calldata_size_ge_of_selIs I ⟨#[0x02, 0x2c, 0x0d, 0x9f]⟩ rfl hsel
  exact uniswapSwapBodyCoreDecodeFailed_payloadShort hcode hsize hsz132 hoffMax hlenWord
    hlenMax hpayload hdispatch
    (uniswapReachSwapBody (g := Sat256.ofUInt256 g) hcode hwv hsz4 hsize hsel)

theorem uniswapSwapBody
    {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256}
    (hcode : I.code = uniswapV2PairBytecode) (hsize : I.calldata.size < UInt256.size)
    (hperm : I.perm = true) (hwv : I.weiValue = ⟨0⟩)
    (hsel : selIs I ⟨#[0x02, 0x2c, 0x0d, 0x9f]⟩)
    (hdispatch : dispatchMsg contract I.calldata = some swapTransition)
    (hAccounts : accountMapEquiv σ_evm σ_solm) :
    runtimeEquivalenceFor config contract cA gh bl σ_evm σ_solm σ₀ g A I := by
  by_cases hsz132 : 132 ≤ I.calldata.size
  · by_cases hoff : solcLegacyMaxU32 < swapDataOffset I
    · exact uniswapSwapBodyDecodeFailed_offsetHuge hcode hsize hwv hsel hsz132 hoff
        hdispatch
    · by_cases hlenWord : 4 + swapDataOffset I + 32 ≤ I.calldata.size
      · by_cases hlenHuge : solcLegacyMaxU32 < swapDataSize I
        · exact uniswapSwapBodyDecodeFailed_lengthHuge hcode hsize hwv hsel hsz132
            hoff hlenWord hlenHuge hdispatch
        · by_cases hpayload : (((I.calldata.toList.drop 4).drop
              (swapDataOffset I + 32)).take (swapDataSize I)).length = swapDataSize I
          · sorry
          · exact uniswapSwapBodyDecodeFailed_payloadShort hcode hsize hwv hsel hsz132
              hoff hlenWord hlenHuge hpayload hdispatch
      · exact uniswapSwapBodyDecodeFailed_lengthShort hcode hsize hwv hsel hsz132
          hoff (by omega) hdispatch
  · exact uniswapSwapBodyDecodeFailed_headShort hcode hsize hwv hsel (by omega) hdispatch

end UniswapV2Pair
