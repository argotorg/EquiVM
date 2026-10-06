import Reasoning.ABI

/-!
# Legacy Solidity ABI decoding

Shared scalar tuple decoders for Solidity's legacy ABI mode, including truncated-input cases.
-/

open Solm ABI Ethereum Ethereum.EVM

namespace Reasoning.Theory

set_option autoImplicit false

theorem decodeABIValues_bytes32_uint256_legacy_ok {bytes : List UInt8}
    (hlen0 : (bytes.take 32).length = 32)
    (hlen32 : ((bytes.drop 32).take 32).length = 32) :
    decodeABIValues? [abiBytes32, abiUInt256] bytes 0 0 64 64 DecodeMode.legacySolc05 =
      some ([.fixedBytes abiBytes32Width (bytes.take 32),
        .int (Int.ofNat (ABI.bytesToWord ((bytes.drop 32).take 32)).toNat)], 64) := by
  simp [decodeABIValues?, abiBytes32, abiBytes32Width, abiUInt256, isDynamicABIType,
    staticABIEncodedSize?, decodeABIValue?, readBytes?, hlen0]
  simp [readWord?, readBytes?, decodeABIWord?, hlen32]
  exact normalizeInt_uint256_word (ABI.bytesToWord ((bytes.drop 32).take 32))

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
  rw [show abiTupleHeadSize? [abiBytes32, abiUInt256] = some 64 by
    simp [abiTupleHeadSize?, isDynamicABIType, staticABIEncodedSize?,
      abiBytes32, abiBytes32Width, abiUInt256, abiAddress]]
  simp only [bind, Option.bind]
  rw [decodeABIValues_bytes32_uint256_legacy_ok (bytes := cd.toList.drop 4)
    (by simpa using htake4)
    (by simpa [List.drop_drop, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using htake36)]
  rw [if_neg (by rw [List.length_drop, htlen]; omega : ¬ (cd.toList.drop 4).length < 64)]
  simp [decodeCalldata.insertValues]
  rw [hword36]

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
  rw [show abiTupleHeadSize? [abiBytes32, abiUInt256] = some 64 by
    simp [abiTupleHeadSize?, isDynamicABIType, staticABIEncodedSize?,
      abiBytes32, abiBytes32Width, abiUInt256, abiAddress]]
  simp only [bind, Option.bind]
  by_cases hbytes : (cd.toList.drop 4).length < 64
  · rw [if_pos hbytes]
  · rw [if_neg hbytes]
    rw [decodeABIValues_bytes32_uint256_legacy_none_short (bytes := cd.toList.drop 4) (by
      rw [List.length_drop, htlen]
      omega)]

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
  rw [show abiTupleHeadSize? [abiBytes32, abiAddress] = some 64 by
    simp [abiTupleHeadSize?, isDynamicABIType, staticABIEncodedSize?,
      abiBytes32, abiBytes32Width, abiUInt256, abiAddress]]
  simp only [bind, Option.bind]
  rw [decodeABIValues_bytes32_address_legacy_ok (bytes := cd.toList.drop 4)
    (by simpa using htake4)
    (by simpa [List.drop_drop, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using htake36)]
  rw [if_neg (by rw [List.length_drop, htlen]; omega : ¬ (cd.toList.drop 4).length < 64)]
  simp [decodeCalldata.insertValues]
  rw [hword36]

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
  rw [show abiTupleHeadSize? [abiBytes32, abiAddress] = some 64 by
    simp [abiTupleHeadSize?, isDynamicABIType, staticABIEncodedSize?,
      abiBytes32, abiBytes32Width, abiUInt256, abiAddress]]
  simp only [bind, Option.bind]
  by_cases hbytes : (cd.toList.drop 4).length < 64
  · rw [if_pos hbytes]
  · rw [if_neg hbytes]
    rw [decodeABIValues_bytes32_address_legacy_none_short (bytes := cd.toList.drop 4) (by
      rw [List.length_drop, htlen]
      omega)]

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
  exact normalizeInt_uint256_word (ABI.bytesToWord ((bytes.drop 64).take 32))

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
  rw [show abiTupleHeadSize? [abiBytes32, abiBytes32, abiUInt256] = some 96 by
    simp [abiTupleHeadSize?, isDynamicABIType, staticABIEncodedSize?,
      abiBytes32, abiBytes32Width, abiUInt256, abiAddress]]
  simp only [bind, Option.bind]
  rw [decodeABIValues_bytes32_bytes32_uint256_legacy_ok (bytes := cd.toList.drop 4)
    (by simpa using htake4)
    (by simpa [List.drop_drop, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using htake36)
    (by simpa [List.drop_drop, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using htake68)]
  rw [if_neg (by rw [List.length_drop, htlen]; omega : ¬ (cd.toList.drop 4).length < 96)]
  simp [decodeCalldata.insertValues]
  rw [hword68]

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
  rw [show abiTupleHeadSize? [abiBytes32, abiBytes32, abiUInt256] = some 96 by
    simp [abiTupleHeadSize?, isDynamicABIType, staticABIEncodedSize?,
      abiBytes32, abiBytes32Width, abiUInt256, abiAddress]]
  simp only [bind, Option.bind]
  by_cases hbytes : (cd.toList.drop 4).length < 96
  · rw [if_pos hbytes]
  · rw [if_neg hbytes]
    rw [decodeABIValues_bytes32_bytes32_uint256_legacy_none_short
      (bytes := cd.toList.drop 4) (by
        rw [List.length_drop, htlen]
        omega)]

theorem decodeABIValues_bytes32_bytes32_address_legacy_ok {bytes : List UInt8}
    (hlen0 : (bytes.take 32).length = 32)
    (hlen32 : ((bytes.drop 32).take 32).length = 32)
    (hlen64 : ((bytes.drop 64).take 32).length = 32) :
    decodeABIValues? [abiBytes32, abiBytes32, abiAddress] bytes 0 0 96 96
        DecodeMode.legacySolc05 =
      some ([.fixedBytes abiBytes32Width (bytes.take 32),
        .fixedBytes abiBytes32Width ((bytes.drop 32).take 32),
        .address (AccountAddress.ofNat
          (ABI.bytesToWord ((bytes.drop 64).take 32)).toNat)], 96) := by
  simp [decodeABIValues?, abiBytes32, abiBytes32Width, abiAddress, isDynamicABIType,
    staticABIEncodedSize?, decodeABIValue?, readBytes?, hlen0]
  have hlen32le : 32 ≤ bytes.length - 32 := by
    rw [List.length_take, List.length_drop] at hlen32
    omega
  rw [if_pos hlen32le]
  have hlen64le : 32 ≤ bytes.length - 64 := by
    rw [List.length_take, List.length_drop] at hlen64
    omega
  simp [readWord?, readBytes?, decodeABIWord?, UInt256.toNat, hlen64]

theorem decodeCalldata_legacyBytes32_bytes32_address_ok {cd : ByteArray}
    {x y z : Solm.Ident} (hsz100 : 100 ≤ cd.size) :
    decodeCalldataWithMode DecodeMode.legacySolc05 [x, y, z]
        [abiBytes32, abiBytes32, abiAddress] cd =
      some ((((∅ : Solm.Store).insert x
        (.fixedBytes abiBytes32Width ((cd.toList.drop 4).take 32))).insert y
        (.fixedBytes abiBytes32Width ((cd.toList.drop 36).take 32))).insert z
        (.address (AccountAddress.ofNat (calldataWord cd 68).toNat))) := by
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
  rw [if_neg (by simp [abiBytes32, abiAddress, isDynamicABIType])]
  simp only [decodeCalldata.decodeArgs]
  rw [show abiTupleHeadSize? [abiBytes32, abiBytes32, abiAddress] = some 96 by
    simp [abiTupleHeadSize?, isDynamicABIType, staticABIEncodedSize?,
      abiBytes32, abiBytes32Width, abiUInt256, abiAddress]]
  simp only [bind, Option.bind]
  rw [decodeABIValues_bytes32_bytes32_address_legacy_ok (bytes := cd.toList.drop 4)
    (by simpa using htake4)
    (by simpa [List.drop_drop, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using htake36)
    (by simpa [List.drop_drop, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using htake68)]
  rw [if_neg (by rw [List.length_drop, htlen]; omega : ¬ (cd.toList.drop 4).length < 96)]
  simp [decodeCalldata.insertValues]
  rw [hword68]

theorem decodeABIValues_bytes32_bytes32_address_legacy_none_short {bytes : List UInt8}
    (hshort : bytes.length < 96) :
    decodeABIValues? [abiBytes32, abiBytes32, abiAddress] bytes 0 0 96 96
        DecodeMode.legacySolc05 =
      none := by
  simp only [decodeABIValues?, abiBytes32, abiBytes32Width, abiAddress, isDynamicABIType,
    Bool.false_eq_true, if_false, staticABIEncodedSize?, bind, Option.bind, Nat.zero_add]
  by_cases h32 : bytes.length < 32
  · have hnot : ¬ 32 ≤ bytes.length := by omega
    simp [decodeABIValue?, readBytes?, hnot]
  · have htake0 : (bytes.take 32).length = 32 := by
      rw [List.length_take]
      omega
    simp [decodeABIValue?, readBytes?, htake0]
    by_cases h64 : bytes.length < 64
    · have hnot : ¬ 32 ≤ bytes.length - 32 := by omega
      simp [hnot]
    · have hlen32le : 32 ≤ bytes.length - 32 := by omega
      rw [if_pos hlen32le]
      have hnot : ¬ 32 ≤ bytes.length - 64 := by omega
      simp [readWord?, readBytes?, hnot]

theorem decodeCalldata_legacyBytes32_bytes32_address_none_short {cd : ByteArray}
    {x y z : Solm.Ident} (hsz4 : 4 ≤ cd.size) (hshort : cd.size < 100) :
    decodeCalldataWithMode DecodeMode.legacySolc05 [x, y, z]
        [abiBytes32, abiBytes32, abiAddress] cd =
      none := by
  have htlen : cd.toList.length = cd.size := by
    rw [byteArray_toList_eq, Array.length_toList]
    rfl
  unfold decodeCalldataWithMode decodeCalldata
  rw [if_neg (by rw [htlen]; omega : ¬ cd.toList.length < 4)]
  rw [if_neg (by simp [abiBytes32, abiAddress, isDynamicABIType])]
  simp only [decodeCalldata.decodeArgs]
  rw [show abiTupleHeadSize? [abiBytes32, abiBytes32, abiAddress] = some 96 by
    simp [abiTupleHeadSize?, isDynamicABIType, staticABIEncodedSize?,
      abiBytes32, abiBytes32Width, abiUInt256, abiAddress]]
  simp only [bind, Option.bind]
  by_cases hbytes : (cd.toList.drop 4).length < 96
  · rw [if_pos hbytes]
  · rw [if_neg hbytes]
    rw [decodeABIValues_bytes32_bytes32_address_legacy_none_short
      (bytes := cd.toList.drop 4) (by
        rw [List.length_drop, htlen]
        omega)]

theorem decodeCalldataWithMode_legacyBytes32_ok {cd : ByteArray} {x : Ident}
    (hsz36 : 36 ≤ cd.size) :
    decodeCalldataWithMode DecodeMode.legacySolc05 [x] [abiBytes32] cd =
      some ((∅ : Store).insert x (.fixedBytes abiBytes32Width ((cd.toList.drop 4).take 32))) := by
  unfold decodeCalldataWithMode decodeCalldata
  have htlen : cd.toList.length = cd.size := by
    rw [byteArray_toList_eq, Array.length_toList]
    rfl
  have hnot4 : ¬ cd.toList.length < 4 := by
    rw [htlen]; omega
  rw [if_neg hnot4]
  have hnotDyn : ¬ ([abiBytes32].any isDynamicABIType = true ∧ 2 ^ 255 ≤ cd.toList.length) := by
    simp [abiBytes32, isDynamicABIType]
  rw [if_neg hnotDyn]
  have hread : readBytes? (cd.toList.drop 4) 0 32 =
      some ((cd.toList.drop 4).take 32) := by
    unfold readBytes?
    have hlen : (((cd.toList.drop 4).drop 0).take 32).length = 32 := by
      rw [List.drop_zero, List.length_take, List.length_drop, htlen]; omega
    rw [if_pos hlen, List.drop_zero]
  have hblen : ((cd.toList.drop 4).take 32).length = 32 := by
    rw [List.length_take, List.length_drop, htlen]; omega
  have hpad : zeroPadding? ((cd.toList.drop 4).take 32) 32 0 = some () := by
    unfold zeroPadding? readBytes?; simp
  have htake : List.take 32 ((cd.toList.drop 4).take 32) = (cd.toList.drop 4).take 32 :=
    List.take_of_length_le (by rw [hblen])
  have hnotArgShort : ¬ cd.toList.length - 4 < 32 := by
    rw [htlen]; omega
  simp [decodeCalldata.decodeArgs, decodeCalldata.insertValues, abiBytes32,
    ABI.decodeABIValues?, ABI.decodeABIValue?, isDynamicABIType, staticABIEncodedSize?,
    abiTupleHeadSize?, hread, abiBytes32Width, htake, hnotArgShort]

theorem decodeCalldataWithMode_legacyBytes32_none_short {cd : ByteArray} {x : Ident}
    (hsz4 : 4 ≤ cd.size) (hshort : cd.size < 36) :
    decodeCalldataWithMode DecodeMode.legacySolc05 [x] [abiBytes32] cd = none := by
  unfold decodeCalldataWithMode decodeCalldata
  have htlen : cd.toList.length = cd.size := by
    rw [byteArray_toList_eq, Array.length_toList]
    rfl
  have hnot4 : ¬ cd.toList.length < 4 := by
    rw [htlen]; omega
  rw [if_neg hnot4]
  have hnotDyn : ¬ ([abiBytes32].any isDynamicABIType = true ∧ 2 ^ 255 ≤ cd.toList.length) := by
    simp [abiBytes32, isDynamicABIType]
  rw [if_neg hnotDyn]
  have hread : readBytes? (cd.toList.drop 4) 0 32 = none := by
    unfold readBytes?
    have hlen : ¬ (((cd.toList.drop 4).drop 0).take 32).length = 32 := by
      rw [List.drop_zero, List.length_take, List.length_drop, htlen]; omega
    rw [if_neg hlen]
  simp [decodeCalldata.decodeArgs, abiBytes32, ABI.decodeABIValues?, ABI.decodeABIValue?,
    isDynamicABIType, staticABIEncodedSize?, abiTupleHeadSize?, hread]

end Reasoning.Theory
