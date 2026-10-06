import Reasoning.ABILegacy

/-!
# Composite ABI helpers

Shared tuple, dynamic payload, and return-value decoders. Strict and legacy modes retain their
original canonicality and input-size requirements.
-/

open Solm ABI Ethereum Ethereum.EVM

set_option autoImplicit false
set_option maxRecDepth 2000000
set_option maxHeartbeats 2000000

namespace Reasoning.Theory

abbrev abiUInt8Int : IntType := .uint ⟨8, by decide⟩
abbrev abiUInt48Int : IntType := .uint ⟨48, by decide⟩
abbrev abiUInt96Int : IntType := .uint ⟨96, by decide⟩
abbrev abiUInt256Int : IntType := .uint ⟨256, by decide⟩
abbrev abiInt256Int : IntType := .sint ⟨256, by decide⟩
abbrev abiUInt8 : ABIType := .elem (.int abiUInt8Int)
abbrev abiUInt48 : ABIType := .elem (.int abiUInt48Int)
abbrev abiUInt96 : ABIType := .elem (.int abiUInt96Int)
abbrev abiInt256 : ABIType := .elem (.int abiInt256Int)
abbrev abiBytes : ABIType := .bytes

theorem decodeCalldata_legacyUInt256_ok {cd : ByteArray} {x : Solm.Ident}
    (hsz36 : 36 ≤ cd.size) :
    decodeCalldataWithMode DecodeMode.legacySolc05 [x] [abiUInt256] cd =
      some ((∅ : Solm.Store).insert x (.int (Int.ofNat (calldataWord cd 4).toNat))) := by
  have htlen : cd.toList.length = cd.size := by
    rw [byteArray_toList_eq, Array.length_toList]
    rfl
  have htake4 : ((cd.toList.drop 4).take 32).length = 32 := by
    rw [List.length_take, List.length_drop, htlen]
    omega
  have hword4 : ABI.bytesToWord ((cd.toList.drop 4).take 32) = calldataWord cd 4 :=
    decode_word_at_eq cd 4 (by omega) (by norm_num)
  rw [decodeCalldataWithMode_legacyScalarWords_eq (names := [x]) (types := [abiUInt256])
    (cd := cd) (by decide)]
  rw [if_neg (by rw [htlen]; omega : ¬ cd.toList.length < 4)]
  simp only [decodeScalarWordsWithMode?]
  rw [decodeScalarWordWithMode_uint256_ok (mode := DecodeMode.legacySolc05)
    (bytes := cd.toList.drop 4) (start := 0) htake4]
  change decodeCalldata.insertValues [x]
      [.int (Int.ofNat (ABI.bytesToWord ((cd.toList.drop 4).take 32)).toNat)] ∅ =
    some ((∅ : Solm.Store).insert x (.int (Int.ofNat (calldataWord cd 4).toNat)))
  rw [hword4]
  simp [decodeCalldata.insertValues]

theorem decodeCalldata_legacyUInt256_none_short {cd : ByteArray} {x : Solm.Ident}
    (hsz4 : 4 ≤ cd.size) (hshort : cd.size < 36) :
    decodeCalldataWithMode DecodeMode.legacySolc05 [x] [abiUInt256] cd = none := by
  have htlen : cd.toList.length = cd.size := by
    rw [byteArray_toList_eq, Array.length_toList]
    rfl
  rw [decodeCalldataWithMode_legacyScalarWords_eq (names := [x]) (types := [abiUInt256])
    (cd := cd) (by decide)]
  rw [if_neg (by rw [htlen]; omega : ¬ cd.toList.length < 4)]
  simp only [decodeScalarWordsWithMode?]
  have htake0n : ¬ ((cd.toList.drop 4).take 32).length = 32 := by
    rw [List.length_take, List.length_drop, htlen]
    omega
  rw [decodeScalarWordWithMode_uint256_none_short (mode := DecodeMode.legacySolc05)
    (start := 0) (by simpa using htake0n)]
  simp only [Option.bind, bind]

theorem decodeABIValues_uint256_uint256_legacy_ok {bytes : List UInt8}
    (hlen0 : (bytes.take 32).length = 32)
    (hlen32 : ((bytes.drop 32).take 32).length = 32) :
    decodeABIValues? [abiUInt256, abiUInt256] bytes 0 0 64 64 DecodeMode.legacySolc05 =
      some ([.int (Int.ofNat (ABI.bytesToWord (bytes.take 32)).toNat),
        .int (Int.ofNat (ABI.bytesToWord ((bytes.drop 32).take 32)).toNat)], 64) := by
  have hread32 : 32 ≤ bytes.length - 32 := by
    rw [List.length_take, List.length_drop] at hlen32
    omega
  have hmod0 :
      (Int.ofNat (ABI.bytesToWord (bytes.take 32)).val % Int.ofNat (EVM.twoPow 256)) =
        Int.ofNat (UInt256.toNat (ABI.bytesToWord (bytes.take 32))) := by
    rw [Int.emod_eq_of_lt]
    · simp [UInt256.toNat]
    · exact Int.natCast_nonneg _
    · have hlt : (ABI.bytesToWord (bytes.take 32)).val < EVM.twoPow 256 := by
        simpa [EVM.twoPow, UInt256.size] using (ABI.bytesToWord (bytes.take 32)).val.isLt
      exact Int.ofNat_lt.mpr hlt
  have hmod32 :
      (Int.ofNat (ABI.bytesToWord ((bytes.drop 32).take 32)).val %
          Int.ofNat (EVM.twoPow 256)) =
        Int.ofNat (UInt256.toNat (ABI.bytesToWord ((bytes.drop 32).take 32))) := by
    rw [Int.emod_eq_of_lt]
    · simp [UInt256.toNat]
    · exact Int.natCast_nonneg _
    · have hlt : (ABI.bytesToWord ((bytes.drop 32).take 32)).val < EVM.twoPow 256 := by
        simpa [EVM.twoPow, UInt256.size] using
          (ABI.bytesToWord ((bytes.drop 32).take 32)).val.isLt
      exact Int.ofNat_lt.mpr hlt
  simp [decodeABIValues?, abiUInt256, isDynamicABIType, staticABIEncodedSize?,
    decodeABIValue?, readWord?, readBytes?, decodeABIWord?, hlen0, hread32]
  exact ⟨hmod0, hmod32⟩

theorem decodeABIValues_uint256_uint256_legacy_none_short {bytes : List UInt8}
    (hshort : bytes.length < 64) :
    decodeABIValues? [abiUInt256, abiUInt256] bytes 0 0 64 64 DecodeMode.legacySolc05 =
      none := by
  simp only [decodeABIValues?, abiUInt256, isDynamicABIType, Bool.false_eq_true, if_false,
    staticABIEncodedSize?, bind, Option.bind, Nat.zero_add]
  by_cases h32 : bytes.length < 32
  · have hnot : ¬ 32 ≤ bytes.length := by omega
    simp [decodeABIValue?, readWord?, readBytes?, hnot]
  · have htake0 : (bytes.take 32).length = 32 := by
      rw [List.length_take]
      omega
    have hnot : ¬ 32 ≤ bytes.length - 32 := by
      omega
    simp [decodeABIValue?, readWord?, readBytes?, decodeABIWord?, htake0, hnot]

theorem decodeCalldata_legacyUInt256_uint256_ok {cd : ByteArray}
    {x y : Solm.Ident} (hsz68 : 68 ≤ cd.size) :
    decodeCalldataWithMode DecodeMode.legacySolc05 [x, y] [abiUInt256, abiUInt256] cd =
      some (((∅ : Solm.Store).insert x
        (.int (Int.ofNat (calldataWord cd 4).toNat))).insert y
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
  have hword4 : ABI.bytesToWord ((cd.toList.drop 4).take 32) = calldataWord cd 4 :=
    decode_word_at_eq cd 4 (by omega) (by norm_num)
  have hword36 : ABI.bytesToWord ((cd.toList.drop 36).take 32) = calldataWord cd 36 :=
    decode_word_at_eq cd 36 (by omega) (by norm_num)
  unfold decodeCalldataWithMode decodeCalldata
  rw [if_neg (by rw [htlen]; omega : ¬ cd.toList.length < 4)]
  rw [if_neg (by simp [abiUInt256, isDynamicABIType])]
  simp only [decodeCalldata.decodeArgs]
  rw [show abiTupleHeadSize? [abiUInt256, abiUInt256] = some 64 by
    simp [abiTupleHeadSize?, isDynamicABIType, staticABIEncodedSize?,
      abiBytes32, abiBytes32Width, abiUInt256, abiAddress, abiInt256, abiBytes]]
  simp only [bind, Option.bind]
  rw [decodeABIValues_uint256_uint256_legacy_ok (bytes := cd.toList.drop 4)
    (by simpa using htake4)
    (by simpa [List.drop_drop, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using htake36)]
  rw [if_neg (by rw [List.length_drop, htlen]; omega :
    ¬ (cd.toList.drop 4).length < 64)]
  simp [decodeCalldata.insertValues]
  rw [hword4, hword36]

theorem decodeCalldata_legacyUInt256_uint256_none_short {cd : ByteArray}
    {x y : Solm.Ident} (hsz4 : 4 ≤ cd.size) (hshort : cd.size < 68) :
    decodeCalldataWithMode DecodeMode.legacySolc05 [x, y] [abiUInt256, abiUInt256] cd =
      none := by
  have htlen : cd.toList.length = cd.size := by
    rw [byteArray_toList_eq, Array.length_toList]
    rfl
  unfold decodeCalldataWithMode decodeCalldata
  rw [if_neg (by rw [htlen]; omega : ¬ cd.toList.length < 4)]
  rw [if_neg (by simp [abiUInt256, isDynamicABIType])]
  simp only [decodeCalldata.decodeArgs]
  rw [show abiTupleHeadSize? [abiUInt256, abiUInt256] = some 64 by
    simp [abiTupleHeadSize?, isDynamicABIType, staticABIEncodedSize?,
      abiBytes32, abiBytes32Width, abiUInt256, abiAddress, abiInt256, abiBytes]]
  simp only [bind, Option.bind]
  by_cases hbytes : (cd.toList.drop 4).length < 64
  · rw [if_pos hbytes]
  · rw [if_neg hbytes]
    rw [decodeABIValues_uint256_uint256_legacy_none_short
      (bytes := cd.toList.drop 4) (by
        rw [List.length_drop, htlen]
        omega)]

theorem decodeCalldata_legacyUint256_uint256_uint256_ok {cd : ByteArray}
    {x y z : Solm.Ident} (hsz100 : 100 ≤ cd.size) :
    decodeCalldataWithMode DecodeMode.legacySolc05 [x, y, z]
        [abiUInt256, abiUInt256, abiUInt256] cd =
      some ((((∅ : Store).insert x (.int (Int.ofNat (calldataWord cd 4).toNat))).insert y
        (.int (Int.ofNat (calldataWord cd 36).toNat))).insert z
        (.int (Int.ofNat (calldataWord cd 68).toNat))) := by
  have hlen : cd.toList.length = cd.size := by
    rw [byteArray_toList_eq, Array.length_toList]
    rfl
  have htake4 : ((cd.toList.drop 4).take 32).length = 32 := by
    rw [List.length_take, List.length_drop, hlen]
    omega
  have htake36 : ((cd.toList.drop 4).drop 32 |>.take 32).length = 32 := by
    rw [List.length_take, List.length_drop, List.length_drop, hlen]
    omega
  have htake68 : ((cd.toList.drop 4).drop 64 |>.take 32).length = 32 := by
    rw [List.length_take, List.length_drop, List.length_drop, hlen]
    omega
  have hword4 : ABI.bytesToWord ((cd.toList.drop 4).take 32) = calldataWord cd 4 :=
    decode_word_at_eq cd 4 (by omega) (by norm_num)
  have hword36 :
      ABI.bytesToWord (((cd.toList.drop 4).drop 32).take 32) = calldataWord cd 36 := by
    simpa [List.drop_drop, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc]
      using decode_word_at_eq cd 36 (by omega) (by norm_num)
  have hword68 :
      ABI.bytesToWord (((cd.toList.drop 4).drop 64).take 32) = calldataWord cd 68 := by
    simpa [List.drop_drop, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc]
      using decode_word_at_eq cd 68 (by omega) (by norm_num)
  rw [decodeCalldataWithMode_legacyScalarWords_eq (names := [x, y, z])
    (types := [abiUInt256, abiUInt256, abiUInt256]) (cd := cd) (by decide)]
  rw [if_neg (by rw [hlen]; omega : ¬ cd.toList.length < 4)]
  simp only [decodeScalarWordsWithMode?]
  rw [decodeScalarWordWithMode_uint256_ok (mode := DecodeMode.legacySolc05)
    (bytes := cd.toList.drop 4) (start := 0) htake4]
  rw [decodeScalarWordWithMode_uint256_ok (mode := DecodeMode.legacySolc05)
    (bytes := cd.toList.drop 4) (start := 32) htake36]
  rw [decodeScalarWordWithMode_uint256_ok (mode := DecodeMode.legacySolc05)
    (bytes := cd.toList.drop 4) (start := 64) htake68]
  simp only [Option.bind, bind]
  change decodeCalldata.insertValues [x, y, z]
      [.int (Int.ofNat (ABI.bytesToWord ((cd.toList.drop 4).take 32)).toNat),
        .int (Int.ofNat (ABI.bytesToWord (((cd.toList.drop 4).drop 32).take 32)).toNat),
        .int (Int.ofNat (ABI.bytesToWord (((cd.toList.drop 4).drop 64).take 32)).toNat)] ∅ =
    some ((((∅ : Store).insert x (.int (Int.ofNat (calldataWord cd 4).toNat))).insert y
      (.int (Int.ofNat (calldataWord cd 36).toNat))).insert z
      (.int (Int.ofNat (calldataWord cd 68).toNat)))
  rw [hword4, hword36, hword68]
  simp [decodeCalldata.insertValues]

theorem decodeCalldata_legacyUint256_uint256_uint256_none_short {cd : ByteArray}
    {x y z : Solm.Ident} (hsz4 : 4 ≤ cd.size) (hshort : cd.size < 100) :
    decodeCalldataWithMode DecodeMode.legacySolc05 [x, y, z]
      [abiUInt256, abiUInt256, abiUInt256] cd = none := by
  have hlen : cd.toList.length = cd.size := by
    rw [byteArray_toList_eq, Array.length_toList]
    rfl
  rw [decodeCalldataWithMode_legacyScalarWords_eq (names := [x, y, z])
    (types := [abiUInt256, abiUInt256, abiUInt256]) (cd := cd) (by decide)]
  rw [if_neg (by rw [hlen]; omega : ¬ cd.toList.length < 4)]
  by_cases hlen0 : 32 ≤ (cd.toList.drop 4).length
  · have htake0 : ((cd.toList.drop 4).take 32).length = 32 := by
      rw [List.length_take]
      omega
    simp only [decodeScalarWordsWithMode?]
    rw [decodeScalarWordWithMode_uint256_ok (mode := DecodeMode.legacySolc05)
      (bytes := cd.toList.drop 4) (start := 0) htake0]
    by_cases hlen32 : 64 ≤ (cd.toList.drop 4).length
    · have htake32 : (((cd.toList.drop 4).drop 32).take 32).length = 32 := by
        rw [List.length_take, List.length_drop]
        omega
      rw [decodeScalarWordWithMode_uint256_ok (mode := DecodeMode.legacySolc05)
        (bytes := cd.toList.drop 4) (start := 32) htake32]
      have htake64n : ¬ (((cd.toList.drop 4).drop 64).take 32).length = 32 := by
        rw [List.length_take, List.length_drop, List.length_drop, hlen]
        omega
      rw [decodeScalarWordWithMode_uint256_none_short (mode := DecodeMode.legacySolc05)
        (start := 64) (by simpa using htake64n)]
      simp only [Option.bind, bind]
    · have htake32n : ¬ (((cd.toList.drop 4).drop 32).take 32).length = 32 := by
        rw [List.length_take, List.length_drop]
        omega
      rw [decodeScalarWordWithMode_uint256_none_short (mode := DecodeMode.legacySolc05)
        (start := 32) (by simpa using htake32n)]
      simp only [Option.bind, bind]
  · have htake0n : ¬ ((cd.toList.drop 4).take 32).length = 32 := by
      rw [List.length_take]
      omega
    simp only [decodeScalarWordsWithMode?]
    rw [decodeScalarWordWithMode_uint256_none_short (mode := DecodeMode.legacySolc05)
      (start := 0) (by simpa using htake0n)]
    simp only [Option.bind, bind]

theorem decodeReturnValue_legacyAddress_ok {returndata : ByteArray}
    (hlo : 32 ≤ returndata.size) :
    ABI.decodeReturnValueWithMode? DecodeMode.legacySolc05 abiAddress returndata =
      some (.address (AccountAddress.ofNat
        (fromByteArrayBigEndian (returndata.extract 0 32)))) := by
  have hlen : returndata.toList.length = returndata.size := by
    rw [byteArray_toList_eq, Array.length_toList]
    rfl
  have htake0 : ((returndata.toList.drop 0).take 32).length = 32 := by
    rw [List.drop_zero, List.length_take, hlen]
    omega
  have hword := bytesToWord_take32_eq_extract0_32 (returndata := returndata)
  unfold ABI.decodeReturnValueWithMode? ABI.decodeReturnValuesWithMode?
  rw [abiTupleHeadSize_scalarWords_eq (types := [abiAddress]) (by decide)]
  simp only [bind, Option.bind]
  rw [decodeABIValues_scalarWordsWithMode_eq (mode := DecodeMode.legacySolc05)
    (types := [abiAddress]) (bytes := returndata.toList) (cursor := 0)
    (total := 32 * [abiAddress].length)
    (by decide) (by simp)]
  simp only [decodeScalarWordsWithMode?]
  unfold abiAddress
  rw [decodeScalarWord_legacyAddress_ok (bytes := returndata.toList) (start := 0) htake0]
  simp [hword, UInt256.toNat_ofNat_of_lt (fromByteArrayBigEndian_extract0_32_lt hlo)]

theorem decodeReturnValue_legacyAddress_none_short {returndata : ByteArray}
    (hshort : returndata.size < 32) :
    ABI.decodeReturnValueWithMode? DecodeMode.legacySolc05 abiAddress returndata = none := by
  have hlen : returndata.toList.length = returndata.size := by
    rw [byteArray_toList_eq, Array.length_toList]
    rfl
  have htake0n : ¬ ((returndata.toList.drop 0).take 32).length = 32 := by
    rw [List.drop_zero, List.length_take, hlen]
    omega
  unfold ABI.decodeReturnValueWithMode? ABI.decodeReturnValuesWithMode?
  rw [abiTupleHeadSize_scalarWords_eq (types := [abiAddress]) (by decide)]
  simp only [bind, Option.bind]
  rw [decodeABIValues_scalarWordsWithMode_eq (mode := DecodeMode.legacySolc05)
    (types := [abiAddress]) (bytes := returndata.toList) (cursor := 0)
    (total := 32 * [abiAddress].length)
    (by decide) (by simp)]
  simp only [decodeScalarWordsWithMode?]
  unfold abiAddress
  rw [decodeScalarWord_legacyAddress_none_short (bytes := returndata.toList) (start := 0)
    htake0n]
  rfl

theorem decodeScalarWordWithMode_legacy_uint8_ok {bytes : List UInt8} {start : Nat}
    (hlen : ((bytes.drop start).take 32).length = 32) :
    decodeScalarWordWithMode? DecodeMode.legacySolc05 (ABIType.elem (ElemType.int abiUInt8Int))
        bytes start =
      some (.int (Int.ofNat ((ABI.bytesToWord ((bytes.drop start).take 32)).toNat %
        EVM.twoPow 8)), start + 32) := by
  simp only [abiUInt8Int, decodeScalarWordWithMode?, readWord?, readBytes?, decodeABIWord?, bind,
    Option.bind]
  rw [if_pos hlen]
  rfl

theorem decodeScalarWordWithMode_legacy_uint48_ok {bytes : List UInt8} {start : Nat}
    (hlen : ((bytes.drop start).take 32).length = 32) :
    decodeScalarWordWithMode? DecodeMode.legacySolc05 abiUInt48 bytes start =
      some (.int (Int.ofNat ((ABI.bytesToWord ((bytes.drop start).take 32)).toNat %
        EVM.twoPow 48)), start + 32) := by
  simp only [abiUInt48, abiUInt48Int, decodeScalarWordWithMode?, readWord?, readBytes?, bind,
    Option.bind]
  rw [if_pos hlen]
  simp [decodeABIWord?, UInt256.toNat, normalizeInt]

theorem decodeScalarWordWithMode_legacy_uint96_ok {bytes : List UInt8} {start : Nat}
    (hlen : ((bytes.drop start).take 32).length = 32) :
    decodeScalarWordWithMode? DecodeMode.legacySolc05 abiUInt96 bytes start =
      some (.int (Int.ofNat ((ABI.bytesToWord ((bytes.drop start).take 32)).toNat %
        EVM.twoPow 96)), start + 32) := by
  simp only [abiUInt96, abiUInt96Int, decodeScalarWordWithMode?, readWord?, readBytes?, bind,
    Option.bind]
  rw [if_pos hlen]
  simp [decodeABIWord?, UInt256.toNat, normalizeInt]

theorem decodeScalarWordWithMode_legacyInt256_ok {bytes : List UInt8} {start : Nat}
    (hlen : ((bytes.drop start).take 32).length = 32) :
    decodeScalarWordWithMode? DecodeMode.legacySolc05 abiInt256 bytes start =
      some
        (.int
          (if (ABI.bytesToWord ((bytes.drop start).take 32)).toNat < EVM.twoPow 255 then
            Int.ofNat (ABI.bytesToWord ((bytes.drop start).take 32)).toNat
          else
            Int.ofNat (ABI.bytesToWord ((bytes.drop start).take 32)).toNat -
              Int.ofNat EVM.wordModulus),
          start + 32) := by
  simp [decodeScalarWordWithMode?, readWord?, readBytes?, decodeABIWord?, abiInt256,
    abiInt256Int, hlen]
  exact normalizeInt_sint256_word (ABI.bytesToWord ((bytes.drop start).take 32))


theorem decodeScalarWords_addr_uint256_uint256_ok {bytes : List UInt8}
    (hlen0 : (bytes.take 32).length = 32)
    (hlen32 : ((bytes.drop 32).take 32).length = 32)
    (hlen64 : ((bytes.drop 64).take 32).length = 32)
    (hcanon : (ABI.bytesToWord (bytes.take 32)).toNat < EVM.addressModulus) :
    decodeScalarWords? [.elem .address, abiUInt256, abiUInt256] bytes 0 =
      some [.address (Ethereum.AccountAddress.ofNat (ABI.bytesToWord (bytes.take 32)).toNat),
        .int (Int.ofNat (ABI.bytesToWord ((bytes.drop 32).take 32)).toNat),
        .int (Int.ofNat (ABI.bytesToWord ((bytes.drop 64).take 32)).toNat)] := by
  exact Reasoning.Theory.decodeScalarWords_address_uint256_uint256_ok
    hlen0 hlen32 hlen64 hcanon


theorem decodeScalarWords_addr_uint256_uint256_none_noncanon {bytes : List UInt8}
    (hlen0 : (bytes.take 32).length = 32)
    (hnc : ¬ (ABI.bytesToWord (bytes.take 32)).toNat < EVM.addressModulus) :
    decodeScalarWords? [.elem .address, abiUInt256, abiUInt256] bytes 0 = none := by
  exact Reasoning.Theory.decodeScalarWords_address_uint256_uint256_none_noncanon0
    hlen0 hnc


theorem decodeScalarWords_addr_uint256_uint256_none_short {bytes : List UInt8}
    (hshort : bytes.length < 96) :
    decodeScalarWords? [.elem .address, abiUInt256, abiUInt256] bytes 0 = none := by
  exact Reasoning.Theory.decodeScalarWords_address_uint256_uint256_none_short hshort


theorem decodeCalldata_addr_uint256_uint256_ok {cd : ByteArray} {x y z : Solm.Ident}
    (hsz100 : 100 ≤ cd.size) (hbig : cd.size < 2 ^ 255 + 4)
    (hcanon : (calldataWord cd 4).toNat < EVM.addressModulus) :
    decodeCalldata [x, y, z] [.elem .address, abiUInt256, abiUInt256] cd =
      some ((((∅ : Solm.Store).insert x
        (.address (Ethereum.AccountAddress.ofNat (calldataWord cd 4).toNat))).insert y
        (.int (Int.ofNat (calldataWord cd 36).toNat))).insert z
        (.int (Int.ofNat (calldataWord cd 68).toNat))) := by
  exact Reasoning.Theory.decodeCalldata_address_uint256_uint256_ok
    hsz100 hbig hcanon


theorem decodeCalldata_addr_uint256_uint256_none_noncanon {cd : ByteArray}
    {x y z : Solm.Ident}
    (hsz100 : 100 ≤ cd.size) (hbig : cd.size < 2 ^ 255 + 4)
    (hnc : ¬ (calldataWord cd 4).toNat < EVM.addressModulus) :
    decodeCalldata [x, y, z] [.elem .address, abiUInt256, abiUInt256] cd = none := by
  exact Reasoning.Theory.decodeCalldata_address_uint256_uint256_none_noncanon0
    hsz100 hbig hnc


theorem decodeCalldata_addr_uint256_uint256_none_short {cd : ByteArray}
    {x y z : Solm.Ident}
    (hsz4 : 4 ≤ cd.size) (hshort : cd.size < 100) :
    decodeCalldata [x, y, z] [.elem .address, abiUInt256, abiUInt256] cd = none := by
  exact Reasoning.Theory.decodeCalldata_address_uint256_uint256_none_short hsz4 hshort


theorem decodeCalldata_addr_uint256_uint256_none_huge {cd : ByteArray}
    {x y z : Solm.Ident}
    (hbig : 2 ^ 255 + 4 ≤ cd.size) :
    decodeCalldata [x, y, z] [.elem .address, abiUInt256, abiUInt256] cd = none := by
  exact Reasoning.Theory.decodeCalldata_address_uint256_uint256_none_huge hbig


theorem decodeReturnValues_uint256_ok {returndata : ByteArray}
    (hlo : 32 ≤ returndata.size) (hhi : returndata.size < (2 : Nat) ^ 255) :
    ABI.decodeReturnValues? [abiUInt256] returndata =
      some [(.int (Int.ofNat (fromByteArrayBigEndian (returndata.extract 0 32))))] := by
  have hlen : returndata.toList.length = returndata.size := by
    rw [byteArray_toList_eq, Array.length_toList]; rfl
  have htake0 : (returndata.toList.take 32).length = 32 := by
    rw [List.length_take, hlen]
    omega
  have hword := bytesToWord_take32_eq_extract0_32 (returndata := returndata)
  rw [decodeReturnValues_scalarWords_eq (types := [abiUInt256]) (returndata := returndata)
    (by decide)]
  rw [if_neg (by
    rintro ⟨_, hhuge⟩
    rw [hlen] at hhuge
    omega)]
  rw [decodeScalarWords_uint256_ok (bytes := returndata.toList) htake0]
  simp [hword, UInt256.toNat_ofNat_of_lt (fromByteArrayBigEndian_extract0_32_lt hlo)]

theorem decodeReturnValues_uint256_none_short {returndata : ByteArray}
    (hshort : returndata.size < 32) :
    ABI.decodeReturnValues? [abiUInt256] returndata = none := by
  have hlen : returndata.toList.length = returndata.size := by
    rw [byteArray_toList_eq, Array.length_toList]; rfl
  rw [decodeReturnValues_scalarWords_eq (types := [abiUInt256]) (returndata := returndata)
    (by decide)]
  rw [if_neg (by
    rintro ⟨_, hhuge⟩
    rw [hlen] at hhuge
    omega)]
  rw [decodeScalarWords_uint256_none_short (bytes := returndata.toList) (by rw [hlen]; omega)]

theorem decodeReturnValues_uint256_none_huge {returndata : ByteArray}
    (hhuge : (2 : Nat) ^ 255 ≤ returndata.size) :
    ABI.decodeReturnValues? [abiUInt256] returndata = none := by
  have hlen : returndata.toList.length = returndata.size := by
    rw [byteArray_toList_eq, Array.length_toList]; rfl
  rw [decodeReturnValues_scalarWords_eq (types := [abiUInt256]) (returndata := returndata)
    (by decide)]
  rw [if_pos (by exact ⟨by simp, by rw [hlen]; exact hhuge⟩)]

def BoolReturnValid (out : ByteArray) : Prop :=
  32 ≤ out.size ∧ (calldataWord out 0 = ⟨0⟩ ∨ calldataWord out 0 = ⟨1⟩)

theorem decodeReturnBool_long {out : ByteArray} (hl : 32 ≤ out.size) (hb : out.size < 2 ^ 255) :
    ABI.decodeReturnValue? abiBool out =
      if calldataWord out 0 = ⟨0⟩ then some (.bool false)
      else if calldataWord out 0 = ⟨1⟩ then some (.bool true) else none := by
  have hlen : out.toList.length = out.size := by
    rw [byteArray_toList_eq, Array.length_toList]
    rfl
  have hword := decode_word_at_eq out 0 (by omega) (by decide)
  have h32 : ((out.toList.drop 0).take 32).length = 32 := by
    simp only [List.drop_zero, List.length_take, hlen]
    omega
  unfold ABI.decodeReturnValue?
  rw [decodeReturnValues_scalarWords_eq (by decide)]
  rw [if_neg (by simp only [List.isEmpty_cons, hlen]; omega)]
  by_cases hz : calldataWord out 0 = ⟨0⟩
  · have hd := decodeScalarWord_bool_ok_zero h32 (hword.trans hz)
    simp only [abiBool, decodeScalarWords?, hd, bind, Option.bind, if_pos hz]
  · by_cases ho : calldataWord out 0 = ⟨1⟩
    · have hd := decodeScalarWord_bool_ok_one h32 (hword.trans ho)
      simp only [abiBool, decodeScalarWords?, hd, bind, Option.bind, if_neg hz, if_pos ho]
    · have hd := decodeScalarWord_bool_none_noncanon h32
        (fun he => hz (hword.symm.trans he)) (fun he => ho (hword.symm.trans he))
      simp only [abiBool, decodeScalarWords?, hd, bind, Option.bind, if_neg hz, if_neg ho]

theorem decodeReturnBool_short {out : ByteArray} (hl : out.size < 32) :
    ABI.decodeReturnValue? abiBool out = none := by
  have hlen : out.toList.length = out.size := by
    rw [byteArray_toList_eq, Array.length_toList]
    rfl
  have h32 : ¬ ((out.toList.drop 0).take 32).length = 32 := by
    simp only [List.drop_zero, List.length_take, hlen]
    omega
  unfold ABI.decodeReturnValue?
  rw [decodeReturnValues_scalarWords_eq (by decide)]
  rw [if_neg (by simp only [List.isEmpty_cons, hlen]; omega)]
  simp only [abiBool, decodeScalarWords?, decodeScalarWord_bool_none_short h32, bind, Option.bind]

theorem decodeReturnBool_valid {out : ByteArray} (hv : BoolReturnValid out)
    (hb : out.size < 2 ^ 255) :
    ABI.decodeReturnValue? abiBool out = some (.bool (decide (calldataWord out 0 ≠ ⟨0⟩))) := by
  rw [decodeReturnBool_long hv.1 hb]
  rcases hv.2 with hz | ho
  · rw [hz]
    decide
  · rw [ho]
    decide

theorem decodeReturnBool_invalid {out : ByteArray} (hv : ¬ BoolReturnValid out)
    (hb : out.size < 2 ^ 255) : ABI.decodeReturnValue? abiBool out = none := by
  by_cases hl : 32 ≤ out.size
  · have hz : calldataWord out 0 ≠ ⟨0⟩ := fun he => hv ⟨hl, Or.inl he⟩
    have ho : calldataWord out 0 ≠ ⟨1⟩ := fun he => hv ⟨hl, Or.inr he⟩
    rw [decodeReturnBool_long hl hb, if_neg hz, if_neg ho]
  · exact decodeReturnBool_short (by omega)

/-- Recover the scalar byte list from an already-proved one-word return encoding. -/
theorem scalarValueEncoding {ty : ABIType} {value : Value} {w : UInt256}
    (hhead : abiTupleHeadSize? [ty] = some 32) (hdyn : isDynamicABIType ty = false)
    (hret : encodeReturnValue? ty value = some (UInt256.toByteArray w)) :
    encodeABIValue? ty value = some (EVM.Word.toBytesBE w) := by
  cases henc : encodeABIValue? ty value with
  | none =>
    simp only [encodeReturnValue?, encodeReturnValues?, encodeABIValues?, hhead,
      encodeABIValuesFrom?, henc, bind, Option.bind] at hret
    cases hret
  | some bs =>
    have hbytes : (⟨bs.toArray⟩ : ByteArray) = UInt256.toByteArray w := by
      simpa only [encodeReturnValue?, encodeReturnValues?, encodeABIValues?, hhead,
        encodeABIValuesFrom?, henc, hdyn, bind, Option.bind, if_false,
        Bool.false_eq_true, List.nil_append, List.append_nil, Option.some.injEq] using hret
    have heq : bs = EVM.Word.toBytesBE w := by
      rw [toByteArray_eq_toBytesBE] at hbytes
      simpa using congrArg (fun b : ByteArray => b.data.toList) hbytes
    exact congrArg some heq

theorem decodeCalldata_legacyUint256_uint256_address_address_ok {cd : ByteArray}
    {w x y z : Solm.Ident} (hsz132 : 132 ≤ cd.size) :
    decodeCalldataWithMode DecodeMode.legacySolc05 [w, x, y, z]
        [abiUInt256, abiUInt256, abiAddress, abiAddress] cd =
      some (((((∅ : Solm.Store).insert w
        (.int (Int.ofNat (calldataWord cd 4).toNat))).insert x
        (.int (Int.ofNat (calldataWord cd 36).toNat))).insert y
        (.address (AccountAddress.ofNat (calldataWord cd 68).toNat))).insert z
        (.address (AccountAddress.ofNat (calldataWord cd 100).toNat))) := by
  have htlen : cd.toList.length = cd.size := by
    rw [byteArray_toList_eq, Array.length_toList]
    rfl
  have htake4 : ((cd.toList.drop 4).take 32).length = 32 := by
    rw [List.length_take, List.length_drop, htlen]
    omega
  have htake36 : ((cd.toList.drop 4).drop 32 |>.take 32).length = 32 := by
    rw [List.length_take, List.length_drop, List.length_drop, htlen]
    omega
  have htake68 : ((cd.toList.drop 4).drop 64 |>.take 32).length = 32 := by
    rw [List.length_take, List.length_drop, List.length_drop, htlen]
    omega
  have htake100 : ((cd.toList.drop 4).drop 96 |>.take 32).length = 32 := by
    rw [List.length_take, List.length_drop, List.length_drop, htlen]
    omega
  have hword4 : ABI.bytesToWord ((cd.toList.drop 4).take 32) = calldataWord cd 4 :=
    decode_word_at_eq cd 4 (by omega) (by norm_num)
  have hword36 : ABI.bytesToWord (((cd.toList.drop 4).drop 32).take 32) =
      calldataWord cd 36 := by
    simpa [List.drop_drop, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using
      decode_word_at_eq cd 36 (by omega) (by norm_num)
  have hword68 : ABI.bytesToWord (((cd.toList.drop 4).drop 64).take 32) =
      calldataWord cd 68 := by
    simpa [List.drop_drop, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using
      decode_word_at_eq cd 68 (by omega) (by norm_num)
  have hword100 : ABI.bytesToWord (((cd.toList.drop 4).drop 96).take 32) =
      calldataWord cd 100 := by
    simpa [List.drop_drop, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using
      decode_word_at_eq cd 100 (by omega) (by norm_num)
  rw [decodeCalldataWithMode_legacyScalarWords_eq (names := [w, x, y, z])
    (types := [abiUInt256, abiUInt256, abiAddress, abiAddress]) (cd := cd) (by decide)]
  rw [if_neg (by rw [htlen]; omega : ¬ cd.toList.length < 4)]
  simp only [decodeScalarWordsWithMode?]
  have hdecode0 :
      decodeScalarWordWithMode? DecodeMode.legacySolc05 abiUInt256 (cd.toList.drop 4) 0 =
        some (.int (Int.ofNat (ABI.bytesToWord ((cd.toList.drop 4).take 32)).toNat),
          0 + 32) := by
    simpa [abiUInt256, abiUInt256Int] using
      decodeScalarWordWithMode_uint256_ok (mode := DecodeMode.legacySolc05)
        (bytes := cd.toList.drop 4) (start := 0) htake4
  have hdecode32 :
      decodeScalarWordWithMode? DecodeMode.legacySolc05 abiUInt256 (cd.toList.drop 4) 32 =
        some (.int (Int.ofNat
          (ABI.bytesToWord (((cd.toList.drop 4).drop 32).take 32)).toNat), 32 + 32) := by
    simpa [abiUInt256, abiUInt256Int] using
      decodeScalarWordWithMode_uint256_ok (mode := DecodeMode.legacySolc05)
        (bytes := cd.toList.drop 4) (start := 32) htake36
  have hdecode64 :
      decodeScalarWordWithMode? DecodeMode.legacySolc05 abiAddress (cd.toList.drop 4) 64 =
        some (.address (AccountAddress.ofNat
          (ABI.bytesToWord (((cd.toList.drop 4).drop 64).take 32)).toNat), 64 + 32) := by
    simpa [abiAddress] using
      decodeScalarWord_legacyAddress_ok (bytes := cd.toList.drop 4) (start := 64) htake68
  have hdecode96 :
      decodeScalarWordWithMode? DecodeMode.legacySolc05 abiAddress (cd.toList.drop 4) 96 =
        some (.address (AccountAddress.ofNat
          (ABI.bytesToWord (((cd.toList.drop 4).drop 96).take 32)).toNat), 96 + 32) := by
    simpa [abiAddress] using
      decodeScalarWord_legacyAddress_ok (bytes := cd.toList.drop 4) (start := 96) htake100
  rw [hdecode0, hdecode32, hdecode64, hdecode96]
  simp only [Option.bind, bind]
  change decodeCalldata.insertValues [w, x, y, z]
      [.int (Int.ofNat (ABI.bytesToWord ((cd.toList.drop 4).take 32)).toNat),
        .int (Int.ofNat (ABI.bytesToWord (((cd.toList.drop 4).drop 32).take 32)).toNat),
        .address (AccountAddress.ofNat
          (ABI.bytesToWord (((cd.toList.drop 4).drop 64).take 32)).toNat),
        .address (AccountAddress.ofNat
          (ABI.bytesToWord (((cd.toList.drop 4).drop 96).take 32)).toNat)] ∅ =
    some (((((∅ : Solm.Store).insert w
      (.int (Int.ofNat (calldataWord cd 4).toNat))).insert x
      (.int (Int.ofNat (calldataWord cd 36).toNat))).insert y
      (.address (AccountAddress.ofNat (calldataWord cd 68).toNat))).insert z
      (.address (AccountAddress.ofNat (calldataWord cd 100).toNat)))
  rw [hword4, hword36, hword68, hword100]
  simp [decodeCalldata.insertValues]

theorem decodeCalldata_legacyUint256_uint256_address_address_none_short {cd : ByteArray}
    {w x y z : Solm.Ident} (hsz4 : 4 ≤ cd.size) (hshort : cd.size < 132) :
    decodeCalldataWithMode DecodeMode.legacySolc05 [w, x, y, z]
      [abiUInt256, abiUInt256, abiAddress, abiAddress] cd = none := by
  have htlen : cd.toList.length = cd.size := by
    rw [byteArray_toList_eq, Array.length_toList]
    rfl
  rw [decodeCalldataWithMode_legacyScalarWords_eq (names := [w, x, y, z])
    (types := [abiUInt256, abiUInt256, abiAddress, abiAddress]) (cd := cd) (by decide)]
  rw [if_neg (by rw [htlen]; omega : ¬ cd.toList.length < 4)]
  by_cases hlen0 : 32 ≤ (cd.toList.drop 4).length
  · have htake0 : ((cd.toList.drop 4).take 32).length = 32 := by
      rw [List.length_take]
      omega
    simp only [decodeScalarWordsWithMode?]
    have hdecode0 :
        decodeScalarWordWithMode? DecodeMode.legacySolc05 abiUInt256 (cd.toList.drop 4) 0 =
          some (.int (Int.ofNat (ABI.bytesToWord ((cd.toList.drop 4).take 32)).toNat),
            0 + 32) := by
      simpa [abiUInt256, abiUInt256Int] using
        decodeScalarWordWithMode_uint256_ok (mode := DecodeMode.legacySolc05)
          (bytes := cd.toList.drop 4) (start := 0) htake0
    rw [hdecode0]
    by_cases hlen32 : 64 ≤ (cd.toList.drop 4).length
    · have htake32 : (((cd.toList.drop 4).drop 32).take 32).length = 32 := by
        rw [List.length_take, List.length_drop]
        omega
      have hdecode32 :
          decodeScalarWordWithMode? DecodeMode.legacySolc05 abiUInt256 (cd.toList.drop 4) 32 =
            some (.int (Int.ofNat
              (ABI.bytesToWord (((cd.toList.drop 4).drop 32).take 32)).toNat), 32 + 32) := by
        simpa [abiUInt256, abiUInt256Int] using
          decodeScalarWordWithMode_uint256_ok (mode := DecodeMode.legacySolc05)
            (bytes := cd.toList.drop 4) (start := 32) htake32
      rw [hdecode32]
      by_cases hlen64 : 96 ≤ (cd.toList.drop 4).length
      · have htake64 : (((cd.toList.drop 4).drop 64).take 32).length = 32 := by
          rw [List.length_take, List.length_drop]
          omega
        have hdecode64 :
            decodeScalarWordWithMode? DecodeMode.legacySolc05 abiAddress (cd.toList.drop 4) 64 =
              some (.address (AccountAddress.ofNat
                (ABI.bytesToWord (((cd.toList.drop 4).drop 64).take 32)).toNat), 64 + 32) := by
          simpa [abiAddress] using
            decodeScalarWord_legacyAddress_ok (bytes := cd.toList.drop 4) (start := 64)
              htake64
        rw [hdecode64]
        have htake96n : ¬ (((cd.toList.drop 4).drop 96).take 32).length = 32 := by
          rw [List.length_take, List.length_drop, List.length_drop, htlen]
          omega
        have hdecode96 :
            decodeScalarWordWithMode? DecodeMode.legacySolc05 abiAddress (cd.toList.drop 4) 96 =
              none := by
          simpa [abiAddress] using
            decodeScalarWord_legacyAddress_none_short (bytes := cd.toList.drop 4)
              (start := 96) htake96n
        rw [hdecode96]
        simp only [Option.bind, bind]
      · have htake64n : ¬ (((cd.toList.drop 4).drop 64).take 32).length = 32 := by
          rw [List.length_take, List.length_drop]
          omega
        have hdecode64 :
            decodeScalarWordWithMode? DecodeMode.legacySolc05 abiAddress (cd.toList.drop 4) 64 =
              none := by
          simpa [abiAddress] using
            decodeScalarWord_legacyAddress_none_short (bytes := cd.toList.drop 4)
              (start := 64) htake64n
        rw [hdecode64]
        simp only [Option.bind, bind]
    · have htake32n : ¬ (((cd.toList.drop 4).drop 32).take 32).length = 32 := by
        rw [List.length_take, List.length_drop]
        omega
      have hdecode32 :
          decodeScalarWordWithMode? DecodeMode.legacySolc05 abiUInt256 (cd.toList.drop 4) 32 =
            none := by
        simpa [abiUInt256, abiUInt256Int] using
          decodeScalarWordWithMode_uint256_none_short (mode := DecodeMode.legacySolc05)
            (bytes := cd.toList.drop 4) (start := 32) htake32n
      rw [hdecode32]
      simp only [Option.bind, bind]
  · have htake0n : ¬ ((cd.toList.drop 4).take 32).length = 32 := by
      rw [List.length_take]
      omega
    simp only [decodeScalarWordsWithMode?]
    have hdecode0 :
        decodeScalarWordWithMode? DecodeMode.legacySolc05 abiUInt256 (cd.toList.drop 4) 0 =
          none := by
      simpa [abiUInt256, abiUInt256Int] using
        decodeScalarWordWithMode_uint256_none_short (mode := DecodeMode.legacySolc05)
          (bytes := cd.toList.drop 4) (start := 0) htake0n
    rw [hdecode0]
    simp only [Option.bind, bind]

theorem decodeCalldata_legacyUint256_address_ok {cd : ByteArray} {x y : Solm.Ident}
    (hsz68 : 68 ≤ cd.size) :
    decodeCalldataWithMode DecodeMode.legacySolc05 [x, y] [abiUInt256, abiAddress] cd =
      some (((∅ : Solm.Store).insert x
        (.int (Int.ofNat (calldataWord cd 4).toNat))).insert y
        (.address (AccountAddress.ofNat (calldataWord cd 36).toNat))) := by
  have htlen : cd.toList.length = cd.size := by
    rw [byteArray_toList_eq, Array.length_toList]
    rfl
  have htake4 : ((cd.toList.drop 4).take 32).length = 32 := by
    rw [List.length_take, List.length_drop, htlen]
    omega
  have htake36 : ((cd.toList.drop 4).drop 32 |>.take 32).length = 32 := by
    rw [List.length_take, List.length_drop, List.length_drop, htlen]
    omega
  have hword4 : ABI.bytesToWord ((cd.toList.drop 4).take 32) = calldataWord cd 4 :=
    decode_word_at_eq cd 4 (by omega) (by norm_num)
  have hword36 : ABI.bytesToWord (((cd.toList.drop 4).drop 32).take 32) =
      calldataWord cd 36 := by
    simpa [List.drop_drop, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using
      decode_word_at_eq cd 36 (by omega) (by norm_num)
  rw [decodeCalldataWithMode_legacyScalarWords_eq (names := [x, y])
    (types := [abiUInt256, abiAddress]) (cd := cd) (by decide)]
  rw [if_neg (by rw [htlen]; omega : ¬ cd.toList.length < 4)]
  simp only [decodeScalarWordsWithMode?]
  have hdecode0 :
      decodeScalarWordWithMode? DecodeMode.legacySolc05 abiUInt256 (cd.toList.drop 4) 0 =
        some (.int (Int.ofNat (ABI.bytesToWord ((cd.toList.drop 4).take 32)).toNat),
          0 + 32) := by
    simpa [abiUInt256, abiUInt256Int] using
      decodeScalarWordWithMode_uint256_ok (mode := DecodeMode.legacySolc05)
        (bytes := cd.toList.drop 4) (start := 0) htake4
  have hdecode32 :
      decodeScalarWordWithMode? DecodeMode.legacySolc05 abiAddress (cd.toList.drop 4) 32 =
        some (.address (AccountAddress.ofNat
          (ABI.bytesToWord (((cd.toList.drop 4).drop 32).take 32)).toNat), 32 + 32) := by
    simpa [abiAddress] using
      decodeScalarWord_legacyAddress_ok (bytes := cd.toList.drop 4) (start := 32) htake36
  rw [hdecode0, hdecode32]
  simp only [Option.bind, bind]
  change decodeCalldata.insertValues [x, y]
      [.int (Int.ofNat (ABI.bytesToWord ((cd.toList.drop 4).take 32)).toNat),
        .address (AccountAddress.ofNat
          (ABI.bytesToWord (((cd.toList.drop 4).drop 32).take 32)).toNat)] ∅ =
    some (((∅ : Solm.Store).insert x
      (.int (Int.ofNat (calldataWord cd 4).toNat))).insert y
      (.address (AccountAddress.ofNat (calldataWord cd 36).toNat)))
  rw [hword4, hword36]
  simp [decodeCalldata.insertValues]

theorem decodeCalldata_legacyUint256_address_none_short {cd : ByteArray}
    {x y : Solm.Ident} (hsz4 : 4 ≤ cd.size) (hshort : cd.size < 68) :
    decodeCalldataWithMode DecodeMode.legacySolc05 [x, y] [abiUInt256, abiAddress] cd = none := by
  have htlen : cd.toList.length = cd.size := by
    rw [byteArray_toList_eq, Array.length_toList]
    rfl
  rw [decodeCalldataWithMode_legacyScalarWords_eq (names := [x, y])
    (types := [abiUInt256, abiAddress]) (cd := cd) (by decide)]
  rw [if_neg (by rw [htlen]; omega : ¬ cd.toList.length < 4)]
  by_cases hlen0 : 32 ≤ (cd.toList.drop 4).length
  · have htake0 : ((cd.toList.drop 4).take 32).length = 32 := by
      rw [List.length_take]
      omega
    simp only [decodeScalarWordsWithMode?]
    have hdecode0 :
        decodeScalarWordWithMode? DecodeMode.legacySolc05 abiUInt256 (cd.toList.drop 4) 0 =
          some (.int (Int.ofNat (ABI.bytesToWord ((cd.toList.drop 4).take 32)).toNat),
            0 + 32) := by
      simpa [abiUInt256, abiUInt256Int] using
        decodeScalarWordWithMode_uint256_ok (mode := DecodeMode.legacySolc05)
          (bytes := cd.toList.drop 4) (start := 0) htake0
    rw [hdecode0]
    have htake32n : ¬ (((cd.toList.drop 4).drop 32).take 32).length = 32 := by
      rw [List.length_take, List.length_drop, List.length_drop, htlen]
      omega
    have hdecode32 :
        decodeScalarWordWithMode? DecodeMode.legacySolc05 abiAddress (cd.toList.drop 4) 32 =
          none := by
      simpa [abiAddress] using
        decodeScalarWord_legacyAddress_none_short (bytes := cd.toList.drop 4) (start := 32)
          htake32n
    rw [hdecode32]
    simp only [Option.bind, bind]
  · have htake0n : ¬ ((cd.toList.drop 4).take 32).length = 32 := by
      rw [List.length_take]
      omega
    simp only [decodeScalarWordsWithMode?]
    have hdecode0 :
        decodeScalarWordWithMode? DecodeMode.legacySolc05 abiUInt256 (cd.toList.drop 4) 0 =
          none := by
      simpa [abiUInt256, abiUInt256Int] using
        decodeScalarWordWithMode_uint256_none_short (mode := DecodeMode.legacySolc05)
          (bytes := cd.toList.drop 4) (start := 0) htake0n
    rw [hdecode0]
    simp only [Option.bind, bind]

theorem decodeCalldata_legacyAddress_uint256_uint256_ok {cd : ByteArray}
    {x y z : Solm.Ident}
    (hsz100 : 100 ≤ cd.size) :
    decodeCalldataWithMode DecodeMode.legacySolc05 [x, y, z]
        [abiAddress, abiUInt256, abiUInt256] cd =
      some ((((∅ : Solm.Store).insert x
        (.address (AccountAddress.ofNat (calldataWord cd 4).toNat))).insert y
        (.int (Int.ofNat (calldataWord cd 36).toNat))).insert z
        (.int (Int.ofNat (calldataWord cd 68).toNat))) := by
  have htlen : cd.toList.length = cd.size := by
    rw [byteArray_toList_eq, Array.length_toList]
    rfl
  have htake4 : ((cd.toList.drop 4).take 32).length = 32 := by
    rw [List.length_take, List.length_drop, htlen]
    omega
  have htake36 : (((cd.toList.drop 4).drop 32).take 32).length = 32 := by
    rw [List.length_take, List.length_drop, List.length_drop, htlen]
    omega
  have htake68 : (((cd.toList.drop 4).drop 64).take 32).length = 32 := by
    rw [List.length_take, List.length_drop, List.length_drop, htlen]
    omega
  have hword4 : ABI.bytesToWord ((cd.toList.drop 4).take 32) = calldataWord cd 4 :=
    decode_word_at_eq cd 4 (by omega) (by norm_num)
  have hword36 : ABI.bytesToWord (((cd.toList.drop 4).drop 32).take 32) =
      calldataWord cd 36 := by
    simpa [List.drop_drop, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc]
      using decode_word_at_eq cd 36 (by omega) (by norm_num)
  have hword68 : ABI.bytesToWord (((cd.toList.drop 4).drop 64).take 32) =
      calldataWord cd 68 := by
    simpa [List.drop_drop, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc]
      using decode_word_at_eq cd 68 (by omega) (by norm_num)
  rw [decodeCalldataWithMode_legacyScalarWords_eq (names := [x, y, z])
    (types := [abiAddress, abiUInt256, abiUInt256]) (cd := cd) (by decide)]
  rw [if_neg (by rw [htlen]; omega : ¬ cd.toList.length < 4)]
  simp only [decodeScalarWordsWithMode?]
  rw [decodeScalarWord_legacyAddress_ok (bytes := cd.toList.drop 4) htake4]
  rw [decodeScalarWordWithMode_uint256_ok (mode := DecodeMode.legacySolc05)
    (bytes := cd.toList.drop 4) (start := 32) htake36]
  rw [decodeScalarWordWithMode_uint256_ok (mode := DecodeMode.legacySolc05)
    (bytes := cd.toList.drop 4) (start := 64) htake68]
  change decodeCalldata.insertValues [x, y, z]
      [.address (AccountAddress.ofNat
          (ABI.bytesToWord ((cd.toList.drop 4).take 32)).toNat),
        .int (Int.ofNat
          (ABI.bytesToWord (((cd.toList.drop 4).drop 32).take 32)).toNat),
        .int (Int.ofNat
          (ABI.bytesToWord (((cd.toList.drop 4).drop 64).take 32)).toNat)] ∅ =
    some ((((∅ : Solm.Store).insert x
      (.address (AccountAddress.ofNat (calldataWord cd 4).toNat))).insert y
      (.int (Int.ofNat (calldataWord cd 36).toNat))).insert z
      (.int (Int.ofNat (calldataWord cd 68).toNat)))
  rw [hword4, hword36, hword68]
  simp [decodeCalldata.insertValues]

theorem decodeCalldata_legacyAddress_uint256_uint256_none_short {cd : ByteArray}
    {x y z : Solm.Ident} (hsz4 : 4 ≤ cd.size) (hshort : cd.size < 100) :
    decodeCalldataWithMode DecodeMode.legacySolc05 [x, y, z]
        [abiAddress, abiUInt256, abiUInt256] cd = none := by
  have htlen : cd.toList.length = cd.size := by
    rw [byteArray_toList_eq, Array.length_toList]
    rfl
  rw [decodeCalldataWithMode_legacyScalarWords_eq (names := [x, y, z])
    (types := [abiAddress, abiUInt256, abiUInt256]) (cd := cd) (by decide)]
  rw [if_neg (by rw [htlen]; omega : ¬ cd.toList.length < 4)]
  by_cases hlen0 : 32 ≤ (cd.toList.drop 4).length
  · have htake0 : ((cd.toList.drop 4).take 32).length = 32 := by
      rw [List.length_take]
      omega
    simp only [decodeScalarWordsWithMode?]
    rw [decodeScalarWord_legacyAddress_ok (bytes := cd.toList.drop 4) htake0]
    by_cases hlen32 : 64 ≤ (cd.toList.drop 4).length
    · have htake32 : (((cd.toList.drop 4).drop 32).take 32).length = 32 := by
        rw [List.length_take, List.length_drop]
        omega
      rw [decodeScalarWordWithMode_uint256_ok (mode := DecodeMode.legacySolc05)
        (bytes := cd.toList.drop 4) (start := 32) htake32]
      have htake64n : ¬ (((cd.toList.drop 4).drop 64).take 32).length = 32 := by
        rw [List.length_take, List.length_drop, List.length_drop, htlen]
        omega
      rw [decodeScalarWordWithMode_uint256_none_short (mode := DecodeMode.legacySolc05)
        (start := 64) (by simpa using htake64n)]
      simp only [Option.bind, bind]
    · have htake32n : ¬ (((cd.toList.drop 4).drop 32).take 32).length = 32 := by
        rw [List.length_take, List.length_drop]
        omega
      rw [decodeScalarWordWithMode_uint256_none_short (mode := DecodeMode.legacySolc05)
        (start := 32) (by simpa using htake32n)]
      simp only [Option.bind, bind]
  · have htake0n : ¬ ((cd.toList.drop 4).take 32).length = 32 := by
      rw [List.length_take]
      omega
    simp only [decodeScalarWordsWithMode?]
    rw [decodeScalarWord_legacyAddress_none_short (start := 0) (by simpa using htake0n)]
    simp only [Option.bind, bind]

theorem decodeCalldata_legacyAddress_address_uint256_uint256_uint256_ok {cd : ByteArray}
    {x y z w v : Solm.Ident} (hsz164 : 164 ≤ cd.size) :
    decodeCalldataWithMode DecodeMode.legacySolc05 [x, y, z, w, v]
        [abiAddress, abiAddress, abiUInt256, abiUInt256, abiUInt256] cd =
      some ((((((∅ : Store).insert x
        (.address (AccountAddress.ofNat (calldataWord cd 4).toNat))).insert y
        (.address (AccountAddress.ofNat (calldataWord cd 36).toNat))).insert z
        (.int (Int.ofNat (calldataWord cd 68).toNat))).insert w
        (.int (Int.ofNat (calldataWord cd 100).toNat))).insert v
        (.int (Int.ofNat (calldataWord cd 132).toNat))) := by
  have hlen : cd.toList.length = cd.size := by
    rw [byteArray_toList_eq, Array.length_toList]
    rfl
  have htake4 : ((cd.toList.drop 4).take 32).length = 32 := by
    rw [List.length_take, List.length_drop, hlen]
    omega
  have htake36 : ((cd.toList.drop 4).drop 32 |>.take 32).length = 32 := by
    rw [List.length_take, List.length_drop, List.length_drop, hlen]
    omega
  have htake68 : ((cd.toList.drop 4).drop 64 |>.take 32).length = 32 := by
    rw [List.length_take, List.length_drop, List.length_drop, hlen]
    omega
  have htake100 : ((cd.toList.drop 4).drop 96 |>.take 32).length = 32 := by
    rw [List.length_take, List.length_drop, List.length_drop, hlen]
    omega
  have htake132 : ((cd.toList.drop 4).drop 128 |>.take 32).length = 32 := by
    rw [List.length_take, List.length_drop, List.length_drop, hlen]
    omega
  have hword4 : ABI.bytesToWord ((cd.toList.drop 4).take 32) = calldataWord cd 4 :=
    decode_word_at_eq cd 4 (by omega) (by norm_num)
  have hword36 :
      ABI.bytesToWord (((cd.toList.drop 4).drop 32).take 32) = calldataWord cd 36 := by
    simpa [List.drop_drop, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc]
      using decode_word_at_eq cd 36 (by omega) (by norm_num)
  have hword68 :
      ABI.bytesToWord (((cd.toList.drop 4).drop 64).take 32) = calldataWord cd 68 := by
    simpa [List.drop_drop, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc]
      using decode_word_at_eq cd 68 (by omega) (by norm_num)
  have hword100 :
      ABI.bytesToWord (((cd.toList.drop 4).drop 96).take 32) = calldataWord cd 100 := by
    simpa [List.drop_drop, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc]
      using decode_word_at_eq cd 100 (by omega) (by norm_num)
  have hword132 :
      ABI.bytesToWord (((cd.toList.drop 4).drop 128).take 32) = calldataWord cd 132 := by
    simpa [List.drop_drop, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc]
      using decode_word_at_eq cd 132 (by omega) (by norm_num)
  rw [decodeCalldataWithMode_legacyScalarWords_eq
    (names := [x, y, z, w, v])
    (types := [abiAddress, abiAddress, abiUInt256, abiUInt256, abiUInt256])
    (cd := cd) (by decide)]
  rw [if_neg (by rw [hlen]; omega : ¬ cd.toList.length < 4)]
  simp only [decodeScalarWordsWithMode?]
  rw [decodeScalarWord_legacyAddress_ok (bytes := cd.toList.drop 4)
    (start := 0) htake4]
  rw [decodeScalarWord_legacyAddress_ok (bytes := cd.toList.drop 4)
    (start := 32) htake36]
  rw [decodeScalarWordWithMode_uint256_ok (mode := DecodeMode.legacySolc05)
    (bytes := cd.toList.drop 4) (start := 64) htake68]
  rw [decodeScalarWordWithMode_uint256_ok (mode := DecodeMode.legacySolc05)
    (bytes := cd.toList.drop 4) (start := 96) htake100]
  rw [decodeScalarWordWithMode_uint256_ok (mode := DecodeMode.legacySolc05)
    (bytes := cd.toList.drop 4) (start := 128) htake132]
  simp only [Option.bind, bind]
  change decodeCalldata.insertValues [x, y, z, w, v]
      [.address (AccountAddress.ofNat (ABI.bytesToWord ((cd.toList.drop 4).take 32)).toNat),
        .address (AccountAddress.ofNat
          (ABI.bytesToWord (((cd.toList.drop 4).drop 32).take 32)).toNat),
        .int (Int.ofNat
          (ABI.bytesToWord (((cd.toList.drop 4).drop 64).take 32)).toNat),
        .int (Int.ofNat
          (ABI.bytesToWord (((cd.toList.drop 4).drop 96).take 32)).toNat),
        .int (Int.ofNat
          (ABI.bytesToWord (((cd.toList.drop 4).drop 128).take 32)).toNat)] ∅ =
    some ((((((∅ : Store).insert x
      (.address (AccountAddress.ofNat (calldataWord cd 4).toNat))).insert y
      (.address (AccountAddress.ofNat (calldataWord cd 36).toNat))).insert z
      (.int (Int.ofNat (calldataWord cd 68).toNat))).insert w
      (.int (Int.ofNat (calldataWord cd 100).toNat))).insert v
      (.int (Int.ofNat (calldataWord cd 132).toNat)))
  rw [hword4, hword36, hword68, hword100, hword132]
  rfl

theorem decodeCalldata_legacyAddress_address_uint256_uint256_uint256_none_short
    {cd : ByteArray} {x y z w v : Solm.Ident}
    (hsz4 : 4 ≤ cd.size) (hshort : cd.size < 164) :
    decodeCalldataWithMode DecodeMode.legacySolc05 [x, y, z, w, v]
      [abiAddress, abiAddress, abiUInt256, abiUInt256, abiUInt256] cd = none := by
  have hlen : cd.toList.length = cd.size := by
    rw [byteArray_toList_eq, Array.length_toList]
    rfl
  rw [decodeCalldataWithMode_legacyScalarWords_eq
    (names := [x, y, z, w, v])
    (types := [abiAddress, abiAddress, abiUInt256, abiUInt256, abiUInt256])
    (cd := cd) (by decide)]
  rw [if_neg (by rw [hlen]; omega : ¬ cd.toList.length < 4)]
  by_cases hlen0 : 32 ≤ (cd.toList.drop 4).length
  · have htake0 : ((cd.toList.drop 4).take 32).length = 32 := by
      rw [List.length_take]
      omega
    simp only [decodeScalarWordsWithMode?]
    rw [decodeScalarWord_legacyAddress_ok (bytes := cd.toList.drop 4)
      (start := 0) htake0]
    by_cases hlen32 : 64 ≤ (cd.toList.drop 4).length
    · have htake32 : (((cd.toList.drop 4).drop 32).take 32).length = 32 := by
        rw [List.length_take, List.length_drop]
        omega
      rw [decodeScalarWord_legacyAddress_ok (bytes := cd.toList.drop 4)
        (start := 32) htake32]
      by_cases hlen64 : 96 ≤ (cd.toList.drop 4).length
      · have htake64 : (((cd.toList.drop 4).drop 64).take 32).length = 32 := by
          rw [List.length_take, List.length_drop]
          omega
        rw [decodeScalarWordWithMode_uint256_ok (mode := DecodeMode.legacySolc05)
          (bytes := cd.toList.drop 4) (start := 64) htake64]
        by_cases hlen96 : 128 ≤ (cd.toList.drop 4).length
        · have htake96 : (((cd.toList.drop 4).drop 96).take 32).length = 32 := by
            rw [List.length_take, List.length_drop]
            omega
          rw [decodeScalarWordWithMode_uint256_ok (mode := DecodeMode.legacySolc05)
            (bytes := cd.toList.drop 4) (start := 96) htake96]
          have htake128n :
              ¬ (((cd.toList.drop 4).drop 128).take 32).length = 32 := by
            rw [List.length_take, List.length_drop, List.length_drop, hlen]
            omega
          rw [decodeScalarWordWithMode_uint256_none_short
            (mode := DecodeMode.legacySolc05) (start := 128)
            (by simpa using htake128n)]
          simp only [Option.bind, bind]
        · have htake96n :
              ¬ (((cd.toList.drop 4).drop 96).take 32).length = 32 := by
            rw [List.length_take, List.length_drop]
            omega
          rw [decodeScalarWordWithMode_uint256_none_short
            (mode := DecodeMode.legacySolc05) (start := 96)
            (by simpa using htake96n)]
          simp only [Option.bind, bind]
      · have htake64n :
            ¬ (((cd.toList.drop 4).drop 64).take 32).length = 32 := by
          rw [List.length_take, List.length_drop]
          omega
        rw [decodeScalarWordWithMode_uint256_none_short
          (mode := DecodeMode.legacySolc05) (start := 64)
          (by simpa using htake64n)]
        simp only [Option.bind, bind]
    · have htake32n :
          ¬ (((cd.toList.drop 4).drop 32).take 32).length = 32 := by
        rw [List.length_take, List.length_drop]
        omega
      rw [decodeScalarWord_legacyAddress_none_short (start := 32)
        (by simpa using htake32n)]
      simp only [Option.bind, bind]
  · have htake0n : ¬ ((cd.toList.drop 4).take 32).length = 32 := by
      rw [List.length_take]
      omega
    simp only [decodeScalarWordsWithMode?]
    rw [decodeScalarWord_legacyAddress_none_short (start := 0)
      (by simpa using htake0n)]
    simp only [Option.bind, bind]

theorem decodeABIValues_bytes32_address_address_legacy_ok {bytes : List UInt8}
    (hlen0 : (bytes.take 32).length = 32)
    (hlen32 : ((bytes.drop 32).take 32).length = 32)
    (hlen64 : ((bytes.drop 64).take 32).length = 32) :
    decodeABIValues? [abiBytes32, abiAddress, abiAddress] bytes 0 0 96 96
        DecodeMode.legacySolc05 =
      some ([.fixedBytes abiBytes32Width (bytes.take 32),
        .address (AccountAddress.ofNat
          (ABI.bytesToWord ((bytes.drop 32).take 32)).toNat),
        .address (AccountAddress.ofNat
          (ABI.bytesToWord ((bytes.drop 64).take 32)).toNat)], 96) := by
  simp [decodeABIValues?, abiBytes32, abiBytes32Width, abiAddress, isDynamicABIType,
    staticABIEncodedSize?, decodeABIValue?, readBytes?, hlen0]
  simp [readWord?, readBytes?, decodeABIWord?, UInt256.toNat, hlen32, hlen64]

theorem decodeABIValues_bytes32_address_address_legacy_none_short {bytes : List UInt8}
    (hshort : bytes.length < 96) :
    decodeABIValues? [abiBytes32, abiAddress, abiAddress] bytes 0 0 96 96
        DecodeMode.legacySolc05 = none := by
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
    simp [decodeABIValue?, readBytes?, htake0]
    by_cases h64 : bytes.length < 64
    · have htake32n : ¬ ((bytes.drop 32).take 32).length = 32 := by
        rw [List.length_take, List.length_drop]
        omega
      have hnot : ¬ 32 ≤ bytes.length - 32 := by
        rw [List.length_take, List.length_drop] at htake32n
        omega
      simp [readWord?, readBytes?, hnot]
    · have htake32 : ((bytes.drop 32).take 32).length = 32 := by
        rw [List.length_take, List.length_drop]
        omega
      simp [readWord?, readBytes?, decodeABIWord?, UInt256.toNat, htake32]
      have htake64n : ¬ ((bytes.drop 64).take 32).length = 32 := by
        rw [List.length_take, List.length_drop]
        omega
      have hnot : ¬ 32 ≤ bytes.length - 64 := by
        rw [List.length_take, List.length_drop] at htake64n
        omega
      simp [readWord?, readBytes?, hnot]

theorem decodeCalldataWithMode_legacyBytes32_address_address_ok {cd : ByteArray}
    {x y z : Solm.Ident} (hsz100 : 100 ≤ cd.size) :
    decodeCalldataWithMode DecodeMode.legacySolc05 [x, y, z]
      [abiBytes32, abiAddress, abiAddress] cd =
        some ((((∅ : Solm.Store).insert x
          (.fixedBytes abiBytes32Width ((cd.toList.drop 4).take 32))).insert y
          (.address (AccountAddress.ofNat (calldataWord cd 36).toNat))).insert z
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
  have hword36 : ABI.bytesToWord ((cd.toList.drop 36).take 32) = calldataWord cd 36 :=
    decode_word_at_eq cd 36 (by omega) (by norm_num)
  have hword68 : ABI.bytesToWord ((cd.toList.drop 68).take 32) = calldataWord cd 68 :=
    decode_word_at_eq cd 68 (by omega) (by norm_num)
  unfold decodeCalldataWithMode decodeCalldata
  rw [if_neg (by rw [htlen]; omega : ¬ cd.toList.length < 4)]
  rw [if_neg (by simp [abiBytes32, abiAddress, isDynamicABIType])]
  simp only [decodeCalldata.decodeArgs]
  rw [show abiTupleHeadSize? [abiBytes32, abiAddress, abiAddress] = some 96 by
    simp [abiTupleHeadSize?, isDynamicABIType, staticABIEncodedSize?,
      abiBytes32, abiBytes32Width, abiUInt256, abiAddress, abiInt256, abiBytes]]
  simp only [bind, Option.bind]
  rw [decodeABIValues_bytes32_address_address_legacy_ok (bytes := cd.toList.drop 4)
    (by simpa using htake4)
    (by simpa [List.drop_drop, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using htake36)
    (by simpa [List.drop_drop, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using htake68)]
  rw [if_neg (by rw [List.length_drop, htlen]; omega :
    ¬ (cd.toList.drop 4).length < 96)]
  simp [decodeCalldata.insertValues]
  rw [hword36, hword68]

theorem decodeCalldataWithMode_legacyBytes32_address_address_none_short
    {cd : ByteArray} {x y z : Solm.Ident} (hsz4 : 4 ≤ cd.size)
    (hshort : cd.size < 100) :
    decodeCalldataWithMode DecodeMode.legacySolc05 [x, y, z]
      [abiBytes32, abiAddress, abiAddress] cd = none := by
  have htlen : cd.toList.length = cd.size := by
    rw [byteArray_toList_eq, Array.length_toList]
    rfl
  unfold decodeCalldataWithMode decodeCalldata
  rw [if_neg (by rw [htlen]; omega : ¬ cd.toList.length < 4)]
  rw [if_neg (by simp [abiBytes32, abiAddress, isDynamicABIType])]
  simp only [decodeCalldata.decodeArgs]
  rw [show abiTupleHeadSize? [abiBytes32, abiAddress, abiAddress] = some 96 by
    simp [abiTupleHeadSize?, isDynamicABIType, staticABIEncodedSize?,
      abiBytes32, abiBytes32Width, abiUInt256, abiAddress, abiInt256, abiBytes]]
  simp only [bind, Option.bind]
  by_cases hbytes : (cd.toList.drop 4).length < 96
  · rw [if_pos hbytes]
  · rw [if_neg hbytes]
    rw [decodeABIValues_bytes32_address_address_legacy_none_short
      (bytes := cd.toList.drop 4) (by
        rw [List.length_drop, htlen]
        omega)]

theorem decodeABIValues_bytes32_ok {bytes : List UInt8} {mode : DecodeMode}
    (hlen0 : (bytes.take 32).length = 32) :
    decodeABIValues? [abiBytes32] bytes 0 0 32 32 mode =
      some ([.fixedBytes abiBytes32Width (bytes.take 32)], 32) := by
  have htake : (bytes.take 32).take 32 = bytes.take 32 := by
    simp
  cases mode <;>
    simp [decodeABIValues?, abiBytes32, abiBytes32Width, isDynamicABIType,
      staticABIEncodedSize?, decodeABIValue?, readBytes?, zeroPadding?, hlen0, htake]

theorem decodeABIValues_bytes32_none_short {bytes : List UInt8} {mode : DecodeMode}
    (hshort : bytes.length < 32) :
    decodeABIValues? [abiBytes32] bytes 0 0 32 32 mode = none := by
  have hnot : ¬ 32 ≤ bytes.length := by omega
  cases mode <;>
    simp [decodeABIValues?, abiBytes32, abiBytes32Width, isDynamicABIType,
      staticABIEncodedSize?, decodeABIValue?, readBytes?, zeroPadding?, hnot]

theorem decodeReturnValue_bytes32_ok {returndata : ByteArray}
    (hlo : 32 ≤ returndata.size) :
    ABI.decodeReturnValueWithMode? DecodeMode.legacySolc05 abiBytes32 returndata =
      some (.fixedBytes abiBytes32Width
        (EVM.Word.toBytesBE (uInt256OfByteArray (returndata.extract 0 32)))) := by
  have hlen : returndata.toList.length = returndata.size := by
    rw [byteArray_toList_eq, Array.length_toList]
    rfl
  have htake0 : (returndata.toList.take 32).length = 32 := by
    rw [List.length_take, hlen]
    omega
  have hwordList := bytesToWord_take32_eq_extract0_32 (returndata := returndata)
  have hword : ABI.bytesToWord (returndata.toList.take 32) =
      uInt256OfByteArray (returndata.extract 0 32) := by
    rw [hwordList, uInt256OfByteArray_eq]
  have hbytes :
      EVM.Word.toBytesBE (uInt256OfByteArray (returndata.extract 0 32)) =
        returndata.toList.take 32 := by
    rw [← hword]
    exact toBytesBE_bytesToWord_of_length htake0
  rw [hbytes]
  unfold ABI.decodeReturnValueWithMode? ABI.decodeReturnValuesWithMode?
  rw [show ABI.abiTupleHeadSize? [abiBytes32] = some 32 by
    simp [abiTupleHeadSize?, isDynamicABIType, staticABIEncodedSize?,
      abiBytes32, abiBytes32Width, abiUInt256, abiAddress, abiInt256, abiBytes]]
  simp only [bind, Option.bind]
  rw [decodeABIValues_bytes32_ok
    (bytes := returndata.toList) (mode := DecodeMode.legacySolc05) htake0]

theorem decodeReturnValue_bytes32_none_short {returndata : ByteArray}
    (hshort : returndata.size < 32) :
    ABI.decodeReturnValueWithMode? DecodeMode.legacySolc05 abiBytes32 returndata = none := by
  have hlen : returndata.toList.length = returndata.size := by
    rw [byteArray_toList_eq, Array.length_toList]
    rfl
  unfold ABI.decodeReturnValueWithMode? ABI.decodeReturnValuesWithMode?
  rw [show ABI.abiTupleHeadSize? [abiBytes32] = some 32 by
    simp [abiTupleHeadSize?, isDynamicABIType, staticABIEncodedSize?,
      abiBytes32, abiBytes32Width, abiUInt256, abiAddress, abiInt256, abiBytes]]
  simp only [bind, Option.bind]
  rw [decodeABIValues_bytes32_none_short
    (bytes := returndata.toList) (mode := DecodeMode.legacySolc05) (by rw [hlen]; omega)]

theorem decodeScalarWords_address_address_address_int256_int256_legacy_ok
    {bytes : List UInt8}
    (hlen32 : ((bytes.drop 32).take 32).length = 32)
    (hlen64 : ((bytes.drop 64).take 32).length = 32)
    (hlen96 : ((bytes.drop 96).take 32).length = 32)
    (hlen128 : ((bytes.drop 128).take 32).length = 32)
    (hlen160 : ((bytes.drop 160).take 32).length = 32) :
    decodeScalarWordsWithMode? DecodeMode.legacySolc05
      [abiAddress, abiAddress, abiAddress, abiInt256, abiInt256] bytes 32 =
      some
        [ .address (AccountAddress.ofNat
            (ABI.bytesToWord ((bytes.drop 32).take 32)).toNat),
          .address (AccountAddress.ofNat
            (ABI.bytesToWord ((bytes.drop 64).take 32)).toNat),
          .address (AccountAddress.ofNat
            (ABI.bytesToWord ((bytes.drop 96).take 32)).toNat),
          .int
            (if (ABI.bytesToWord ((bytes.drop 128).take 32)).toNat < EVM.twoPow 255 then
              Int.ofNat (ABI.bytesToWord ((bytes.drop 128).take 32)).toNat
            else
              Int.ofNat (ABI.bytesToWord ((bytes.drop 128).take 32)).toNat -
                Int.ofNat EVM.wordModulus),
          .int
            (if (ABI.bytesToWord ((bytes.drop 160).take 32)).toNat < EVM.twoPow 255 then
              Int.ofNat (ABI.bytesToWord ((bytes.drop 160).take 32)).toNat
            else
              Int.ofNat (ABI.bytesToWord ((bytes.drop 160).take 32)).toNat -
                Int.ofNat EVM.wordModulus) ] := by
  have haddr32 :
      decodeScalarWordWithMode? DecodeMode.legacySolc05 abiAddress bytes 32 =
        some (.address (AccountAddress.ofNat
          (ABI.bytesToWord ((bytes.drop 32).take 32)).toNat), 32 + 32) := by
    simpa [abiAddress] using
      decodeScalarWord_legacyAddress_ok (bytes := bytes) (start := 32) hlen32
  have haddr64 :
      decodeScalarWordWithMode? DecodeMode.legacySolc05 abiAddress bytes 64 =
        some (.address (AccountAddress.ofNat
          (ABI.bytesToWord ((bytes.drop 64).take 32)).toNat), 64 + 32) := by
    simpa [abiAddress] using
      decodeScalarWord_legacyAddress_ok (bytes := bytes) (start := 64) hlen64
  have haddr96 :
      decodeScalarWordWithMode? DecodeMode.legacySolc05 abiAddress bytes 96 =
        some (.address (AccountAddress.ofNat
          (ABI.bytesToWord ((bytes.drop 96).take 32)).toNat), 96 + 32) := by
    simpa [abiAddress] using
      decodeScalarWord_legacyAddress_ok (bytes := bytes) (start := 96) hlen96
  have hint128 :
      decodeScalarWordWithMode? DecodeMode.legacySolc05 abiInt256 bytes 128 =
        some
          (.int
            (if (ABI.bytesToWord ((bytes.drop 128).take 32)).toNat < EVM.twoPow 255 then
              Int.ofNat (ABI.bytesToWord ((bytes.drop 128).take 32)).toNat
            else
              Int.ofNat (ABI.bytesToWord ((bytes.drop 128).take 32)).toNat -
                Int.ofNat EVM.wordModulus),
            128 + 32) :=
    decodeScalarWordWithMode_legacyInt256_ok (bytes := bytes) (start := 128) hlen128
  have hint160 :
      decodeScalarWordWithMode? DecodeMode.legacySolc05 abiInt256 bytes 160 =
        some
          (.int
            (if (ABI.bytesToWord ((bytes.drop 160).take 32)).toNat < EVM.twoPow 255 then
              Int.ofNat (ABI.bytesToWord ((bytes.drop 160).take 32)).toNat
            else
              Int.ofNat (ABI.bytesToWord ((bytes.drop 160).take 32)).toNat -
                Int.ofNat EVM.wordModulus),
            160 + 32) :=
    decodeScalarWordWithMode_legacyInt256_ok (bytes := bytes) (start := 160) hlen160
  simp only [decodeScalarWordsWithMode?]
  norm_num
  rw [haddr32]
  simp only [Option.bind, bind]
  rw [haddr64]
  simp only [Option.bind, bind]
  rw [haddr96]
  simp only [Option.bind, bind]
  rw [hint128]
  simp only [Option.bind, bind]
  rw [hint160]
  rfl

set_option maxHeartbeats 0 in
theorem decodeABIValues_bytes32_address_address_address_int256_int256_legacy_ok
    {bytes : List UInt8}
    (hlen0 : (bytes.take 32).length = 32)
    (hlen32 : ((bytes.drop 32).take 32).length = 32)
    (hlen64 : ((bytes.drop 64).take 32).length = 32)
    (hlen96 : ((bytes.drop 96).take 32).length = 32)
    (hlen128 : ((bytes.drop 128).take 32).length = 32)
    (hlen160 : ((bytes.drop 160).take 32).length = 32) :
    decodeABIValues? [abiBytes32, abiAddress, abiAddress, abiAddress, abiInt256, abiInt256] bytes
      0 0 192 192 DecodeMode.legacySolc05 =
        some
          ([ .fixedBytes abiBytes32Width (bytes.take 32),
             .address (AccountAddress.ofNat
               (ABI.bytesToWord ((bytes.drop 32).take 32)).toNat),
           .address (AccountAddress.ofNat
             (ABI.bytesToWord ((bytes.drop 64).take 32)).toNat),
           .address (AccountAddress.ofNat
             (ABI.bytesToWord ((bytes.drop 96).take 32)).toNat),
           .int
             (if (ABI.bytesToWord ((bytes.drop 128).take 32)).toNat < EVM.twoPow 255 then
               Int.ofNat (ABI.bytesToWord ((bytes.drop 128).take 32)).toNat
             else
               Int.ofNat (ABI.bytesToWord ((bytes.drop 128).take 32)).toNat -
                 Int.ofNat EVM.wordModulus),
           .int
             (if (ABI.bytesToWord ((bytes.drop 160).take 32)).toNat < EVM.twoPow 255 then
               Int.ofNat (ABI.bytesToWord ((bytes.drop 160).take 32)).toNat
             else
                 Int.ofNat (ABI.bytesToWord ((bytes.drop 160).take 32)).toNat -
                   Int.ofNat EVM.wordModulus) ],
           192) := by
    have hbytes32 :
        decodeABIValue? (.elem (.bytes abiBytes32Width)) bytes 0 DecodeMode.legacySolc05 =
          some (.fixedBytes abiBytes32Width (bytes.take 32), 32) := by
      simp only [abiBytes32Width, decodeABIValue?, readBytes?, bind, Option.bind]
      rw [if_pos (by simpa using hlen0)]
      simp [zeroPadding?, readBytes?]
    have htail :
        decodeABIValues? [abiAddress, abiAddress, abiAddress, abiInt256,
          abiInt256] bytes 0 32 192 192
          DecodeMode.legacySolc05 =
          some
            ([ .address (AccountAddress.ofNat
                (ABI.bytesToWord ((bytes.drop 32).take 32)).toNat),
               .address (AccountAddress.ofNat
                (ABI.bytesToWord ((bytes.drop 64).take 32)).toNat),
               .address (AccountAddress.ofNat
                (ABI.bytesToWord ((bytes.drop 96).take 32)).toNat),
               .int
                (if (ABI.bytesToWord ((bytes.drop 128).take 32)).toNat < EVM.twoPow 255 then
                  Int.ofNat (ABI.bytesToWord ((bytes.drop 128).take 32)).toNat
                else
                  Int.ofNat (ABI.bytesToWord ((bytes.drop 128).take 32)).toNat -
                    Int.ofNat EVM.wordModulus),
               .int
                (if (ABI.bytesToWord ((bytes.drop 160).take 32)).toNat < EVM.twoPow 255 then
                  Int.ofNat (ABI.bytesToWord ((bytes.drop 160).take 32)).toNat
                else
                  Int.ofNat (ABI.bytesToWord ((bytes.drop 160).take 32)).toNat -
                    Int.ofNat EVM.wordModulus) ],
             192) := by
      rw [decodeABIValues_scalarWordsWithMode_eq
        (mode := DecodeMode.legacySolc05)
        (types := [abiAddress, abiAddress, abiAddress, abiInt256, abiInt256])
        (bytes := bytes) (cursor := 32) (total := 192)
        (by decide) (by norm_num)]
      rw [decodeScalarWords_address_address_address_int256_int256_legacy_ok
        (bytes := bytes) hlen32 hlen64 hlen96 hlen128 hlen160]
    rw [decodeABIValues?]
    simp only [abiBytes32, isDynamicABIType, staticABIEncodedSize?, Bool.false_eq_true, if_false,
      Nat.zero_add, Option.bind, bind]
    rw [hbytes32]
    simp only [Option.bind, bind]
    rw [if_pos (by norm_num)]
    rw [show max 192 32 = 192 by norm_num]
    rw [htail]

set_option maxHeartbeats 0 in
theorem decodeCalldata_legacyBytes32_address_address_address_int256_int256_ok
    {cd : ByteArray} {a b c d e f : Solm.Ident} (hsz196 : 196 ≤ cd.size) :
    decodeCalldataWithMode DecodeMode.legacySolc05 [a, b, c, d, e, f]
      [abiBytes32, abiAddress, abiAddress, abiAddress, abiInt256, abiInt256] cd =
      some (((((((∅ : Store).insert a
        (.fixedBytes abiBytes32Width ((cd.toList.drop 4).take 32))).insert b
        (.address (AccountAddress.ofNat (calldataWord cd 36).toNat))).insert c
        (.address (AccountAddress.ofNat (calldataWord cd 68).toNat))).insert d
        (.address (AccountAddress.ofNat (calldataWord cd 100).toNat))).insert e
        (.int
          (if (calldataWord cd 132).toNat < EVM.twoPow 255 then
            Int.ofNat (calldataWord cd 132).toNat
          else
            Int.ofNat (calldataWord cd 132).toNat - Int.ofNat EVM.wordModulus))).insert f
        (.int
          (if (calldataWord cd 164).toNat < EVM.twoPow 255 then
            Int.ofNat (calldataWord cd 164).toNat
          else
            Int.ofNat (calldataWord cd 164).toNat - Int.ofNat EVM.wordModulus))) := by
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
  have htake100 : ((cd.toList.drop 100).take 32).length = 32 := by
    rw [List.length_take, List.length_drop, htlen]
    omega
  have htake132 : ((cd.toList.drop 132).take 32).length = 32 := by
    rw [List.length_take, List.length_drop, htlen]
    omega
  have htake164 : ((cd.toList.drop 164).take 32).length = 32 := by
    rw [List.length_take, List.length_drop, htlen]
    omega
  have hword36 : ABI.bytesToWord ((cd.toList.drop 36).take 32) = calldataWord cd 36 :=
    decode_word_at_eq cd 36 (by omega) (by norm_num)
  have hword68 : ABI.bytesToWord ((cd.toList.drop 68).take 32) = calldataWord cd 68 :=
    decode_word_at_eq cd 68 (by omega) (by norm_num)
  have hword100 : ABI.bytesToWord ((cd.toList.drop 100).take 32) = calldataWord cd 100 :=
    decode_word_at_eq cd 100 (by omega) (by norm_num)
  have hword132 : ABI.bytesToWord ((cd.toList.drop 132).take 32) = calldataWord cd 132 :=
    decode_word_at_eq cd 132 (by omega) (by norm_num)
  have hword164 : ABI.bytesToWord ((cd.toList.drop 164).take 32) = calldataWord cd 164 :=
    decode_word_at_eq cd 164 (by omega) (by norm_num)
  unfold decodeCalldataWithMode decodeCalldata
  rw [if_neg (by rw [htlen]; omega : ¬ cd.toList.length < 4)]
  rw [if_neg (by simp [abiBytes32, abiAddress, abiInt256, isDynamicABIType])]
  simp only
  simp only [decodeCalldata.decodeArgs]
  rw [show abiTupleHeadSize? [abiBytes32, abiAddress, abiAddress, abiAddress, abiInt256,
    abiInt256] =
      some 192 by
    simp [abiTupleHeadSize?, isDynamicABIType, staticABIEncodedSize?,
      abiBytes32, abiBytes32Width, abiUInt256, abiAddress, abiInt256, abiBytes]]
  simp only [bind, Option.bind]
  rw [if_neg (by rw [List.length_drop, htlen]; omega :
    ¬ (cd.toList.drop 4).length < 192)]
  rw [decodeABIValues_bytes32_address_address_address_int256_int256_legacy_ok
    (bytes := cd.toList.drop 4)
    (by simpa using htake4)
    (by simpa [List.drop_drop, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc]
      using htake36)
    (by simpa [List.drop_drop, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc]
      using htake68)
    (by simpa [List.drop_drop, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc]
      using htake100)
    (by simpa [List.drop_drop, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc]
      using htake132)
    (by simpa [List.drop_drop, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc]
      using htake164)]
  rw [show ABI.bytesToWord (((cd.toList.drop 4).drop 32).take 32) =
      calldataWord cd 36 from by
    simpa [List.drop_drop, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using hword36]
  rw [show ABI.bytesToWord (((cd.toList.drop 4).drop 64).take 32) =
      calldataWord cd 68 from by
    simpa [List.drop_drop, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using hword68]
  rw [show ABI.bytesToWord (((cd.toList.drop 4).drop 96).take 32) =
      calldataWord cd 100 from by
    simpa [List.drop_drop, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using hword100]
  rw [show ABI.bytesToWord (((cd.toList.drop 4).drop 128).take 32) =
      calldataWord cd 132 from by
    simpa [List.drop_drop, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using hword132]
  rw [show ABI.bytesToWord (((cd.toList.drop 4).drop 160).take 32) =
      calldataWord cd 164 from by
    simpa [List.drop_drop, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using hword164]
  simp only [Option.bind, bind]
  change decodeCalldata.insertValues [a, b, c, d, e, f]
      [ .fixedBytes abiBytes32Width ((cd.toList.drop 4).take 32),
        .address (AccountAddress.ofNat (calldataWord cd 36).toNat),
        .address (AccountAddress.ofNat (calldataWord cd 68).toNat),
        .address (AccountAddress.ofNat (calldataWord cd 100).toNat),
        .int
          (if (calldataWord cd 132).toNat < EVM.twoPow 255 then
            Int.ofNat (calldataWord cd 132).toNat
          else
            Int.ofNat (calldataWord cd 132).toNat - Int.ofNat EVM.wordModulus),
        .int
          (if (calldataWord cd 164).toNat < EVM.twoPow 255 then
            Int.ofNat (calldataWord cd 164).toNat
          else
            Int.ofNat (calldataWord cd 164).toNat - Int.ofNat EVM.wordModulus) ] ∅ =
      some (((((((∅ : Store).insert a
        (.fixedBytes abiBytes32Width ((cd.toList.drop 4).take 32))).insert b
        (.address (AccountAddress.ofNat (calldataWord cd 36).toNat))).insert c
        (.address (AccountAddress.ofNat (calldataWord cd 68).toNat))).insert d
        (.address (AccountAddress.ofNat (calldataWord cd 100).toNat))).insert e
        (.int
          (if (calldataWord cd 132).toNat < EVM.twoPow 255 then
            Int.ofNat (calldataWord cd 132).toNat
          else
            Int.ofNat (calldataWord cd 132).toNat - Int.ofNat EVM.wordModulus))).insert f
        (.int
          (if (calldataWord cd 164).toNat < EVM.twoPow 255 then
            Int.ofNat (calldataWord cd 164).toNat
          else
            Int.ofNat (calldataWord cd 164).toNat - Int.ofNat EVM.wordModulus)))
  rfl

theorem decodeABIValues_bytes32_address_address_uint256_legacy_ok {bytes : List UInt8}
    (hlen0 : (bytes.take 32).length = 32)
    (hlen32 : ((bytes.drop 32).take 32).length = 32)
    (hlen64 : ((bytes.drop 64).take 32).length = 32)
    (hlen96 : ((bytes.drop 96).take 32).length = 32) :
    decodeABIValues? [abiBytes32, abiAddress, abiAddress,
      abiUInt256] bytes 0 0 128 128 DecodeMode.legacySolc05 =
      some
        ([ .fixedBytes abiBytes32Width (bytes.take 32),
           .address (AccountAddress.ofNat
             (ABI.bytesToWord ((bytes.drop 32).take 32)).toNat),
           .address (AccountAddress.ofNat
             (ABI.bytesToWord ((bytes.drop 64).take 32)).toNat),
           .int (Int.ofNat (ABI.bytesToWord ((bytes.drop 96).take 32)).toNat) ],
         128) := by
  have hge32 : 32 ≤ bytes.length - 32 := by
    rw [List.length_take, List.length_drop] at hlen32
    omega
  have hge64 : 32 ≤ bytes.length - 64 := by
    rw [List.length_take, List.length_drop] at hlen64
    omega
  have hge96 : 32 ≤ bytes.length - 96 := by
    rw [List.length_take, List.length_drop] at hlen96
    omega
  simp [decodeABIValues?, decodeABIValue?, readBytes?, readWord?, decodeABIWord?,
    abiBytes32, abiAddress, abiUInt256, abiBytes32Width, abiUInt256Int, isDynamicABIType,
    staticABIEncodedSize?, hlen0, hge32, hge64, hge96, UInt256.toNat]
  exact normalizeInt_uint256_word (ABI.bytesToWord ((bytes.drop 96).take 32))

set_option maxHeartbeats 0 in
theorem decodeCalldata_legacyBytes32_address_address_uint256_ok {cd : ByteArray}
    {w x y z : Solm.Ident} (hsz132 : 132 ≤ cd.size) :
    decodeCalldataWithMode DecodeMode.legacySolc05 [w, x, y, z]
      [abiBytes32, abiAddress, abiAddress, abiUInt256] cd =
      some (((((∅ : Store).insert w
        (.fixedBytes abiBytes32Width ((cd.toList.drop 4).take 32))).insert x
        (.address (AccountAddress.ofNat (calldataWord cd 36).toNat))).insert y
        (.address (AccountAddress.ofNat (calldataWord cd 68).toNat))).insert z
        (.int (Int.ofNat (calldataWord cd 100).toNat))) := by
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
  have htake100 : ((cd.toList.drop 100).take 32).length = 32 := by
    rw [List.length_take, List.length_drop, htlen]
    omega
  have hword36 : ABI.bytesToWord ((cd.toList.drop 36).take 32) = calldataWord cd 36 :=
    decode_word_at_eq cd 36 (by omega) (by norm_num)
  have hword68 : ABI.bytesToWord ((cd.toList.drop 68).take 32) = calldataWord cd 68 :=
    decode_word_at_eq cd 68 (by omega) (by norm_num)
  have hword100 : ABI.bytesToWord ((cd.toList.drop 100).take 32) = calldataWord cd 100 :=
    decode_word_at_eq cd 100 (by omega) (by norm_num)
  unfold decodeCalldataWithMode decodeCalldata
  rw [if_neg (by rw [htlen]; omega : ¬ cd.toList.length < 4)]
  rw [if_neg (by simp [abiBytes32, abiAddress, abiUInt256, isDynamicABIType])]
  simp only
  simp only [decodeCalldata.decodeArgs]
  rw [show abiTupleHeadSize? [abiBytes32, abiAddress, abiAddress, abiUInt256] = some 128 by
    simp [abiTupleHeadSize?, isDynamicABIType, staticABIEncodedSize?,
      abiBytes32, abiBytes32Width, abiUInt256, abiAddress, abiInt256, abiBytes]]
  simp only [bind, Option.bind]
  rw [if_neg (by rw [List.length_drop, htlen]; omega :
    ¬ (cd.toList.drop 4).length < 128)]
  rw [decodeABIValues_bytes32_address_address_uint256_legacy_ok
    (bytes := cd.toList.drop 4)
    (by simpa using htake4)
    (by simpa [List.drop_drop, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc]
      using htake36)
    (by simpa [List.drop_drop, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc]
      using htake68)
    (by simpa [List.drop_drop, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc]
      using htake100)]
  rw [show ABI.bytesToWord (((cd.toList.drop 4).drop 32).take 32) =
      calldataWord cd 36 from by
    simpa [List.drop_drop, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using hword36]
  rw [show ABI.bytesToWord (((cd.toList.drop 4).drop 64).take 32) =
      calldataWord cd 68 from by
    simpa [List.drop_drop, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using hword68]
  rw [show ABI.bytesToWord (((cd.toList.drop 4).drop 96).take 32) =
      calldataWord cd 100 from by
    simpa [List.drop_drop, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using hword100]
  simp [decodeCalldata.insertValues]

set_option maxHeartbeats 0 in
theorem decodeABIValues_bytes32_address_address_int256_int256_legacy_ok {bytes : List UInt8}
    (hlen0 : (bytes.take 32).length = 32)
    (hlen32 : ((bytes.drop 32).take 32).length = 32)
    (hlen64 : ((bytes.drop 64).take 32).length = 32)
    (hlen96 : ((bytes.drop 96).take 32).length = 32)
    (hlen128 : ((bytes.drop 128).take 32).length = 32) :
    decodeABIValues? [abiBytes32, abiAddress, abiAddress, abiInt256, abiInt256] bytes 0 0 160 160
      DecodeMode.legacySolc05 =
      some
        ([ .fixedBytes abiBytes32Width (bytes.take 32),
           .address (AccountAddress.ofNat
             (ABI.bytesToWord ((bytes.drop 32).take 32)).toNat),
           .address (AccountAddress.ofNat
             (ABI.bytesToWord ((bytes.drop 64).take 32)).toNat),
           .int
             (if (ABI.bytesToWord ((bytes.drop 96).take 32)).toNat < EVM.twoPow 255 then
               Int.ofNat (ABI.bytesToWord ((bytes.drop 96).take 32)).toNat
             else
               Int.ofNat (ABI.bytesToWord ((bytes.drop 96).take 32)).toNat -
                 Int.ofNat EVM.wordModulus),
           .int
             (if (ABI.bytesToWord ((bytes.drop 128).take 32)).toNat < EVM.twoPow 255 then
               Int.ofNat (ABI.bytesToWord ((bytes.drop 128).take 32)).toNat
             else
               Int.ofNat (ABI.bytesToWord ((bytes.drop 128).take 32)).toNat -
                 Int.ofNat EVM.wordModulus) ],
         160) := by
  have hbytes32 :
      decodeABIValue? (.elem (.bytes abiBytes32Width)) bytes 0 DecodeMode.legacySolc05 =
        some (.fixedBytes abiBytes32Width (bytes.take 32), 32) := by
    simp only [abiBytes32Width, decodeABIValue?, readBytes?, bind, Option.bind]
    rw [if_pos (by simpa using hlen0)]
    simp [zeroPadding?, readBytes?]
  have haddr32 :
      decodeScalarWordWithMode? DecodeMode.legacySolc05 abiAddress bytes 32 =
        some (.address (AccountAddress.ofNat
          (ABI.bytesToWord ((bytes.drop 32).take 32)).toNat), 32 + 32) := by
    simpa [abiAddress] using
      decodeScalarWord_legacyAddress_ok (bytes := bytes) (start := 32) hlen32
  have haddr64 :
      decodeScalarWordWithMode? DecodeMode.legacySolc05 abiAddress bytes 64 =
        some (.address (AccountAddress.ofNat
          (ABI.bytesToWord ((bytes.drop 64).take 32)).toNat), 64 + 32) := by
    simpa [abiAddress] using
      decodeScalarWord_legacyAddress_ok (bytes := bytes) (start := 64) hlen64
  have hint96 := decodeScalarWordWithMode_legacyInt256_ok
    (bytes := bytes) (start := 96) hlen96
  have hint128 := decodeScalarWordWithMode_legacyInt256_ok
    (bytes := bytes) (start := 128) hlen128
  have htail :
      decodeScalarWordsWithMode? DecodeMode.legacySolc05
        [abiAddress, abiAddress, abiInt256, abiInt256] bytes 32 =
        some
          [ .address (AccountAddress.ofNat
              (ABI.bytesToWord ((bytes.drop 32).take 32)).toNat),
            .address (AccountAddress.ofNat
              (ABI.bytesToWord ((bytes.drop 64).take 32)).toNat),
            .int
              (if (ABI.bytesToWord ((bytes.drop 96).take 32)).toNat < EVM.twoPow 255 then
                Int.ofNat (ABI.bytesToWord ((bytes.drop 96).take 32)).toNat
              else
                Int.ofNat (ABI.bytesToWord ((bytes.drop 96).take 32)).toNat -
                  Int.ofNat EVM.wordModulus),
            .int
              (if (ABI.bytesToWord ((bytes.drop 128).take 32)).toNat < EVM.twoPow 255 then
                Int.ofNat (ABI.bytesToWord ((bytes.drop 128).take 32)).toNat
              else
                Int.ofNat (ABI.bytesToWord ((bytes.drop 128).take 32)).toNat -
                  Int.ofNat EVM.wordModulus) ] := by
    simp only [decodeScalarWordsWithMode?]
    norm_num
    rw [haddr32]
    simp only [Option.bind, bind]
    rw [haddr64]
    simp only [Option.bind, bind]
    rw [hint96]
    simp only [Option.bind, bind]
    rw [hint128]
    rfl
  rw [decodeABIValues?]
  simp only [abiBytes32, isDynamicABIType, staticABIEncodedSize?, Bool.false_eq_true, if_false,
    Nat.zero_add, Option.bind, bind]
  rw [hbytes32]
  simp only [Option.bind, bind]
  rw [if_pos (by norm_num)]
  rw [show max 160 32 = 160 by norm_num]
  rw [decodeABIValues_scalarWordsWithMode_eq
    (mode := DecodeMode.legacySolc05)
    (types := [abiAddress, abiAddress, abiInt256, abiInt256])
    (bytes := bytes) (cursor := 32) (total := 160)
    (by decide) (by norm_num)]
  rw [htail]

set_option maxHeartbeats 0 in
theorem decodeCalldata_legacyBytes32_address_address_int256_int256_ok {cd : ByteArray}
    {v w x y z : Solm.Ident} (hsz164 : 164 ≤ cd.size) :
    decodeCalldataWithMode DecodeMode.legacySolc05 [v, w, x, y, z]
      [abiBytes32, abiAddress, abiAddress, abiInt256, abiInt256] cd =
      some ((((((∅ : Store).insert v
        (.fixedBytes abiBytes32Width ((cd.toList.drop 4).take 32))).insert w
        (.address (AccountAddress.ofNat (calldataWord cd 36).toNat))).insert x
        (.address (AccountAddress.ofNat (calldataWord cd 68).toNat))).insert y
        (.int
          (if (calldataWord cd 100).toNat < EVM.twoPow 255 then
            Int.ofNat (calldataWord cd 100).toNat
          else
            Int.ofNat (calldataWord cd 100).toNat - Int.ofNat EVM.wordModulus))).insert z
        (.int
          (if (calldataWord cd 132).toNat < EVM.twoPow 255 then
            Int.ofNat (calldataWord cd 132).toNat
          else
            Int.ofNat (calldataWord cd 132).toNat - Int.ofNat EVM.wordModulus))) := by
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
  have htake100 : ((cd.toList.drop 100).take 32).length = 32 := by
    rw [List.length_take, List.length_drop, htlen]
    omega
  have htake132 : ((cd.toList.drop 132).take 32).length = 32 := by
    rw [List.length_take, List.length_drop, htlen]
    omega
  have hword36 : ABI.bytesToWord ((cd.toList.drop 36).take 32) = calldataWord cd 36 :=
    decode_word_at_eq cd 36 (by omega) (by norm_num)
  have hword68 : ABI.bytesToWord ((cd.toList.drop 68).take 32) = calldataWord cd 68 :=
    decode_word_at_eq cd 68 (by omega) (by norm_num)
  have hword100 : ABI.bytesToWord ((cd.toList.drop 100).take 32) = calldataWord cd 100 :=
    decode_word_at_eq cd 100 (by omega) (by norm_num)
  have hword132 : ABI.bytesToWord ((cd.toList.drop 132).take 32) = calldataWord cd 132 :=
    decode_word_at_eq cd 132 (by omega) (by norm_num)
  unfold decodeCalldataWithMode decodeCalldata
  rw [if_neg (by rw [htlen]; omega : ¬ cd.toList.length < 4)]
  rw [if_neg (by simp [abiBytes32, abiAddress, abiInt256, isDynamicABIType])]
  simp only
  simp only [decodeCalldata.decodeArgs]
  rw [show abiTupleHeadSize? [abiBytes32, abiAddress, abiAddress, abiInt256,
    abiInt256] = some 160 by
    simp [abiTupleHeadSize?, isDynamicABIType, staticABIEncodedSize?,
      abiBytes32, abiBytes32Width, abiUInt256, abiAddress, abiInt256, abiBytes]]
  simp only [bind, Option.bind]
  rw [if_neg (by rw [List.length_drop, htlen]; omega :
    ¬ (cd.toList.drop 4).length < 160)]
  rw [decodeABIValues_bytes32_address_address_int256_int256_legacy_ok
    (bytes := cd.toList.drop 4)
    (by simpa using htake4)
    (by simpa [List.drop_drop, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc]
      using htake36)
    (by simpa [List.drop_drop, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc]
      using htake68)
    (by simpa [List.drop_drop, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc]
      using htake100)
    (by simpa [List.drop_drop, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc]
      using htake132)]
  rw [show ABI.bytesToWord (((cd.toList.drop 4).drop 32).take 32) =
      calldataWord cd 36 from by
    simpa [List.drop_drop, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using hword36]
  rw [show ABI.bytesToWord (((cd.toList.drop 4).drop 64).take 32) =
      calldataWord cd 68 from by
    simpa [List.drop_drop, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using hword68]
  rw [show ABI.bytesToWord (((cd.toList.drop 4).drop 96).take 32) =
      calldataWord cd 100 from by
    simpa [List.drop_drop, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using hword100]
  rw [show ABI.bytesToWord (((cd.toList.drop 4).drop 128).take 32) =
      calldataWord cd 132 from by
    simpa [List.drop_drop, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using hword132]
  simp [decodeCalldata.insertValues]

set_option maxHeartbeats 0 in
theorem decodeABIValues_bytes32_address_int256_legacy_ok {bytes : List UInt8}
    (hlen0 : (bytes.take 32).length = 32)
    (hlen32 : ((bytes.drop 32).take 32).length = 32)
    (hlen64 : ((bytes.drop 64).take 32).length = 32) :
    decodeABIValues? [abiBytes32, abiAddress, abiInt256] bytes 0 0 96 96 DecodeMode.legacySolc05 =
      some
        ([ .fixedBytes abiBytes32Width (bytes.take 32),
           .address (AccountAddress.ofNat
             (ABI.bytesToWord ((bytes.drop 32).take 32)).toNat),
           .int
             (if (ABI.bytesToWord ((bytes.drop 64).take 32)).toNat < EVM.twoPow 255 then
               Int.ofNat (ABI.bytesToWord ((bytes.drop 64).take 32)).toNat
             else
               Int.ofNat (ABI.bytesToWord ((bytes.drop 64).take 32)).toNat -
                 Int.ofNat EVM.wordModulus) ],
         96) := by
  have hge32 : 32 ≤ bytes.length - 32 := by
    rw [List.length_take, List.length_drop] at hlen32
    omega
  have hge64 : 32 ≤ bytes.length - 64 := by
    rw [List.length_take, List.length_drop] at hlen64
    omega
  simp [decodeABIValues?, decodeABIValue?, readBytes?, readWord?, decodeABIWord?,
    abiBytes32, abiAddress, abiInt256, abiBytes32Width, abiInt256Int, isDynamicABIType,
    staticABIEncodedSize?, hlen0, hge32, hge64, UInt256.toNat]
  exact normalizeInt_sint256_word (ABI.bytesToWord ((bytes.drop 64).take 32))

theorem decodeCalldata_legacyBytes32_address_int256_ok {cd : ByteArray}
    {x y z : Solm.Ident} (hsz100 : 100 ≤ cd.size) :
    decodeCalldataWithMode DecodeMode.legacySolc05 [x, y, z] [abiBytes32, abiAddress,
      abiInt256] cd =
      some ((((∅ : Store).insert x
        (.fixedBytes abiBytes32Width ((cd.toList.drop 4).take 32))).insert y
        (.address (AccountAddress.ofNat (calldataWord cd 36).toNat))).insert z
        (.int
          (if (calldataWord cd 68).toNat < EVM.twoPow 255 then
            Int.ofNat (calldataWord cd 68).toNat
          else
            Int.ofNat (calldataWord cd 68).toNat - Int.ofNat EVM.wordModulus))) := by
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
  have hword36 : ABI.bytesToWord ((cd.toList.drop 36).take 32) = calldataWord cd 36 :=
    decode_word_at_eq cd 36 (by omega) (by norm_num)
  have hword68 : ABI.bytesToWord ((cd.toList.drop 68).take 32) = calldataWord cd 68 :=
    decode_word_at_eq cd 68 (by omega) (by norm_num)
  unfold decodeCalldataWithMode decodeCalldata
  rw [if_neg (by rw [htlen]; omega : ¬ cd.toList.length < 4)]
  rw [if_neg (by simp [abiBytes32, abiAddress, abiInt256, isDynamicABIType])]
  simp only
  simp only [decodeCalldata.decodeArgs]
  rw [show abiTupleHeadSize? [abiBytes32, abiAddress, abiInt256] = some 96 by
    simp [abiTupleHeadSize?, isDynamicABIType, staticABIEncodedSize?,
      abiBytes32, abiBytes32Width, abiUInt256, abiAddress, abiInt256, abiBytes]]
  simp only [bind, Option.bind]
  rw [if_neg (by rw [List.length_drop, htlen]; omega :
    ¬ (cd.toList.drop 4).length < 96)]
  rw [decodeABIValues_bytes32_address_int256_legacy_ok
    (bytes := cd.toList.drop 4)
    (by simpa using htake4)
    (by simpa [List.drop_drop, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc]
      using htake36)
    (by simpa [List.drop_drop, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc]
      using htake68)]
  rw [show ABI.bytesToWord (((cd.toList.drop 4).drop 32).take 32) =
      calldataWord cd 36 from by
    simpa [List.drop_drop, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using hword36]
  rw [show ABI.bytesToWord (((cd.toList.drop 4).drop 64).take 32) =
      calldataWord cd 68 from by
    simpa [List.drop_drop, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using hword68]
  simp [decodeCalldata.insertValues]

theorem decodeABIValue_legacyAddress_ok {bytes : List UInt8} {start : Nat}
    (hlen : ((bytes.drop start).take 32).length = 32) :
    decodeABIValue? (.elem .address) bytes start DecodeMode.legacySolc05 =
      some (.address (AccountAddress.ofNat
        (ABI.bytesToWord ((bytes.drop start).take 32)).toNat), start + 32) := by
  rw [decodeABIValue_scalarWordWithMode_eq (mode := DecodeMode.legacySolc05)
    (ty := .elem .address) (bytes := bytes) (start := start) (by decide)]
  simpa [abiAddress] using
    (decodeScalarWord_legacyAddress_ok (bytes := bytes) (start := start) hlen)

theorem decodeABIValue_legacyUint256_ok {bytes : List UInt8} {start : Nat}
    (hlen : ((bytes.drop start).take 32).length = 32) :
    decodeABIValue? abiUInt256 bytes start DecodeMode.legacySolc05 =
      some (.int (Int.ofNat (ABI.bytesToWord ((bytes.drop start).take 32)).toNat),
        start + 32) := by
  rw [decodeABIValue_scalarWordWithMode_eq (mode := DecodeMode.legacySolc05)
    (ty := abiUInt256) (bytes := bytes) (start := start) (by decide)]
  simpa [abiUInt256, abiUInt256Int, abiUInt256] using
    (decodeScalarWordWithMode_uint256_ok (mode := DecodeMode.legacySolc05)
      (bytes := bytes) (start := start) hlen)

theorem decodeABIValue_legacyUint8_ok {bytes : List UInt8} {start : Nat}
    (hlen : ((bytes.drop start).take 32).length = 32) :
    decodeABIValue? abiUInt8 bytes start DecodeMode.legacySolc05 =
      some (.int (Int.ofNat
          ((ABI.bytesToWord ((bytes.drop start).take 32)).toNat % EVM.twoPow 8)),
        start + 32) := by
  simp only [abiUInt8, abiUInt8Int, decodeABIValue?, readWord?, readBytes?, decodeABIWord?, bind,
    Option.bind]
  rw [if_pos hlen]
  rfl

theorem decodeABIValue_legacyBytes32_ok {bytes : List UInt8} {start : Nat}
    (hlen : ((bytes.drop start).take 32).length = 32) :
    decodeABIValue? abiBytes32 bytes start DecodeMode.legacySolc05 =
      some (.fixedBytes abiBytes32Width ((bytes.drop start).take 32), start + 32) := by
  simp only [abiBytes32, abiBytes32Width, decodeABIValue?, readBytes?, zeroPadding?, bind,
    Option.bind]
  rw [if_pos hlen]
  simp

abbrev legacyThreeUintAddressBytesDecodedBytes (cd : ByteArray) : ByteArray :=
  ByteArray.mk
    ((((cd.toList.drop 4).drop ((calldataWord cd 132).toNat + 32)).take
      (calldataWord cd (4 + (calldataWord cd 132).toNat)).toNat).toArray)

abbrev legacyThreeUintAddressBytesDecodedStore (cd : ByteArray) (a b c d e : Solm.Ident) : Store :=
  (((((∅ : Store).insert a (.int (Int.ofNat (calldataWord cd 4).toNat))).insert b
    (.int (Int.ofNat (calldataWord cd 36).toNat))).insert c
    (.int (Int.ofNat (calldataWord cd 68).toNat))).insert d
    (.address (AccountAddress.ofNat (calldataWord cd 100).toNat))).insert e
    (.bytes (legacyThreeUintAddressBytesDecodedBytes cd))

theorem readNat_drop4_at_eq_calldataWord {cd : ByteArray} (off : Nat)
    (hlenWord : 4 + off + 32 ≤ cd.size) :
    readNat? (cd.toList.drop 4) off = some (calldataWord cd (4 + off)).toNat := by
  unfold readNat? readWord?
  have hread : readBytes? (cd.toList.drop 4) off 32 =
      some (((cd.toList.drop 4).drop off).take 32) := by
    unfold readBytes?
    have htlen : cd.toList.length = cd.size := by
      rw [byteArray_toList_eq, Array.length_toList]
      rfl
    have hlen : (((cd.toList.drop 4).drop off).take 32).length = 32 := by
      rw [List.length_take, List.length_drop, List.length_drop, htlen]
      omega
    rw [if_pos hlen]
  rw [hread]
  have hword :
      bytesToWord (((cd.toList.drop 4).drop off).take 32) =
        calldataWord cd (4 + off) := by
    have h := decode_word_at_eq_any cd (4 + off) hlenWord
    simpa [List.drop_drop, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using h
  simp only [Option.bind, bind, hword]
  rfl

theorem readBytes_drop4_payload {cd : ByteArray} {off len : Nat}
    (hpayload : (((cd.toList.drop 4).drop off).take len).length = len) :
    readBytes? (cd.toList.drop 4) off len =
      some (((cd.toList.drop 4).drop off).take len) := by
  unfold readBytes?
  rw [if_pos hpayload]

theorem decodeABIValue_legacyBytes_ok {bytes : List UInt8} {start len : Nat}
    (hreadLen : readNat? bytes start = some len)
    (hlenMax : ¬ solcMaxLen DecodeMode.legacySolc05 < len)
    (hpayload : ((bytes.drop (start + 32)).take len).length = len) :
    decodeABIValue? ABIType.bytes bytes start DecodeMode.legacySolc05 =
      some (.bytes (ByteArray.mk (((bytes.drop (start + 32)).take len).toArray)),
        start + 32 + paddedSize len) := by
  unfold decodeABIValue?
  rw [hreadLen]
  simp only [Option.bind, bind]
  rw [if_neg hlenMax]
  have hreadPayload :
      readBytes? bytes (start + 32) len = some ((bytes.drop (start + 32)).take len) := by
    unfold readBytes?
    rw [if_pos hpayload]
  rw [hreadPayload]

set_option maxHeartbeats 1000000 in
theorem decodeCalldata_legacyUint256_uint256_uint256_address_bytes_ok {cd : ByteArray}
    {a b c d e : Solm.Ident}
    (hsmall : cd.size < 2 ^ 255)
    (hsz164 : 164 ≤ cd.size)
    (hoffMax : ¬ solcMaxLen DecodeMode.legacySolc05 < (calldataWord cd 132).toNat)
    (hlenWord : 4 + (calldataWord cd 132).toNat + 32 ≤ cd.size)
    (hlenMax : ¬ solcMaxLen DecodeMode.legacySolc05 <
      (calldataWord cd (4 + (calldataWord cd 132).toNat)).toNat)
    (hpayload :
      (((cd.toList.drop 4).drop ((calldataWord cd 132).toNat + 32)).take
        (calldataWord cd (4 + (calldataWord cd 132).toNat)).toNat).length =
        (calldataWord cd (4 + (calldataWord cd 132).toNat)).toNat) :
    decodeCalldataWithMode DecodeMode.legacySolc05 [a, b, c, d, e]
        [abiUInt256, abiUInt256, abiUInt256, abiAddress, abiBytes] cd =
      some (legacyThreeUintAddressBytesDecodedStore cd a b c d e) := by
  have htlen : cd.toList.length = cd.size := by
    rw [byteArray_toList_eq, Array.length_toList]
    rfl
  have htake4 : ((cd.toList.drop 4).take 32).length = 32 := by
    rw [List.length_take, List.length_drop, htlen]
    omega
  have htake36 : ((cd.toList.drop 4).drop 32 |>.take 32).length = 32 := by
    rw [List.length_take, List.length_drop, List.length_drop, htlen]
    omega
  have htake68 : ((cd.toList.drop 4).drop 64 |>.take 32).length = 32 := by
    rw [List.length_take, List.length_drop, List.length_drop, htlen]
    omega
  have htake100 : ((cd.toList.drop 4).drop 96 |>.take 32).length = 32 := by
    rw [List.length_take, List.length_drop, List.length_drop, htlen]
    omega
  have hword4 : ABI.bytesToWord ((cd.toList.drop 4).take 32) = calldataWord cd 4 :=
    decode_word_at_eq cd 4 (by omega) (by norm_num)
  have hword36 : ABI.bytesToWord (((cd.toList.drop 4).drop 32).take 32) =
      calldataWord cd 36 := by
    simpa [List.drop_drop, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using
      decode_word_at_eq cd 36 (by omega) (by norm_num)
  have hword68 : ABI.bytesToWord (((cd.toList.drop 4).drop 64).take 32) =
      calldataWord cd 68 := by
    simpa [List.drop_drop, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using
      decode_word_at_eq cd 68 (by omega) (by norm_num)
  have hword100 : ABI.bytesToWord (((cd.toList.drop 4).drop 96).take 32) =
      calldataWord cd 100 := by
    simpa [List.drop_drop, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using
      decode_word_at_eq cd 100 (by omega) (by norm_num)
  have hdecode0 := decodeABIValue_legacyUint256_ok (bytes := cd.toList.drop 4)
    (start := 0) (by simpa using htake4)
  have hdecode32 := decodeABIValue_legacyUint256_ok (bytes := cd.toList.drop 4)
    (start := 32) htake36
  have hdecode64 := decodeABIValue_legacyUint256_ok (bytes := cd.toList.drop 4)
    (start := 64) htake68
  have hdecode96 := decodeABIValue_legacyAddress_ok (bytes := cd.toList.drop 4)
    (start := 96) htake100
  have hreadOff :
      readNat? (cd.toList.drop 4) 128 = some (calldataWord cd 132).toNat := by
    simpa using readNat_drop4_at_eq_calldataWord (cd := cd) 128 (by omega)
  have hreadLen :
      readNat? (cd.toList.drop 4) (calldataWord cd 132).toNat =
        some (calldataWord cd (4 + (calldataWord cd 132).toNat)).toNat :=
    readNat_drop4_at_eq_calldataWord (cd := cd) (calldataWord cd 132).toNat hlenWord
  have hdecodeBytes :
      decodeABIValue? abiBytes (cd.toList.drop 4) (calldataWord cd 132).toNat
          DecodeMode.legacySolc05 =
        some (.bytes (ByteArray.mk
            ((((cd.toList.drop 4).drop ((calldataWord cd 132).toNat + 32)).take
              (calldataWord cd (4 + (calldataWord cd 132).toNat)).toNat).toArray)),
          (calldataWord cd 132).toNat + 32 +
            paddedSize (calldataWord cd (4 + (calldataWord cd 132).toNat)).toNat) := by
    simpa [abiBytes] using
      decodeABIValue_legacyBytes_ok (bytes := cd.toList.drop 4)
        (start := (calldataWord cd 132).toNat)
        (len := (calldataWord cd (4 + (calldataWord cd 132).toNat)).toNat)
        hreadLen hlenMax hpayload
  unfold decodeCalldataWithMode decodeCalldata
  rw [if_neg (by rw [htlen]; omega : ¬ cd.toList.length < 4)]
  rw [if_neg (by
    rintro ⟨_, hhuge⟩
    rw [htlen] at hhuge
    omega)]
  simp only [decodeCalldata.decodeArgs]
  rw [show abiTupleHeadSize? [abiUInt256, abiUInt256, abiUInt256, abiAddress,
    abiBytes] = some 160 by
    simp [abiTupleHeadSize?, isDynamicABIType, staticABIEncodedSize?,
      abiBytes32, abiBytes32Width, abiUInt256, abiAddress, abiInt256, abiBytes]]
  simp only [Option.bind, bind]
  rw [if_neg (by rw [List.length_drop, htlen]; omega :
    ¬ (cd.toList.drop 4).length < 160)]
  have hdynUInt : isDynamicABIType abiUInt256 = false := by
    decide
  have hsizeUInt : staticABIEncodedSize? abiUInt256 = some 32 := by
    decide
  have hdynAddr : isDynamicABIType abiAddress = false := by
    decide
  have hsizeAddr : staticABIEncodedSize? abiAddress = some 32 := by
    decide
  have hdynBytes : isDynamicABIType abiBytes = true := by
    decide
  have hvalues :
      decodeABIValues? [abiUInt256, abiUInt256, abiUInt256, abiAddress, abiBytes] (cd.toList.drop 4)
          0 0 160 160 DecodeMode.legacySolc05 =
        some ([Value.int (Int.ofNat (calldataWord cd 4).toNat),
          Value.int (Int.ofNat (calldataWord cd 36).toNat),
          Value.int (Int.ofNat (calldataWord cd 68).toNat),
          Value.address (AccountAddress.ofNat (calldataWord cd 100).toNat),
          Value.bytes (ByteArray.mk
            ((((cd.toList.drop 4).drop ((calldataWord cd 132).toNat + 32)).take
              (calldataWord cd (4 + (calldataWord cd 132).toNat)).toNat).toArray))],
          max 160 ((calldataWord cd 132).toNat + 32 +
            paddedSize (calldataWord cd (4 + (calldataWord cd 132).toNat)).toNat)) := by
    rw [decodeABIValues?]
    rw [hdynUInt]
    simp only [Bool.false_eq_true, if_false, hsizeUInt, Option.bind, bind, Nat.zero_add]
    rw [hdecode0]
    simp only [Nat.zero_add, if_true]
    rw [decodeABIValues?]
    rw [hdynUInt]
    simp only [Bool.false_eq_true, if_false, hsizeUInt, Option.bind, bind]
    rw [hdecode32]
    simp only [if_true]
    rw [decodeABIValues?]
    rw [hdynUInt]
    simp only [Bool.false_eq_true, if_false, hsizeUInt, Option.bind, bind]
    rw [hdecode64]
    simp only [if_true]
    rw [decodeABIValues?]
    rw [hdynAddr]
    simp only [Bool.false_eq_true, if_false, hsizeAddr, Option.bind, bind]
    rw [hdecode96]
    simp only [if_true]
    rw [decodeABIValues?]
    rw [hdynBytes]
    simp only [if_true, Option.bind, bind]
    rw [hreadOff]
    dsimp only
    rw [if_neg hoffMax]
    simp only [Nat.zero_add]
    rw [hdecodeBytes]
    simp only [ABI.decodeABIValues?.eq_def, hword4, hword36, hword68, hword100,
      List.drop_zero]
    norm_num
  rw [hvalues]
  simp [decodeCalldata.insertValues, legacyThreeUintAddressBytesDecodedStore,
    legacyThreeUintAddressBytesDecodedBytes]

theorem decodeCalldata_legacyUint256_uint256_uint256_address_bytes_none_short
    {cd : ByteArray} {a b c d e : Solm.Ident} (hsz4 : 4 ≤ cd.size)
    (hshort : cd.size < 164) :
    decodeCalldataWithMode DecodeMode.legacySolc05 [a, b, c, d, e]
      [abiUInt256, abiUInt256, abiUInt256, abiAddress, abiBytes] cd = none := by
  have htlen : cd.toList.length = cd.size := by
    rw [byteArray_toList_eq, Array.length_toList]
    rfl
  unfold decodeCalldataWithMode decodeCalldata
  rw [if_neg (by rw [htlen]; omega : ¬ cd.toList.length < 4)]
  rw [if_neg (by
    rintro ⟨_, hhuge⟩
    rw [htlen] at hhuge
    omega)]
  simp only [decodeCalldata.decodeArgs]
  rw [show abiTupleHeadSize? [abiUInt256, abiUInt256, abiUInt256, abiAddress,
    abiBytes] = some 160 by
    simp [abiTupleHeadSize?, isDynamicABIType, staticABIEncodedSize?,
      abiBytes32, abiBytes32Width, abiUInt256, abiAddress, abiInt256, abiBytes]]
  simp only [Option.bind, bind]
  rw [if_pos (by rw [List.length_drop, htlen]; omega :
    (cd.toList.drop 4).length < 160)]

set_option maxHeartbeats 1000000 in
theorem decodeCalldata_legacyUint256_uint256_uint256_address_bytes_none_offset_huge
    {cd : ByteArray} {a b c d e : Solm.Ident}
    (hsmall : cd.size < 2 ^ 255)
    (hsz164 : 164 ≤ cd.size)
    (hoff : solcMaxLen DecodeMode.legacySolc05 < (calldataWord cd 132).toNat) :
    decodeCalldataWithMode DecodeMode.legacySolc05 [a, b, c, d, e]
      [abiUInt256, abiUInt256, abiUInt256, abiAddress, abiBytes] cd = none := by
  have htlen : cd.toList.length = cd.size := by
    rw [byteArray_toList_eq, Array.length_toList]
    rfl
  have htake4 : ((cd.toList.drop 4).take 32).length = 32 := by
    rw [List.length_take, List.length_drop, htlen]
    omega
  have htake36 : ((cd.toList.drop 4).drop 32 |>.take 32).length = 32 := by
    rw [List.length_take, List.length_drop, List.length_drop, htlen]
    omega
  have htake68 : ((cd.toList.drop 4).drop 64 |>.take 32).length = 32 := by
    rw [List.length_take, List.length_drop, List.length_drop, htlen]
    omega
  have htake100 : ((cd.toList.drop 4).drop 96 |>.take 32).length = 32 := by
    rw [List.length_take, List.length_drop, List.length_drop, htlen]
    omega
  have hdecode0 := decodeABIValue_legacyUint256_ok (bytes := cd.toList.drop 4)
    (start := 0) (by simpa using htake4)
  have hdecode32 := decodeABIValue_legacyUint256_ok (bytes := cd.toList.drop 4)
    (start := 32) htake36
  have hdecode64 := decodeABIValue_legacyUint256_ok (bytes := cd.toList.drop 4)
    (start := 64) htake68
  have hdecode96 := decodeABIValue_legacyAddress_ok (bytes := cd.toList.drop 4)
    (start := 96) htake100
  have hreadOff :
      readNat? (cd.toList.drop 4) 128 = some (calldataWord cd 132).toNat := by
    simpa using readNat_drop4_at_eq_calldataWord (cd := cd) 128 (by omega)
  unfold decodeCalldataWithMode decodeCalldata
  rw [if_neg (by rw [htlen]; omega : ¬ cd.toList.length < 4)]
  rw [if_neg (by
    rintro ⟨_, hhuge⟩
    rw [htlen] at hhuge
    omega)]
  simp only [decodeCalldata.decodeArgs]
  rw [show abiTupleHeadSize? [abiUInt256, abiUInt256, abiUInt256, abiAddress,
    abiBytes] = some 160 by
    simp [abiTupleHeadSize?, isDynamicABIType, staticABIEncodedSize?,
      abiBytes32, abiBytes32Width, abiUInt256, abiAddress, abiInt256, abiBytes]]
  simp only [Option.bind, bind]
  rw [if_neg (by rw [List.length_drop, htlen]; omega :
    ¬ (cd.toList.drop 4).length < 160)]
  have hdynUInt : isDynamicABIType abiUInt256 = false := by
    decide
  have hsizeUInt : staticABIEncodedSize? abiUInt256 = some 32 := by
    decide
  have hdynAddr : isDynamicABIType abiAddress = false := by
    decide
  have hsizeAddr : staticABIEncodedSize? abiAddress = some 32 := by
    decide
  have hdynBytes : isDynamicABIType abiBytes = true := by
    decide
  rw [decodeABIValues?]
  rw [hdynUInt]
  simp only [Bool.false_eq_true, if_false, hsizeUInt, Option.bind, bind, Nat.zero_add]
  rw [hdecode0]
  simp only [Nat.zero_add, if_true]
  rw [decodeABIValues?]
  rw [hdynUInt]
  simp only [Bool.false_eq_true, if_false, hsizeUInt, Option.bind, bind]
  rw [hdecode32]
  simp only [if_true]
  rw [decodeABIValues?]
  rw [hdynUInt]
  simp only [Bool.false_eq_true, if_false, hsizeUInt, Option.bind, bind]
  rw [hdecode64]
  simp only [if_true]
  rw [decodeABIValues?]
  rw [hdynAddr]
  simp only [Bool.false_eq_true, if_false, hsizeAddr, Option.bind, bind]
  rw [hdecode96]
  simp only [if_true]
  rw [decodeABIValues?]
  rw [hdynBytes]
  simp only [if_true, Option.bind, bind]
  rw [hreadOff]
  dsimp only
  rw [if_pos hoff]

theorem decodeABIValue_legacyBytes_none_length_short {bytes : List UInt8} {start : Nat}
    (hreadLen : readNat? bytes start = none) :
    decodeABIValue? abiBytes bytes start DecodeMode.legacySolc05 = none := by
  unfold decodeABIValue?
  simp [abiBytes, hreadLen, Option.bind, bind]

theorem decodeABIValue_legacyBytes_none_length_huge {bytes : List UInt8} {start len : Nat}
    (hreadLen : readNat? bytes start = some len)
    (hlenHuge : solcMaxLen DecodeMode.legacySolc05 < len) :
    decodeABIValue? abiBytes bytes start DecodeMode.legacySolc05 = none := by
  unfold decodeABIValue?
  simp [abiBytes, hreadLen, Option.bind, bind, hlenHuge]

theorem decodeABIValue_legacyBytes_none_payload_short {bytes : List UInt8} {start len : Nat}
    (hreadLen : readNat? bytes start = some len)
    (hlenMax : ¬ solcMaxLen DecodeMode.legacySolc05 < len)
    (hpayloadShort : ((bytes.drop (start + 32)).take len).length ≠ len) :
    decodeABIValue? abiBytes bytes start DecodeMode.legacySolc05 = none := by
  unfold decodeABIValue?
  simp only [abiBytes, hreadLen, Option.bind, bind]
  rw [if_neg hlenMax]
  unfold readBytes?
  rw [if_neg hpayloadShort]

set_option maxHeartbeats 1000000 in
theorem decodeCalldata_legacyUint256_uint256_uint256_address_bytes_none_length_short
    {cd : ByteArray} {a b c d e : Solm.Ident}
    (hsmall : cd.size < 2 ^ 255)
    (hsz164 : 164 ≤ cd.size)
    (hoffMax : ¬ solcMaxLen DecodeMode.legacySolc05 < (calldataWord cd 132).toNat)
    (hshort : cd.size < 4 + (calldataWord cd 132).toNat + 32) :
    decodeCalldataWithMode DecodeMode.legacySolc05 [a, b, c, d, e]
      [abiUInt256, abiUInt256, abiUInt256, abiAddress, abiBytes] cd = none := by
  have htlen : cd.toList.length = cd.size := by
    rw [byteArray_toList_eq, Array.length_toList]
    rfl
  have htake4 : ((cd.toList.drop 4).take 32).length = 32 := by
    rw [List.length_take, List.length_drop, htlen]
    omega
  have htake36 : ((cd.toList.drop 4).drop 32 |>.take 32).length = 32 := by
    rw [List.length_take, List.length_drop, List.length_drop, htlen]
    omega
  have htake68 : ((cd.toList.drop 4).drop 64 |>.take 32).length = 32 := by
    rw [List.length_take, List.length_drop, List.length_drop, htlen]
    omega
  have htake100 : ((cd.toList.drop 4).drop 96 |>.take 32).length = 32 := by
    rw [List.length_take, List.length_drop, List.length_drop, htlen]
    omega
  have hdecode0 := decodeABIValue_legacyUint256_ok (bytes := cd.toList.drop 4)
    (start := 0) (by simpa using htake4)
  have hdecode32 := decodeABIValue_legacyUint256_ok (bytes := cd.toList.drop 4)
    (start := 32) htake36
  have hdecode64 := decodeABIValue_legacyUint256_ok (bytes := cd.toList.drop 4)
    (start := 64) htake68
  have hdecode96 := decodeABIValue_legacyAddress_ok (bytes := cd.toList.drop 4)
    (start := 96) htake100
  have hreadOff :
      readNat? (cd.toList.drop 4) 128 = some (calldataWord cd 132).toNat := by
    simpa using readNat_drop4_at_eq_calldataWord (cd := cd) 128 (by omega)
  have hreadLen :
      readNat? (cd.toList.drop 4) (calldataWord cd 132).toNat = none := by
    unfold readNat? readWord? readBytes?
    have hlen :
        ¬ (((cd.toList.drop 4).drop (calldataWord cd 132).toNat).take 32).length = 32 := by
      rw [List.length_take, List.length_drop, List.length_drop, htlen]
      omega
    rw [if_neg hlen]
    rfl
  have hdecodeBytes :
      decodeABIValue? abiBytes (cd.toList.drop 4) (calldataWord cd 132).toNat
          DecodeMode.legacySolc05 = none :=
    decodeABIValue_legacyBytes_none_length_short hreadLen
  unfold decodeCalldataWithMode decodeCalldata
  rw [if_neg (by rw [htlen]; omega : ¬ cd.toList.length < 4)]
  rw [if_neg (by
    rintro ⟨_, hhuge⟩
    rw [htlen] at hhuge
    omega)]
  simp only [decodeCalldata.decodeArgs]
  rw [show abiTupleHeadSize? [abiUInt256, abiUInt256, abiUInt256, abiAddress,
    abiBytes] = some 160 by
    simp [abiTupleHeadSize?, isDynamicABIType, staticABIEncodedSize?,
      abiBytes32, abiBytes32Width, abiUInt256, abiAddress, abiInt256, abiBytes]]
  simp only [Option.bind, bind]
  rw [if_neg (by rw [List.length_drop, htlen]; omega :
    ¬ (cd.toList.drop 4).length < 160)]
  have hdynUInt : isDynamicABIType abiUInt256 = false := by
    decide
  have hsizeUInt : staticABIEncodedSize? abiUInt256 = some 32 := by
    decide
  have hdynAddr : isDynamicABIType abiAddress = false := by
    decide
  have hsizeAddr : staticABIEncodedSize? abiAddress = some 32 := by
    decide
  have hdynBytes : isDynamicABIType abiBytes = true := by
    decide
  rw [decodeABIValues?]
  rw [hdynUInt]
  simp only [Bool.false_eq_true, if_false, hsizeUInt, Option.bind, bind, Nat.zero_add]
  rw [hdecode0]
  simp only [Nat.zero_add, if_true]
  rw [decodeABIValues?]
  rw [hdynUInt]
  simp only [Bool.false_eq_true, if_false, hsizeUInt, Option.bind, bind]
  rw [hdecode32]
  simp only [if_true]
  rw [decodeABIValues?]
  rw [hdynUInt]
  simp only [Bool.false_eq_true, if_false, hsizeUInt, Option.bind, bind]
  rw [hdecode64]
  simp only [if_true]
  rw [decodeABIValues?]
  rw [hdynAddr]
  simp only [Bool.false_eq_true, if_false, hsizeAddr, Option.bind, bind]
  rw [hdecode96]
  simp only [if_true]
  rw [decodeABIValues?]
  rw [hdynBytes]
  simp only [if_true, Option.bind, bind]
  rw [hreadOff]
  dsimp only
  rw [if_neg hoffMax]
  simp only [Nat.zero_add]
  rw [hdecodeBytes]

set_option maxHeartbeats 1000000 in
theorem decodeCalldata_legacyUint256_uint256_uint256_address_bytes_none_length_huge
    {cd : ByteArray} {a b c d e : Solm.Ident}
    (hsmall : cd.size < 2 ^ 255)
    (hsz164 : 164 ≤ cd.size)
    (hoffMax : ¬ solcMaxLen DecodeMode.legacySolc05 < (calldataWord cd 132).toNat)
    (hlenWord : 4 + (calldataWord cd 132).toNat + 32 ≤ cd.size)
    (hlenHuge :
      solcMaxLen DecodeMode.legacySolc05 <
        (calldataWord cd (4 + (calldataWord cd 132).toNat)).toNat) :
    decodeCalldataWithMode DecodeMode.legacySolc05 [a, b, c, d, e]
      [abiUInt256, abiUInt256, abiUInt256, abiAddress, abiBytes] cd = none := by
  have htlen : cd.toList.length = cd.size := by
    rw [byteArray_toList_eq, Array.length_toList]
    rfl
  have htake4 : ((cd.toList.drop 4).take 32).length = 32 := by
    rw [List.length_take, List.length_drop, htlen]
    omega
  have htake36 : ((cd.toList.drop 4).drop 32 |>.take 32).length = 32 := by
    rw [List.length_take, List.length_drop, List.length_drop, htlen]
    omega
  have htake68 : ((cd.toList.drop 4).drop 64 |>.take 32).length = 32 := by
    rw [List.length_take, List.length_drop, List.length_drop, htlen]
    omega
  have htake100 : ((cd.toList.drop 4).drop 96 |>.take 32).length = 32 := by
    rw [List.length_take, List.length_drop, List.length_drop, htlen]
    omega
  have hdecode0 := decodeABIValue_legacyUint256_ok (bytes := cd.toList.drop 4)
    (start := 0) (by simpa using htake4)
  have hdecode32 := decodeABIValue_legacyUint256_ok (bytes := cd.toList.drop 4)
    (start := 32) htake36
  have hdecode64 := decodeABIValue_legacyUint256_ok (bytes := cd.toList.drop 4)
    (start := 64) htake68
  have hdecode96 := decodeABIValue_legacyAddress_ok (bytes := cd.toList.drop 4)
    (start := 96) htake100
  have hreadOff :
      readNat? (cd.toList.drop 4) 128 = some (calldataWord cd 132).toNat := by
    simpa using readNat_drop4_at_eq_calldataWord (cd := cd) 128 (by omega)
  have hreadLen :
      readNat? (cd.toList.drop 4) (calldataWord cd 132).toNat =
        some (calldataWord cd (4 + (calldataWord cd 132).toNat)).toNat :=
    readNat_drop4_at_eq_calldataWord (cd := cd) (calldataWord cd 132).toNat hlenWord
  have hdecodeBytes :
      decodeABIValue? abiBytes (cd.toList.drop 4) (calldataWord cd 132).toNat
          DecodeMode.legacySolc05 = none :=
    decodeABIValue_legacyBytes_none_length_huge hreadLen hlenHuge
  unfold decodeCalldataWithMode decodeCalldata
  rw [if_neg (by rw [htlen]; omega : ¬ cd.toList.length < 4)]
  rw [if_neg (by
    rintro ⟨_, hhuge⟩
    rw [htlen] at hhuge
    omega)]
  simp only [decodeCalldata.decodeArgs]
  rw [show abiTupleHeadSize? [abiUInt256, abiUInt256, abiUInt256, abiAddress,
    abiBytes] = some 160 by
    simp [abiTupleHeadSize?, isDynamicABIType, staticABIEncodedSize?,
      abiBytes32, abiBytes32Width, abiUInt256, abiAddress, abiInt256, abiBytes]]
  simp only [Option.bind, bind]
  rw [if_neg (by rw [List.length_drop, htlen]; omega :
    ¬ (cd.toList.drop 4).length < 160)]
  have hdynUInt : isDynamicABIType abiUInt256 = false := by
    decide
  have hsizeUInt : staticABIEncodedSize? abiUInt256 = some 32 := by
    decide
  have hdynAddr : isDynamicABIType abiAddress = false := by
    decide
  have hsizeAddr : staticABIEncodedSize? abiAddress = some 32 := by
    decide
  have hdynBytes : isDynamicABIType abiBytes = true := by
    decide
  rw [decodeABIValues?]
  rw [hdynUInt]
  simp only [Bool.false_eq_true, if_false, hsizeUInt, Option.bind, bind, Nat.zero_add]
  rw [hdecode0]
  simp only [Nat.zero_add, if_true]
  rw [decodeABIValues?]
  rw [hdynUInt]
  simp only [Bool.false_eq_true, if_false, hsizeUInt, Option.bind, bind]
  rw [hdecode32]
  simp only [if_true]
  rw [decodeABIValues?]
  rw [hdynUInt]
  simp only [Bool.false_eq_true, if_false, hsizeUInt, Option.bind, bind]
  rw [hdecode64]
  simp only [if_true]
  rw [decodeABIValues?]
  rw [hdynAddr]
  simp only [Bool.false_eq_true, if_false, hsizeAddr, Option.bind, bind]
  rw [hdecode96]
  simp only [if_true]
  rw [decodeABIValues?]
  rw [hdynBytes]
  simp only [if_true, Option.bind, bind]
  rw [hreadOff]
  dsimp only
  rw [if_neg hoffMax]
  simp only [Nat.zero_add]
  rw [hdecodeBytes]

set_option maxHeartbeats 1000000 in
theorem decodeCalldata_legacyUint256_uint256_uint256_address_bytes_none_payload_short
    {cd : ByteArray} {a b c d e : Solm.Ident}
    (hsmall : cd.size < 2 ^ 255)
    (hsz164 : 164 ≤ cd.size)
    (hoffMax : ¬ solcMaxLen DecodeMode.legacySolc05 < (calldataWord cd 132).toNat)
    (hlenWord : 4 + (calldataWord cd 132).toNat + 32 ≤ cd.size)
    (hlenMax : ¬ solcMaxLen DecodeMode.legacySolc05 <
      (calldataWord cd (4 + (calldataWord cd 132).toNat)).toNat)
    (hpayloadShort :
      (((cd.toList.drop 4).drop ((calldataWord cd 132).toNat + 32)).take
        (calldataWord cd (4 + (calldataWord cd 132).toNat)).toNat).length ≠
        (calldataWord cd (4 + (calldataWord cd 132).toNat)).toNat) :
    decodeCalldataWithMode DecodeMode.legacySolc05 [a, b, c, d, e]
      [abiUInt256, abiUInt256, abiUInt256, abiAddress, abiBytes] cd = none := by
  have htlen : cd.toList.length = cd.size := by
    rw [byteArray_toList_eq, Array.length_toList]
    rfl
  have htake4 : ((cd.toList.drop 4).take 32).length = 32 := by
    rw [List.length_take, List.length_drop, htlen]
    omega
  have htake36 : ((cd.toList.drop 4).drop 32 |>.take 32).length = 32 := by
    rw [List.length_take, List.length_drop, List.length_drop, htlen]
    omega
  have htake68 : ((cd.toList.drop 4).drop 64 |>.take 32).length = 32 := by
    rw [List.length_take, List.length_drop, List.length_drop, htlen]
    omega
  have htake100 : ((cd.toList.drop 4).drop 96 |>.take 32).length = 32 := by
    rw [List.length_take, List.length_drop, List.length_drop, htlen]
    omega
  have hdecode0 := decodeABIValue_legacyUint256_ok (bytes := cd.toList.drop 4)
    (start := 0) (by simpa using htake4)
  have hdecode32 := decodeABIValue_legacyUint256_ok (bytes := cd.toList.drop 4)
    (start := 32) htake36
  have hdecode64 := decodeABIValue_legacyUint256_ok (bytes := cd.toList.drop 4)
    (start := 64) htake68
  have hdecode96 := decodeABIValue_legacyAddress_ok (bytes := cd.toList.drop 4)
    (start := 96) htake100
  have hreadOff :
      readNat? (cd.toList.drop 4) 128 = some (calldataWord cd 132).toNat := by
    simpa using readNat_drop4_at_eq_calldataWord (cd := cd) 128 (by omega)
  have hreadLen :
      readNat? (cd.toList.drop 4) (calldataWord cd 132).toNat =
        some (calldataWord cd (4 + (calldataWord cd 132).toNat)).toNat :=
    readNat_drop4_at_eq_calldataWord (cd := cd) (calldataWord cd 132).toNat hlenWord
  have hdecodeBytes :
      decodeABIValue? abiBytes (cd.toList.drop 4) (calldataWord cd 132).toNat
          DecodeMode.legacySolc05 = none :=
    decodeABIValue_legacyBytes_none_payload_short hreadLen hlenMax hpayloadShort
  unfold decodeCalldataWithMode decodeCalldata
  rw [if_neg (by rw [htlen]; omega : ¬ cd.toList.length < 4)]
  rw [if_neg (by
    rintro ⟨_, hhuge⟩
    rw [htlen] at hhuge
    omega)]
  simp only [decodeCalldata.decodeArgs]
  rw [show abiTupleHeadSize? [abiUInt256, abiUInt256, abiUInt256, abiAddress,
    abiBytes] = some 160 by
    simp [abiTupleHeadSize?, isDynamicABIType, staticABIEncodedSize?,
      abiBytes32, abiBytes32Width, abiUInt256, abiAddress, abiInt256, abiBytes]]
  simp only [Option.bind, bind]
  rw [if_neg (by rw [List.length_drop, htlen]; omega :
    ¬ (cd.toList.drop 4).length < 160)]
  have hdynUInt : isDynamicABIType abiUInt256 = false := by
    decide
  have hsizeUInt : staticABIEncodedSize? abiUInt256 = some 32 := by
    decide
  have hdynAddr : isDynamicABIType abiAddress = false := by
    decide
  have hsizeAddr : staticABIEncodedSize? abiAddress = some 32 := by
    decide
  have hdynBytes : isDynamicABIType abiBytes = true := by
    decide
  rw [decodeABIValues?]
  rw [hdynUInt]
  simp only [Bool.false_eq_true, if_false, hsizeUInt, Option.bind, bind, Nat.zero_add]
  rw [hdecode0]
  simp only [Nat.zero_add, if_true]
  rw [decodeABIValues?]
  rw [hdynUInt]
  simp only [Bool.false_eq_true, if_false, hsizeUInt, Option.bind, bind]
  rw [hdecode32]
  simp only [if_true]
  rw [decodeABIValues?]
  rw [hdynUInt]
  simp only [Bool.false_eq_true, if_false, hsizeUInt, Option.bind, bind]
  rw [hdecode64]
  simp only [if_true]
  rw [decodeABIValues?]
  rw [hdynAddr]
  simp only [Bool.false_eq_true, if_false, hsizeAddr, Option.bind, bind]
  rw [hdecode96]
  simp only [if_true]
  rw [decodeABIValues?]
  rw [hdynBytes]
  simp only [if_true, Option.bind, bind]
  rw [hreadOff]
  dsimp only
  rw [if_neg hoffMax]
  simp only [Nat.zero_add]
  rw [hdecodeBytes]

theorem readNat?_calldataWord_eq {I : ExecutionEnv} {headOff off : Nat}
    (hread : readNat? (List.drop 4 I.calldata.toList) headOff = some off) :
    calldataWord I.calldata (4 + headOff) = UInt256.ofNat off := by
  have hreadLen := readNat?_some_length hread
  have htlen : I.calldata.toList.length = I.calldata.size := by
    rw [byteArray_toList_eq, Array.length_toList]
    rfl
  have hsz : 4 + headOff + 32 ≤ I.calldata.size := by
    rw [List.length_drop, htlen] at hreadLen
    omega
  rw [calldataWord]
  rw [← decode_word_at_eq_any I.calldata (4 + headOff) hsz]
  have hword := readNat?_some_bytesToWord hread
  simpa [List.drop_drop, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hword



end Reasoning.Theory
