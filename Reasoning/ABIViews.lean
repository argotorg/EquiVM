import Reasoning.ABIComposite
import Reasoning.MemoryArithmetic

/-!
# ABI word views and compiler bounds

Reusable tuple encoders, raw and padded word views, and bounds connecting compiler calldata
checks to strict and legacy ABI decoders.
-/

open Solm ABI Ethereum Ethereum.EVM Reasoning.Reach

set_option autoImplicit false
set_option maxRecDepth 2000000
set_option maxHeartbeats 2000000

namespace Reasoning.Theory

theorem addrUintUintReturnEncoding (w chop dunk : UInt256) :
    encodeReturnValues? [abiAddress, abiUInt256, abiUInt256]
      [.address (AccountAddress.ofNat (UInt256.land w solcAddrMask).toNat),
        .int (Int.ofNat chop.toNat), .int (Int.ofNat dunk.toNat)] =
      some (UInt256.toByteArray (UInt256.land w solcAddrMask) ++
        UInt256.toByteArray chop ++ UInt256.toByteArray dunk) := by
  have hencFlip :
      encodeABIValue? abiAddress
        (.address (AccountAddress.ofNat (UInt256.land w solcAddrMask).toNat)) =
        some (EVM.Word.toBytesBE (UInt256.land w solcAddrMask)) := by
    have hcanon := solcAddrMask_result_canonical w
    have haddrMod : (UInt256.land w solcAddrMask).toNat % AccountAddress.size =
        (UInt256.land w solcAddrMask).toNat := by
      apply Nat.mod_eq_of_lt
      simpa [EVM.addressModulus, EVM.twoPow, AccountAddress.size] using hcanon
    have hword : EVM.word (UInt256.land w solcAddrMask).toNat = UInt256.land w solcAddrMask :=
      u256_ofNat_toNat _
    simp [abiAddress, encodeABIValue?, encodeABIWord?, AccountAddress.ofNat, haddrMod, hword]
  have hencChop :
      encodeABIValue? abiUInt256 (.int (Int.ofNat chop.toNat)) =
        some (EVM.Word.toBytesBE chop) := by
    have hword : EVM.word chop.toNat = chop := u256_ofNat_toNat chop
    have hlt : chop.toNat < EVM.twoPow 256 := chop.val.isLt
    simp [abiUInt256, abiUInt256Int, encodeABIValue?, encodeABIWord?, hword, hlt]
  have hencDunk :
      encodeABIValue? abiUInt256 (.int (Int.ofNat dunk.toNat)) =
        some (EVM.Word.toBytesBE dunk) := by
    have hword : EVM.word dunk.toNat = dunk := u256_ofNat_toNat dunk
    have hlt : dunk.toNat < EVM.twoPow 256 := dunk.val.isLt
    simp [abiUInt256, abiUInt256Int, encodeABIValue?, encodeABIWord?, hword, hlt]
  rw [show UInt256.toByteArray (UInt256.land w solcAddrMask) =
      (EVM.Word.toBytesBE (UInt256.land w solcAddrMask)).toByteArray by
    exact (word_toBytesBE_toByteArray_eq_toByteArray (UInt256.land w solcAddrMask)).symm]
  rw [show UInt256.toByteArray chop = (EVM.Word.toBytesBE chop).toByteArray by
    exact (word_toBytesBE_toByteArray_eq_toByteArray chop).symm]
  rw [show UInt256.toByteArray dunk = (EVM.Word.toBytesBE dunk).toByteArray by
    exact (word_toBytesBE_toByteArray_eq_toByteArray dunk).symm]
  unfold encodeReturnValues? encodeABIValues?
  rw [show abiTupleHeadSize? [abiAddress, abiUInt256, abiUInt256] = some 96 by
    simp [abiTupleHeadSize?, isDynamicABIType, staticABIEncodedSize?, abiUInt256, abiAddress,
      abiBytes32, abiBytes32Width, abiBool]]
  simp only [bind, Option.bind]
  unfold encodeABIValuesFrom?
  rw [hencFlip]
  simp only [bind, Option.bind]
  rw [show isDynamicABIType abiAddress = false by decide]
  unfold encodeABIValuesFrom?
  rw [hencChop]
  simp only [bind, Option.bind]
  rw [show isDynamicABIType abiUInt256 = false by decide]
  unfold encodeABIValuesFrom?
  rw [hencDunk]
  simp only [bind, Option.bind]
  rw [show isDynamicABIType abiUInt256 = false by decide]
  unfold encodeABIValuesFrom?
  simp only [Bool.false_eq_true, if_false, List.nil_append, List.append_nil]
  apply congrArg some
  apply ByteArray.ext
  simp [ByteArray.data_append, ByteArray.append_assoc]

theorem spotterIlksDecode_none_short_aux {out : ByteArray}
    (hshort : out.size < 64) :
    ABI.decodeReturnValuesWithMode? DecodeMode.legacySolc05 [abiAddress, abiUInt256] out =
      none := by
  have hlen : out.toList.length = out.size := by
    rw [byteArray_toList_eq, Array.length_toList]
    rfl
  unfold ABI.decodeReturnValuesWithMode?
  rw [abiTupleHeadSize_scalarWords_eq
    (types := [abiAddress, abiUInt256]) (by decide)]
  simp only [bind, Option.bind]
  rw [decodeABIValues_scalarWordsWithMode_eq (mode := DecodeMode.legacySolc05)
    (types := [abiAddress, abiUInt256]) (bytes := out.toList)
    (cursor := 0) (total := 32 * [abiAddress, abiUInt256].length)
    (by decide) (by simp)]
  cases hdec : decodeScalarWordsWithMode? DecodeMode.legacySolc05
      [abiAddress, abiUInt256] out.toList 0 with
  | none => rfl
  | some values =>
      have hlenDecoded :=
        decodeScalarWordsWithMode?_some_length (mode := DecodeMode.legacySolc05)
          (types := [abiAddress, abiUInt256]) (bytes := out.toList)
          (cursor := 0) (values := values) (by omega) hdec
      rw [hlen] at hlenDecoded
      simp only [List.length_cons, List.length_nil, Nat.zero_add] at hlenDecoded
      omega

theorem decodeABIValues_legacy_none_short {bytes : List UInt8}
    (hshort : bytes.length < 64) :
    decodeABIValues? [abiBytes32, abiBool] bytes 0 0 64 64 DecodeMode.legacySolc05 =
      none := by
  simp only [decodeABIValues?, abiBytes32, abiBytes32Width, abiBool, isDynamicABIType,
    Bool.false_eq_true, if_false, staticABIEncodedSize?, bind, Option.bind, Nat.zero_add]
  by_cases h32 : bytes.length < 32
  · have hnot : ¬ 32 ≤ bytes.length := by omega
    simp [decodeABIValue?, readBytes?, hnot]
  · have htake0 : (bytes.take 32).length = 32 := by
      rw [List.length_take]
      omega
    have htake32n : ¬ ((bytes.drop 32).take 32).length = 32 := by
      rw [List.length_take, List.length_drop]
      omega
    have hbool : decodeABIValue? abiBool bytes 32 DecodeMode.legacySolc05 = none := by
      rw [decodeABIValue_scalarWordWithMode_eq (mode := DecodeMode.legacySolc05)
        (ty := abiBool) (bytes := bytes) (start := 32) (by decide)]
      exact decodeScalarWordWithMode_legacy_bool_none_short (bytes := bytes) (start := 32)
        htake32n
    simp [decodeABIValue?, readBytes?, htake0, hbool]

theorem decode_none_short_aux {out : ByteArray} (hshort : out.size < 64) :
    ABI.decodeReturnValuesWithMode? DecodeMode.legacySolc05 [abiBytes32, abiBool] out =
      none := by
  have hlen : out.toList.length = out.size := by
    rw [byteArray_toList_eq, Array.length_toList]
    rfl
  unfold ABI.decodeReturnValuesWithMode?
  rw [show abiTupleHeadSize? [abiBytes32, abiBool] = some 64 by
    simp [abiTupleHeadSize?, isDynamicABIType, staticABIEncodedSize?, abiUInt256, abiAddress,
      abiBytes32, abiBytes32Width, abiBool]]
  simp only [bind, Option.bind]
  rw [decodeABIValues_legacy_none_short (bytes := out.toList) (by omega)]

theorem vatIlksDecode_none_short_aux {out : ByteArray} (hshort : out.size < 160) :
    ABI.decodeReturnValuesWithMode? DecodeMode.legacySolc05
      [abiUInt256, abiUInt256, abiUInt256, abiUInt256, abiUInt256] out = none := by
  have hlen : out.toList.length = out.size := by
    rw [byteArray_toList_eq, Array.length_toList]
    rfl
  unfold ABI.decodeReturnValuesWithMode?
  rw [abiTupleHeadSize_scalarWords_eq
    (types := [abiUInt256, abiUInt256, abiUInt256, abiUInt256, abiUInt256]) (by decide)]
  simp only [bind, Option.bind]
  rw [decodeABIValues_scalarWordsWithMode_eq (mode := DecodeMode.legacySolc05)
    (types := [abiUInt256, abiUInt256, abiUInt256, abiUInt256, abiUInt256]) (bytes := out.toList)
    (cursor := 0) (total := 32 * [abiUInt256, abiUInt256, abiUInt256, abiUInt256,
      abiUInt256].length)
    (by decide) (by simp)]
  cases hdec : decodeScalarWordsWithMode? DecodeMode.legacySolc05
      [abiUInt256, abiUInt256, abiUInt256, abiUInt256, abiUInt256] out.toList 0 with
  | none => rfl
  | some values =>
      have hlenDecoded :=
        decodeScalarWordsWithMode?_some_length (mode := DecodeMode.legacySolc05)
          (types := [abiUInt256, abiUInt256, abiUInt256, abiUInt256, abiUInt256])
          (bytes := out.toList) (cursor := 0) (values := values) (by omega) hdec
      rw [hlen] at hlenDecoded
      simp only [List.length_cons, List.length_nil, Nat.zero_add] at hlenDecoded
      omega

theorem encodeABIValue_address_word (w : UInt256) :
    encodeABIValue? abiAddress
        (.address (AccountAddress.ofNat (UInt256.land w solcAddrMask).toNat)) =
      some (UInt256.toByteArray (UInt256.land w solcAddrMask)).toList := by
  have hcanon := solcAddrMask_result_canonical w
  have haddrMod : (UInt256.land w solcAddrMask).toNat % AccountAddress.size =
      (UInt256.land w solcAddrMask).toNat := by
    apply Nat.mod_eq_of_lt
    simpa [EVM.addressModulus, EVM.twoPow, AccountAddress.size] using hcanon
  have hword : EVM.word (UInt256.land w solcAddrMask).toNat =
      UInt256.land w solcAddrMask := u256_ofNat_toNat _
  simp [abiAddress, encodeABIValue?, encodeABIWord?, AccountAddress.ofNat, haddrMod, hword,
    toByteArray_eq_toBytesBE, byteArray_toList_eq]

theorem eip191ByteArray_toList : (⟨#[25, 1]⟩ : ByteArray).toList = [25, 1] := by
  decide +kernel

theorem encodePacked_dynamic_bytes (bytes : ByteArray) :
    encodePackedValue? ABIType.bytes (.bytes bytes) = some bytes.toList := by
  rfl

theorem ilksReturnEncoding (clip chop hole dirt : UInt256) :
    encodeReturnValues? [abiAddress, abiUInt256, abiUInt256, abiUInt256]
      [.address (AccountAddress.ofNat (UInt256.land clip solcAddrMask).toNat),
        .int (Int.ofNat chop.toNat), .int (Int.ofNat hole.toNat),
        .int (Int.ofNat dirt.toNat)] =
        some (UInt256.toByteArray (UInt256.land clip solcAddrMask) ++
          UInt256.toByteArray chop ++ UInt256.toByteArray hole ++ UInt256.toByteArray dirt) := by
  have hencAddr :
      encodeABIValue? abiAddress
          (.address (AccountAddress.ofNat (UInt256.land clip solcAddrMask).toNat)) =
        some (EVM.Word.toBytesBE (UInt256.land clip solcAddrMask)) := by
    have hcanon := solcAddrMask_result_canonical clip
    have haddrMod : (UInt256.land clip solcAddrMask).toNat % AccountAddress.size =
        (UInt256.land clip solcAddrMask).toNat := by
      apply Nat.mod_eq_of_lt
      simpa [EVM.addressModulus, EVM.twoPow, AccountAddress.size] using hcanon
    have hword :
        EVM.word (UInt256.land clip solcAddrMask).toNat =
          UInt256.land clip solcAddrMask :=
      u256_ofNat_toNat _
    simp [abiAddress, encodeABIValue?, encodeABIWord?, AccountAddress.ofNat, haddrMod, hword]
  have hencUint : ∀ w : UInt256,
      encodeABIValue? abiUInt256 (.int (Int.ofNat w.toNat)) =
        some (EVM.Word.toBytesBE w) := by
    intro w
    have hword : EVM.word w.toNat = w := by
      show UInt256.ofNat w.toNat = w
      exact u256_ofNat_toNat w
    have hlt : w.toNat < EVM.twoPow 256 := by
      change w.val.val < EVM.twoPow 256
      exact w.val.isLt
    simp [abiUInt256, abiUInt256Int, encodeABIValue?, encodeABIWord?, hword, hlt]
  rw [show UInt256.toByteArray (UInt256.land clip solcAddrMask) =
      (EVM.Word.toBytesBE (UInt256.land clip solcAddrMask)).toByteArray by
    exact (word_toBytesBE_toByteArray_eq_toByteArray
      (UInt256.land clip solcAddrMask)).symm]
  rw [show UInt256.toByteArray chop = (EVM.Word.toBytesBE chop).toByteArray by
    exact (word_toBytesBE_toByteArray_eq_toByteArray chop).symm]
  rw [show UInt256.toByteArray hole = (EVM.Word.toBytesBE hole).toByteArray by
    exact (word_toBytesBE_toByteArray_eq_toByteArray hole).symm]
  rw [show UInt256.toByteArray dirt = (EVM.Word.toBytesBE dirt).toByteArray by
    exact (word_toBytesBE_toByteArray_eq_toByteArray dirt).symm]
  unfold encodeReturnValues? encodeABIValues?
  rw [show abiTupleHeadSize? [abiAddress, abiUInt256, abiUInt256, abiUInt256] = some 128 by
    simp [abiTupleHeadSize?, isDynamicABIType, staticABIEncodedSize?, abiUInt256, abiAddress,
      abiBytes32, abiBytes32Width, abiBool]]
  simp only [bind, Option.bind]
  unfold encodeABIValuesFrom?
  rw [hencAddr]
  simp only [bind, Option.bind]
  rw [show isDynamicABIType abiAddress = false by decide]
  unfold encodeABIValuesFrom?
  rw [hencUint chop]
  simp only [bind, Option.bind]
  rw [show isDynamicABIType abiUInt256 = false by decide]
  unfold encodeABIValuesFrom?
  rw [hencUint hole]
  simp only [bind, Option.bind]
  rw [show isDynamicABIType abiUInt256 = false by decide]
  unfold encodeABIValuesFrom?
  rw [hencUint dirt]
  simp only [bind, Option.bind]
  rw [show isDynamicABIType abiUInt256 = false by decide]
  unfold encodeABIValuesFrom?
  simp only [Bool.false_eq_true, if_false, List.nil_append, List.append_nil]
  apply congrArg some
  apply ByteArray.ext
  simp [ByteArray.data_append]

theorem decode_legacyBytes32_address_ok {cd : ByteArray} {x y : Ident}
    (hsz68 : 68 ≤ cd.size) :
    decodeCalldataWithMode DecodeMode.legacySolc05 [x, y] [abiBytes32, abiAddress] cd =
      some (((∅ : Store).insert x
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
  rw [if_neg (by simp [abiBytes32, abiBytes32Width, abiAddress, isDynamicABIType])]
  simp only [decodeCalldata.decodeArgs]
  rw [show abiTupleHeadSize? [abiBytes32, abiAddress] = some 64 by
    simp [abiTupleHeadSize?, isDynamicABIType, staticABIEncodedSize?, abiUInt256, abiAddress,
      abiBytes32, abiBytes32Width, abiBool]]
  simp only [bind, Option.bind]
  rw [decodeABIValues_bytes32_address_legacy_ok (bytes := cd.toList.drop 4)
    (by simpa using htake4)
    (by simpa [List.drop_drop, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using htake36)]
  rw [if_neg (by rw [List.length_drop, htlen]; omega : ¬ (cd.toList.drop 4).length < 64)]
  simp [decodeCalldata.insertValues]
  rw [hword36]

theorem decode_legacyBytes32_address_none_short {cd : ByteArray}
    {x y : Ident} (hsz4 : 4 ≤ cd.size) (hshort : cd.size < 68) :
    decodeCalldataWithMode DecodeMode.legacySolc05 [x, y] [abiBytes32, abiAddress] cd =
      none := by
  have htlen : cd.toList.length = cd.size := by
    rw [byteArray_toList_eq, Array.length_toList]
    rfl
  unfold decodeCalldataWithMode decodeCalldata
  rw [if_neg (by rw [htlen]; omega : ¬ cd.toList.length < 4)]
  rw [if_neg (by simp [abiBytes32, abiBytes32Width, abiAddress, isDynamicABIType])]
  simp only [decodeCalldata.decodeArgs]
  rw [show abiTupleHeadSize? [abiBytes32, abiAddress] = some 64 by
    simp [abiTupleHeadSize?, isDynamicABIType, staticABIEncodedSize?, abiUInt256, abiAddress,
      abiBytes32, abiBytes32Width, abiBool]]
  simp only [bind, Option.bind]
  by_cases hbytes : (cd.toList.drop 4).length < 64
  · rw [if_pos hbytes]
  · rw [if_neg hbytes]
    rw [decodeABIValues_bytes32_address_legacy_none_short (bytes := cd.toList.drop 4) (by
      rw [List.length_drop, htlen]
      omega)]

theorem decode_legacyUint256_ok {cd : ByteArray} {x : Ident}
    (hsz36 : 36 ≤ cd.size) :
    decodeCalldataWithMode DecodeMode.legacySolc05 [x] [abiUInt256] cd =
      some ((∅ : Store).insert x (.int (Int.ofNat (calldataWord cd 4).toNat))) := by
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
    some ((∅ : Store).insert x (.int (Int.ofNat (calldataWord cd 4).toNat)))
  rw [hword4]
  simp [decodeCalldata.insertValues]

theorem decode_legacyUint256_none_short {cd : ByteArray} {x : Ident}
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

theorem decode_legacyBytes32_uint256_ok {cd : ByteArray} {x y : Ident}
    (hsz68 : 68 ≤ cd.size) :
    decodeCalldataWithMode DecodeMode.legacySolc05 [x, y] [abiBytes32, abiUInt256] cd =
      some (((∅ : Store).insert x
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
  rw [if_neg (by simp [abiBytes32, abiBytes32Width, abiUInt256, isDynamicABIType])]
  simp only [decodeCalldata.decodeArgs]
  rw [show abiTupleHeadSize? [abiBytes32, abiUInt256] = some 64 by
    simp [abiTupleHeadSize?, isDynamicABIType, staticABIEncodedSize?, abiUInt256, abiAddress,
      abiBytes32, abiBytes32Width, abiBool]]
  simp only [bind, Option.bind]
  rw [decodeABIValues_bytes32_uint256_legacy_ok (bytes := cd.toList.drop 4)
    (by simpa using htake4)
    (by simpa [List.drop_drop, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using htake36)]
  rw [if_neg (by rw [List.length_drop, htlen]; omega : ¬ (cd.toList.drop 4).length < 64)]
  simp [decodeCalldata.insertValues]
  rw [hword36]

theorem decode_legacyBytes32_uint256_none_short {cd : ByteArray}
    {x y : Ident} (hsz4 : 4 ≤ cd.size) (hshort : cd.size < 68) :
    decodeCalldataWithMode DecodeMode.legacySolc05 [x, y] [abiBytes32, abiUInt256] cd =
      none := by
  have htlen : cd.toList.length = cd.size := by
    rw [byteArray_toList_eq, Array.length_toList]
    rfl
  unfold decodeCalldataWithMode decodeCalldata
  rw [if_neg (by rw [htlen]; omega : ¬ cd.toList.length < 4)]
  rw [if_neg (by simp [abiBytes32, abiBytes32Width, abiUInt256, isDynamicABIType])]
  simp only [decodeCalldata.decodeArgs]
  rw [show abiTupleHeadSize? [abiBytes32, abiUInt256] = some 64 by
    simp [abiTupleHeadSize?, isDynamicABIType, staticABIEncodedSize?, abiUInt256, abiAddress,
      abiBytes32, abiBytes32Width, abiBool]]
  simp only [bind, Option.bind]
  by_cases hbytes : (cd.toList.drop 4).length < 64
  · rw [if_pos hbytes]
  · rw [if_neg hbytes]
    rw [decodeABIValues_bytes32_uint256_legacy_none_short (bytes := cd.toList.drop 4) (by
      rw [List.length_drop, htlen]
      omega)]

theorem freeUrnsDecode_none_short_aux {out : ByteArray} (hshort : out.size < 64) :
    ABI.decodeReturnValuesWithMode? DecodeMode.legacySolc05 [abiUInt256, abiUInt256] out =
      none := by
  have hlen : out.toList.length = out.size := by
    rw [byteArray_toList_eq, Array.length_toList]
    rfl
  unfold ABI.decodeReturnValuesWithMode?
  rw [abiTupleHeadSize_scalarWords_eq (types := [abiUInt256, abiUInt256]) (by decide)]
  simp only [bind, Option.bind]
  rw [decodeABIValues_scalarWordsWithMode_eq (mode := DecodeMode.legacySolc05)
    (types := [abiUInt256, abiUInt256]) (bytes := out.toList) (cursor := 0)
    (total := 32 * [abiUInt256, abiUInt256].length)
    (by decide) (by simp)]
  simp only [decodeScalarWordsWithMode?]
  by_cases hfirst : ((out.toList.drop 0).take 32).length = 32
  · rw [decodeScalarWordWithMode_uint256_ok (mode := DecodeMode.legacySolc05)
      (bytes := out.toList) (start := 0) hfirst]
    simp only [Option.bind_eq_bind, Option.bind_some]
    have htake32n : ¬ ((out.toList.drop 32).take 32).length = 32 := by
      rw [List.length_take, List.length_drop, hlen]
      omega
    rw [decodeScalarWordWithMode_uint256_none_short (mode := DecodeMode.legacySolc05)
      (bytes := out.toList) (start := 32) htake32n]
    simp
  · rw [decodeScalarWordWithMode_uint256_none_short (mode := DecodeMode.legacySolc05)
      (bytes := out.toList) (start := 0) hfirst]
    simp

theorem encodeABIValue_uint256_word (w : UInt256) :
    encodeABIValue? abiUInt256 (.int (Int.ofNat w.toNat)) =
      some (UInt256.toByteArray w).toList := by
  have hlt : w.toNat < EVM.twoPow 256 := w.val.isLt
  have hword : EVM.word w.toNat = w := u256_ofNat_toNat w
  simp [abiUInt256, abiUInt256Int, encodeABIValue?, encodeABIWord?, hlt, hword,
    toByteArray_eq_toBytesBE, byteArray_toList_eq]

theorem encodeABIValue_bytes32_word (w : UInt256) :
    encodeABIValue? abiBytes32 (.fixedBytes abiBytes32Width (EVM.Word.toBytesBE w)) =
      some (UInt256.toByteArray w).toList := by
  have hlen : (EVM.Word.toBytesBE w).length = 32 := by
    simpa [toByteArray_eq_toBytesBE] using word_toBytesBE_toByteArray_size w
  have hz : zeroBytes 0 = [] := by decide
  simp [abiBytes32, abiBytes32Width, encodeABIValue?, hlen, hz,
    toByteArray_eq_toBytesBE, byteArray_toList_eq]

theorem encodeABIValue_this_address (I : ExecutionEnv) :
    encodeABIValue? abiAddress (.address I.codeOwner) =
      some (UInt256.toByteArray (EVM.word I.codeOwner.val)).toList := by
  have hword : EVM.word I.codeOwner.val = EVM.word I.codeOwner.val := rfl
  simp [abiAddress, encodeABIValue?, encodeABIWord?, AccountAddress.ofNat,
    EVM.addressModulus, hword, toByteArray_eq_toBytesBE, byteArray_toList_eq]

theorem encodeABIValue_source_address (I : ExecutionEnv) :
    encodeABIValue? abiAddress (.address I.source) =
      some (UInt256.toByteArray (solcSourceWord I)).toList := by
  have hword : EVM.word I.source.val = solcSourceWord I := rfl
  simp [abiAddress, encodeABIValue?, encodeABIWord?, AccountAddress.ofNat, EVM.addressModulus,
    hword, toByteArray_eq_toBytesBE, byteArray_toList_eq]

theorem uint256PairReturnEncoding (first second : UInt256) :
    encodeReturnValues? [abiUInt256, abiUInt256]
      [.int (Int.ofNat first.toNat), .int (Int.ofNat second.toNat)] =
        some (UInt256.toByteArray first ++ UInt256.toByteArray second) := by
  have hencFirst :
      encodeABIValue? abiUInt256 (.int (Int.ofNat first.toNat)) =
        some (EVM.Word.toBytesBE first) := by
    have hword : EVM.word first.toNat = first := by
      show UInt256.ofNat first.toNat = first
      exact u256_ofNat_toNat first
    have hlt : first.toNat < EVM.twoPow 256 := by
      change first.val.val < EVM.twoPow 256
      exact first.val.isLt
    simp [abiUInt256, abiUInt256Int, encodeABIValue?, encodeABIWord?, hword, hlt]
  have hencSecond :
      encodeABIValue? abiUInt256 (.int (Int.ofNat second.toNat)) =
        some (EVM.Word.toBytesBE second) := by
    have hword : EVM.word second.toNat = second := by
      show UInt256.ofNat second.toNat = second
      exact u256_ofNat_toNat second
    have hlt : second.toNat < EVM.twoPow 256 := by
      change second.val.val < EVM.twoPow 256
      exact second.val.isLt
    simp [abiUInt256, abiUInt256Int, encodeABIValue?, encodeABIWord?, hword, hlt]
  rw [show UInt256.toByteArray first = (EVM.Word.toBytesBE first).toByteArray by
    exact (word_toBytesBE_toByteArray_eq_toByteArray first).symm]
  rw [show UInt256.toByteArray second = (EVM.Word.toBytesBE second).toByteArray by
    exact (word_toBytesBE_toByteArray_eq_toByteArray second).symm]
  unfold encodeReturnValues? encodeABIValues?
  rw [show abiTupleHeadSize? [abiUInt256, abiUInt256] = some 64 by
    simp [abiTupleHeadSize?, isDynamicABIType, staticABIEncodedSize?, abiUInt256, abiAddress,
      abiBytes32, abiBytes32Width, abiBool]]
  simp only [bind, Option.bind]
  unfold encodeABIValuesFrom?
  rw [hencFirst]
  simp only [bind, Option.bind]
  rw [show isDynamicABIType abiUInt256 = false by decide]
  unfold encodeABIValuesFrom?
  rw [hencSecond]
  simp only [bind, Option.bind]
  rw [show isDynamicABIType abiUInt256 = false by decide]
  unfold encodeABIValuesFrom?
  simp only [Bool.false_eq_true, if_false, List.nil_append, List.append_nil]
  apply congrArg some
  apply ByteArray.ext
  simp [ByteArray.data_append]

theorem addressUint256PairReturnEncoding (first second : UInt256) :
    encodeReturnValues? [abiAddress, abiUInt256]
      [.address (AccountAddress.ofNat (UInt256.land first solcAddrMask).toNat),
        .int (Int.ofNat second.toNat)] =
        some (UInt256.toByteArray (UInt256.land first solcAddrMask) ++
          UInt256.toByteArray second) := by
  have hencFirst :
      encodeABIValue? abiAddress
          (.address (AccountAddress.ofNat (UInt256.land first solcAddrMask).toNat)) =
        some (EVM.Word.toBytesBE (UInt256.land first solcAddrMask)) := by
    have hcanon := solcAddrMask_result_canonical first
    have haddrMod : (UInt256.land first solcAddrMask).toNat % AccountAddress.size =
        (UInt256.land first solcAddrMask).toNat := by
      apply Nat.mod_eq_of_lt
      simpa [EVM.addressModulus, EVM.twoPow, AccountAddress.size] using hcanon
    have hword :
        EVM.word (UInt256.land first solcAddrMask).toNat =
          UInt256.land first solcAddrMask :=
      u256_ofNat_toNat _
    simp [abiAddress, encodeABIValue?, encodeABIWord?, AccountAddress.ofNat, haddrMod, hword]
  have hencSecond :
      encodeABIValue? abiUInt256 (.int (Int.ofNat second.toNat)) =
        some (EVM.Word.toBytesBE second) := by
    have hword : EVM.word second.toNat = second := by
      show UInt256.ofNat second.toNat = second
      exact u256_ofNat_toNat second
    have hlt : second.toNat < EVM.twoPow 256 := by
      change second.val.val < EVM.twoPow 256
      exact second.val.isLt
    simp [abiUInt256, abiUInt256Int, encodeABIValue?, encodeABIWord?, hword, hlt]
  rw [show UInt256.toByteArray (UInt256.land first solcAddrMask) =
      (EVM.Word.toBytesBE (UInt256.land first solcAddrMask)).toByteArray by
    exact (word_toBytesBE_toByteArray_eq_toByteArray
      (UInt256.land first solcAddrMask)).symm]
  rw [show UInt256.toByteArray second = (EVM.Word.toBytesBE second).toByteArray by
    exact (word_toBytesBE_toByteArray_eq_toByteArray second).symm]
  unfold encodeReturnValues? encodeABIValues?
  rw [show abiTupleHeadSize? [abiAddress, abiUInt256] = some 64 by
    simp [abiTupleHeadSize?, isDynamicABIType, staticABIEncodedSize?, abiUInt256, abiAddress,
      abiBytes32, abiBytes32Width, abiBool]]
  simp only [bind, Option.bind]
  unfold encodeABIValuesFrom?
  rw [hencFirst]
  simp only [bind, Option.bind]
  rw [show isDynamicABIType abiAddress = false by decide]
  unfold encodeABIValuesFrom?
  rw [hencSecond]
  simp only [bind, Option.bind]
  rw [show isDynamicABIType abiUInt256 = false by decide]
  unfold encodeABIValuesFrom?
  simp only [Bool.false_eq_true, if_false, List.nil_append, List.append_nil]
  apply congrArg some
  apply ByteArray.ext
  simp [ByteArray.data_append]

theorem decodeCalldata_legacyBytes32_legacyAddress_ok {cd : ByteArray} {x y : Solm.Ident}
    (hsz68 : 68 ≤ cd.size) :
    decodeCalldataWithMode DecodeMode.legacySolc05 [x, y] [abiBytes32, abiAddress] cd =
      some (((∅ : Store).insert x
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
  rw [if_neg (by simp [abiBytes32, abiBytes32Width, abiAddress, isDynamicABIType])]
  simp only
  simp only [decodeCalldata.decodeArgs]
  rw [show abiTupleHeadSize? [abiBytes32, abiAddress] = some 64 by
    simp [abiTupleHeadSize?, isDynamicABIType, staticABIEncodedSize?, abiUInt256, abiAddress,
      abiBytes32, abiBytes32Width, abiBool]]
  simp only [bind, Option.bind]
  rw [if_neg (by rw [List.length_drop, htlen]; omega :
    ¬ (cd.toList.drop 4).length < 64)]
  rw [decodeABIValues_bytes32_address_legacy_ok
    (bytes := cd.toList.drop 4)
    (by simpa using htake4)
    (by simpa [List.drop_drop, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc]
      using htake36)]
  rw [show ABI.bytesToWord (((cd.toList.drop 4).drop 32).take 32) =
      calldataWord cd 36 from by
    simpa [List.drop_drop, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using hword36]
  simp [decodeCalldata.insertValues]

theorem uint256FiveReturnEncoding (art rate spot line dust : UInt256) :
    encodeReturnValues? [abiUInt256, abiUInt256, abiUInt256, abiUInt256, abiUInt256]
      [.int (Int.ofNat art.toNat), .int (Int.ofNat rate.toNat),
        .int (Int.ofNat spot.toNat), .int (Int.ofNat line.toNat),
        .int (Int.ofNat dust.toNat)] =
        some (UInt256.toByteArray art ++ UInt256.toByteArray rate ++ UInt256.toByteArray spot ++
          UInt256.toByteArray line ++ UInt256.toByteArray dust) := by
  rw [show UInt256.toByteArray art = (EVM.Word.toBytesBE art).toByteArray by
    exact (word_toBytesBE_toByteArray_eq_toByteArray art).symm]
  rw [show UInt256.toByteArray rate = (EVM.Word.toBytesBE rate).toByteArray by
    exact (word_toBytesBE_toByteArray_eq_toByteArray rate).symm]
  rw [show UInt256.toByteArray spot = (EVM.Word.toBytesBE spot).toByteArray by
    exact (word_toBytesBE_toByteArray_eq_toByteArray spot).symm]
  rw [show UInt256.toByteArray line = (EVM.Word.toBytesBE line).toByteArray by
    exact (word_toBytesBE_toByteArray_eq_toByteArray line).symm]
  rw [show UInt256.toByteArray dust = (EVM.Word.toBytesBE dust).toByteArray by
    exact (word_toBytesBE_toByteArray_eq_toByteArray dust).symm]
  unfold encodeReturnValues? encodeABIValues?
  rw [show abiTupleHeadSize? [abiUInt256, abiUInt256, abiUInt256, abiUInt256, abiUInt256] = some 160
    by simp [abiTupleHeadSize?, isDynamicABIType, staticABIEncodedSize?, abiUInt256, abiAddress,
      abiBytes32, abiBytes32Width, abiBool]]
  simp only [bind, Option.bind]
  unfold encodeABIValuesFrom?
  rw [encodeABIValue_uint256 art]
  simp only [bind, Option.bind]
  rw [show isDynamicABIType abiUInt256 = false by decide]
  unfold encodeABIValuesFrom?
  rw [encodeABIValue_uint256 rate]
  simp only [bind, Option.bind]
  rw [show isDynamicABIType abiUInt256 = false by decide]
  unfold encodeABIValuesFrom?
  rw [encodeABIValue_uint256 spot]
  simp only [bind, Option.bind]
  rw [show isDynamicABIType abiUInt256 = false by decide]
  unfold encodeABIValuesFrom?
  rw [encodeABIValue_uint256 line]
  simp only [bind, Option.bind]
  rw [show isDynamicABIType abiUInt256 = false by decide]
  unfold encodeABIValuesFrom?
  rw [encodeABIValue_uint256 dust]
  simp only [bind, Option.bind]
  rw [show isDynamicABIType abiUInt256 = false by decide]
  unfold encodeABIValuesFrom?
  simp only [Bool.false_eq_true, if_false, List.nil_append, List.append_nil]
  apply congrArg some
  apply ByteArray.ext
  simp [ByteArray.data_append]

/-- ABI-encoding a `Proposal` getter return list is exactly `name || voteCount`. -/
theorem proposalReturnEncoding (name count : UInt256) :
    encodeReturnValues? [abiBytes32, abiUInt256]
      [.fixedBytes ⟨31, by decide⟩ (EVM.Word.toBytesBE name),
        .int (Int.ofNat count.toNat)] =
      some (UInt256.toByteArray name ++ UInt256.toByteArray count) := by
  have hnameLen : (EVM.Word.toBytesBE name).length = 32 := by
    simpa using word_toBytesBE_toByteArray_size name
  have hword : EVM.word count.toNat = count := u256_ofNat_toNat count
  have hlt : count.toNat < EVM.twoPow 256 := by
    change count.val.val < EVM.twoPow 256
    exact count.val.isLt
  have hencName :
      encodeABIValue? abiBytes32 (.fixedBytes ⟨31, by decide⟩ (EVM.Word.toBytesBE name)) =
        some (EVM.Word.toBytesBE name) := by
    simp only [abiBytes32, abiBytes32Width, encodeABIValue?, hnameLen, zeroBytes]
    simp
  have hencCount :
      encodeABIValue? abiUInt256 (.int (Int.ofNat count.toNat)) =
        some (EVM.Word.toBytesBE count) := by
    simp [abiUInt256, abiUInt256Int, encodeABIValue?, encodeABIWord?, hword, hlt]
  have hhead : abiTupleHeadSize? [abiBytes32, abiUInt256] = some 64 := by
    simp [abiTupleHeadSize?, isDynamicABIType, staticABIEncodedSize?, abiUInt256, abiAddress,
      abiBytes32, abiBytes32Width, abiBool]
  have hdynBytes : isDynamicABIType abiBytes32 = false := by decide
  have hdynUint : isDynamicABIType abiUInt256 = false := by decide
  rw [toByteArray_eq_toBytesBE name, toByteArray_eq_toBytesBE count]
  simp only [encodeReturnValues?, encodeABIValues?, encodeABIValuesFrom?,
    hhead, hencName, hencCount, hdynBytes, hdynUint, bind, Option.bind, Bool.false_eq_true,
      if_false,
    List.nil_append, List.append_nil]
  apply congrArg some
  apply ByteArray.ext
  apply Array.toList_inj.mp
  simp

theorem bidsReturnEncoding (blinded deposit : UInt256) :
    encodeReturnValues? [abiBytes32, abiUInt256]
      [.fixedBytes ⟨31, by decide⟩ (EVM.Word.toBytesBE blinded),
        .int (Int.ofNat deposit.toNat)] =
      some (UInt256.toByteArray blinded ++ UInt256.toByteArray deposit) := by
  have hblindedLen : (EVM.Word.toBytesBE blinded).length = 32 := by
    simpa using word_toBytesBE_toByteArray_size blinded
  have hword : EVM.word deposit.toNat = deposit := u256_ofNat_toNat deposit
  have hlt : deposit.toNat < EVM.twoPow 256 := by
    change deposit.val.val < EVM.twoPow 256
    exact deposit.val.isLt
  have hencBlinded :
      encodeABIValue? abiBytes32 (.fixedBytes ⟨31, by decide⟩ (EVM.Word.toBytesBE blinded)) =
        some (EVM.Word.toBytesBE blinded) := by
    simp only [abiBytes32, abiBytes32Width, encodeABIValue?, hblindedLen, zeroBytes]
    simp
  have hencDeposit :
      encodeABIValue? abiUInt256 (.int (Int.ofNat deposit.toNat)) =
        some (EVM.Word.toBytesBE deposit) := by
    simp [abiUInt256, abiUInt256Int, encodeABIValue?, encodeABIWord?, hword, hlt]
  have hhead : abiTupleHeadSize? [abiBytes32, abiUInt256] = some 64 := by
    simp [abiTupleHeadSize?, isDynamicABIType, staticABIEncodedSize?, abiUInt256, abiAddress,
      abiBytes32, abiBytes32Width, abiBool]
  have hdynBytes : isDynamicABIType abiBytes32 = false := by decide
  have hdynUint : isDynamicABIType abiUInt256 = false := by decide
  rw [toByteArray_eq_toBytesBE blinded, toByteArray_eq_toBytesBE deposit]
  simp only [encodeReturnValues?, encodeABIValues?, encodeABIValuesFrom?,
    hhead, hencBlinded, hencDeposit, hdynBytes, hdynUint, bind, Option.bind,
    Bool.false_eq_true, if_false,
    List.nil_append, List.append_nil]
  apply congrArg some
  apply ByteArray.ext
  apply Array.toList_inj.mp
  simp

/-- The 32-byte big-endian ABI encoding of `2^N` (for `N < 256`, so it fits a word) is exactly the
    EVM `RETURN` word `UInt256.ofNat (2^N)`. -/
theorem pow2ReturnEncoding {N : ℕ} (hN : N < 256) :
    encodeReturnValue? abiUInt256 (.int (Int.ofNat (2 ^ N)))
      = some (UInt256.toByteArray (UInt256.ofNat (2 ^ N))) := by
  have hlt : Int.ofNat (2 ^ N) < Int.ofNat (EVM.twoPow 256) := by
    simp only [Int.ofNat_eq_natCast, Nat.cast_lt, EVM.twoPow]
    exact Nat.pow_lt_pow_right (by norm_num) hN
  -- the single ABI value encodes to the 32 big-endian bytes of `ofNat (2^N)`
  have hval : encodeABIValue? abiUInt256 (.int (Int.ofNat (2 ^ N)))
                = some (EVM.Word.toBytesBE (UInt256.ofNat (2 ^ N))) := by
    simp only [abiUInt256, encodeABIValue?, encodeABIWord?]
    rw [if_neg (by decide), if_pos ⟨Int.natCast_nonneg _, hlt⟩, evm_word_eq_ofNat]; rfl
  have hdyn : isDynamicABIType abiUInt256 = false := rfl
  have hhead : abiTupleHeadSize? [abiUInt256] = some 32 := by
    simp only [abiTupleHeadSize?, staticABIEncodedSize?, isDynamicABIType, abiUInt256, bind,
      Option.bind]
    decide
  exact scalarReturnEncoding hdyn hhead hval

theorem decodeCalldata_string_some {cd : ByteArray} {x : Solm.Ident}
    (hsz36 : 36 ≤ cd.size) (hsizeSign : cd.size < 2 ^ 255)
    (hoffMax : ¬ ABI.solcMaxU64 < (calldataWord cd 4).toNat)
    (hlenWord : 4 + (calldataWord cd 4).toNat + 32 ≤ cd.size)
    (hlenMax :
      ¬ ABI.solcMaxU64 <
        (calldataWord cd (4 + (calldataWord cd 4).toNat)).toNat)
    (hpayload :
      (((cd.toList.drop 4).drop ((calldataWord cd 4).toNat + 32)).take
        (calldataWord cd (4 + (calldataWord cd 4).toNat)).toNat).length =
        (calldataWord cd (4 + (calldataWord cd 4).toNat)).toNat) :
    decodeCalldata [x] [ABIType.string] cd =
      some ((∅ : Store).insert x (.bytes (ByteArray.mk
        (((cd.toList.drop 4).drop ((calldataWord cd 4).toNat + 32)).take
          (calldataWord cd (4 + (calldataWord cd 4).toNat)).toNat).toArray))) := by
  unfold decodeCalldata
  have htlen : cd.toList.length = cd.size := by
    rw [byteArray_toList_eq, Array.length_toList]; rfl
  rw [if_neg (by rw [htlen]; omega : ¬ cd.toList.length < 4)]
  rw [if_neg (by
    rintro ⟨_, hhuge⟩
    rw [htlen] at hhuge
    omega)]
  rw [if_neg (by
    rintro ⟨_, hhuge⟩
    rw [List.length_drop, htlen] at hhuge
    omega)]
  rw [if_neg (by
    rintro ⟨_, hhuge⟩
    rw [htlen] at hhuge
    omega)]
  have hreadOff := readNat_drop4_zero_eq_calldataWord (cd := cd) hsz36
  have hreadLen := readNat_drop4_dynamic_eq_calldataWord (cd := cd) hlenWord
  have hpayloadRead := readBytes_drop4_string_payload (cd := cd) hpayload
  have hnotHeadShort : ¬ cd.toList.length - 4 < 32 := by
    rw [htlen]
    omega
  simp [decodeCalldata.decodeArgs, decodeCalldata.insertValues, decodeABIValues?,
    decodeABIValue?, isDynamicABIType, abiTupleHeadSize?, ABI.solcMaxLen, hreadOff, hoffMax,
    hreadLen, hlenMax, hpayloadRead, hnotHeadShort]

theorem calldataLengthWord_eq_abi
    (cd : ByteArray)
    (hoffMax : ¬ ABI.solcMaxU64 < (calldataWord cd 4).toNat) :
    uInt256OfByteArray
        (cd.readBytes ((((⟨4⟩ : UInt256) + calldataWord cd 4)).toNat) 32) =
      calldataWord cd (4 + (calldataWord cd 4).toNat) := by
  have hoffLeMax : (calldataWord cd 4).toNat ≤ 18446744073709551615 := by
    simpa [ABI.solcMaxU64] using Nat.le_of_not_gt hoffMax
  have haddr :
      (((⟨4⟩ : UInt256) + calldataWord cd 4).toNat) =
        4 + (calldataWord cd 4).toNat := by
    rw [uadd_toNat]
    rw [show (⟨4⟩ : UInt256).toNat = 4 from by decide]
    rw [Nat.add_comm]
    exact Nat.mod_eq_of_lt (by
      have hsize : 4 + (calldataWord cd 4).toNat < UInt256.size := by
        have hsmall : 4 + (calldataWord cd 4).toNat ≤ 18446744073709551619 := by
          omega
        exact lt_of_le_of_lt hsmall (by norm_num [UInt256.size])
      simpa [Nat.add_comm] using hsize)
  simp [calldataWord, haddr]

theorem calldataStartPlus31_toNat
    (cd : ByteArray)
    (hoffMax : ¬ ABI.solcMaxU64 < (calldataWord cd 4).toNat) :
    (((⟨4⟩ : UInt256) + calldataWord cd 4) + ⟨31⟩).toNat =
      4 + (calldataWord cd 4).toNat + 31 := by
  have hoffLeMax : (calldataWord cd 4).toNat ≤ 18446744073709551615 := by
    simpa [ABI.solcMaxU64] using Nat.le_of_not_gt hoffMax
  have hoffSmall : (calldataWord cd 4).toNat < 2 ^ 255 := by
    omega
  have hoffSize : (calldataWord cd 4).toNat < UInt256.size :=
    (calldataWord cd 4).val.isLt
  have hoffOfNat :
      (UInt256.ofNat (calldataWord cd 4).toNat).toNat =
        (calldataWord cd 4).toNat :=
    ulit_toNat' _ hoffSize
  rw [← u256_ofNat_toNat (calldataWord cd 4)]
  simpa [hoffOfNat] using (uadd3_ofNat_toNat (a := 4)
    (b := (calldataWord cd 4).toNat)
    (c := 31)
    (by norm_num [UInt256.size])
    (lt_size_of_lt_sign hoffSmall)
    (by norm_num [UInt256.size])
    (lt_size_of_lt_sign (by omega : 4 + (calldataWord cd 4).toNat < 2 ^ 255))
    (lt_size_of_lt_sign (by omega :
      4 + (calldataWord cd 4).toNat + 31 < 2 ^ 255)))

theorem calldataStart_slt_one
    (cd : ByteArray)
    (hoffMax : ¬ ABI.solcMaxU64 < (calldataWord cd 4).toNat)
    (hlenWord : 4 + (calldataWord cd 4).toNat + 32 ≤ cd.size)
    (hsizeSign : cd.size < 2 ^ 255) :
    UInt256.slt ((((⟨4⟩ : UInt256) + calldataWord cd 4) + ⟨31⟩))
        (UInt256.ofNat cd.size) = ⟨1⟩ := by
  apply slt_lit_one_low hsizeSign
  rw [calldataStartPlus31_toNat cd hoffMax]
  omega

theorem calldataStart_slt_zero_of_size_high
    (cd : ByteArray)
    (hoffMax : ¬ ABI.solcMaxU64 < (calldataWord cd 4).toNat)
    (hsize : cd.size < UInt256.size)
    (hsizeSign : ¬ cd.size < 2 ^ 255) :
    UInt256.slt ((((⟨4⟩ : UInt256) + calldataWord cd 4) + ⟨31⟩))
        (UInt256.ofNat cd.size) = ⟨0⟩ := by
  have hoffLeMax : (calldataWord cd 4).toNat ≤ ABI.solcMaxU64 :=
    Nat.le_of_not_gt hoffMax
  apply slt_zero_low_high
  · rw [calldataStartPlus31_toNat cd hoffMax]
    norm_num [ABI.solcMaxU64] at hoffLeMax ⊢
    omega
  · rw [ulit_toNat' cd.size hsize]
    omega

theorem calldataPayloadStart_toNat
    (cd : ByteArray)
    (hoffMax : ¬ ABI.solcMaxU64 < (calldataWord cd 4).toNat) :
    (((⟨4⟩ : UInt256) + calldataWord cd 4) + ⟨32⟩).toNat =
      4 + (calldataWord cd 4).toNat + 32 := by
  have hoffLeMax : (calldataWord cd 4).toNat ≤ 18446744073709551615 := by
    simpa [ABI.solcMaxU64] using Nat.le_of_not_gt hoffMax
  have hoffSmall : (calldataWord cd 4).toNat < 2 ^ 255 := by
    omega
  have hoffSize : (calldataWord cd 4).toNat < UInt256.size :=
    (calldataWord cd 4).val.isLt
  have hoffOfNat :
      (UInt256.ofNat (calldataWord cd 4).toNat).toNat =
        (calldataWord cd 4).toNat :=
    ulit_toNat' _ hoffSize
  rw [← u256_ofNat_toNat (calldataWord cd 4)]
  simpa [hoffOfNat] using (uadd3_ofNat_toNat (a := 4)
    (b := (calldataWord cd 4).toNat)
    (c := 32)
    (by norm_num [UInt256.size])
    (lt_size_of_lt_sign hoffSmall)
    (by norm_num [UInt256.size])
    (lt_size_of_lt_sign (by omega : 4 + (calldataWord cd 4).toNat < 2 ^ 255))
    (lt_size_of_lt_sign (by omega :
      4 + (calldataWord cd 4).toNat + 32 < 2 ^ 255)))

theorem calldataLengthMaxWord_zero
    (cd : ByteArray)
    (hlenZero :
      uInt256OfByteArray
        (cd.readBytes ((((⟨4⟩ : UInt256) + calldataWord cd 4)).toNat) 32) = ⟨0⟩) :
    UInt256.gt
        (uInt256OfByteArray
          (cd.readBytes
            ((((⟨4⟩ : UInt256) + calldataWord cd 4)).toNat) 32))
        ⟨18446744073709551615⟩ = ⟨0⟩ := by
  rw [hlenZero]
  decide

theorem calldataPayloadWord_zero
    (cd : ByteArray)
    (hsize : cd.size < UInt256.size)
    (hoffMax : ¬ ABI.solcMaxU64 < (calldataWord cd 4).toNat)
    (hlenWord : 4 + (calldataWord cd 4).toNat + 32 ≤ cd.size)
    (hlenZero :
      uInt256OfByteArray
        (cd.readBytes ((((⟨4⟩ : UInt256) + calldataWord cd 4)).toNat) 32) = ⟨0⟩) :
    UInt256.gt
      (((((⟨4⟩ : UInt256) + calldataWord cd 4) + ⟨32⟩) +
        UInt256.mul
          (uInt256OfByteArray
            (cd.readBytes
              ((((⟨4⟩ : UInt256) + calldataWord cd 4)).toNat) 32)) ⟨1⟩))
      (UInt256.ofNat cd.size) = ⟨0⟩ := by
  have hmul :
      UInt256.mul
          (uInt256OfByteArray
            (cd.readBytes
              ((((⟨4⟩ : UInt256) + calldataWord cd 4)).toNat) 32)) ⟨1⟩ =
        ⟨0⟩ := by
    rw [hlenZero]
    decide
  apply ugt_zero
  rw [hmul]
  rw [setAddZero_toNat]
  rw [calldataPayloadStart_toNat cd hoffMax]
  rw [ulit_toNat' cd.size hsize]
  exact hlenWord

theorem calldataPayloadShort_size_lt
    (cd : ByteArray)
    (hlenWord : 4 + (calldataWord cd 4).toNat + 32 ≤ cd.size)
    (hpayloadList :
      ((((cd.toList.drop 4).drop ((calldataWord cd 4).toNat + 32)).take
        (calldataWord cd (4 + (calldataWord cd 4).toNat)).toNat).length ≠
        (calldataWord cd (4 + (calldataWord cd 4).toNat)).toNat)) :
    cd.size < 4 + (calldataWord cd 4).toNat + 32 +
      (calldataWord cd (4 + (calldataWord cd 4).toNat)).toNat := by
  let off := (calldataWord cd 4).toNat
  let n := (calldataWord cd (4 + (calldataWord cd 4).toNat)).toNat
  have htlen : cd.toList.length = cd.size := by
    rw [byteArray_toList_eq, Array.length_toList]; rfl
  have hdropLen :
      ((cd.toList.drop 4).drop (off + 32)).length =
        cd.size - (4 + (off + 32)) := by
    rw [List.drop_drop, List.length_drop, htlen]
  have htakeLen :
      (((cd.toList.drop 4).drop (off + 32)).take n).length =
        min n (cd.size - (4 + (off + 32))) := by
    rw [List.length_take, hdropLen]
  have hltRemain : cd.size - (4 + (off + 32)) < n := by
    by_contra hnot
    have hge : n ≤ cd.size - (4 + (off + 32)) := Nat.le_of_not_gt hnot
    apply hpayloadList
    have : (((cd.toList.drop 4).drop (off + 32)).take n).length = n := by
      rw [htakeLen, min_eq_left hge]
    simpa [off, n] using this
  omega

theorem calldataPayloadStartLen_le_of_payload
    (cd : ByteArray)
    (hlenWord : 4 + (calldataWord cd 4).toNat + 32 ≤ cd.size)
    (hpayload :
      ((((cd.toList.drop 4).drop ((calldataWord cd 4).toNat + 32)).take
        (calldataWord cd (4 + (calldataWord cd 4).toNat)).toNat).length =
        (calldataWord cd (4 + (calldataWord cd 4).toNat)).toNat)) :
    4 + (calldataWord cd 4).toNat + 32 +
      (calldataWord cd (4 + (calldataWord cd 4).toNat)).toNat ≤ cd.size := by
  let off := (calldataWord cd 4).toNat
  let n := (calldataWord cd (4 + (calldataWord cd 4).toNat)).toNat
  have htlen : cd.toList.length = cd.size := by
    rw [byteArray_toList_eq, Array.length_toList]; rfl
  have hdropLen :
      ((cd.toList.drop 4).drop (off + 32)).length =
        cd.size - (4 + (off + 32)) := by
    rw [List.drop_drop, List.length_drop, htlen]
  have htakeLen :
      (((cd.toList.drop 4).drop (off + 32)).take n).length =
        min n (cd.size - (4 + (off + 32))) := by
    rw [List.length_take, hdropLen]
  have hnle : n ≤ cd.size - (4 + (off + 32)) := by
    by_contra hnot
    have hlt : cd.size - (4 + (off + 32)) < n := Nat.lt_of_not_ge hnot
    have hmin : min n (cd.size - (4 + (off + 32))) = cd.size - (4 + (off + 32)) :=
      min_eq_right (le_of_lt hlt)
    have hpayload' :
        (((cd.toList.drop 4).drop (off + 32)).take n).length = n := by
      simpa [off, n] using hpayload
    rw [htakeLen, hmin] at hpayload'
    omega
  omega

theorem calldataPayloadWord_zero_of_payload
    (cd : ByteArray)
    (hsize : cd.size < UInt256.size)
    (hoffMax : ¬ ABI.solcMaxU64 < (calldataWord cd 4).toNat)
    (hlenWord : 4 + (calldataWord cd 4).toNat + 32 ≤ cd.size)
    (hlenMax :
      ¬ ABI.solcMaxU64 <
        (calldataWord cd (4 + (calldataWord cd 4).toNat)).toNat)
    (hpayload :
      ((((cd.toList.drop 4).drop ((calldataWord cd 4).toNat + 32)).take
        (calldataWord cd (4 + (calldataWord cd 4).toNat)).toNat).length =
        (calldataWord cd (4 + (calldataWord cd 4).toNat)).toNat)) :
    UInt256.gt
      (((((⟨4⟩ : UInt256) + calldataWord cd 4) + ⟨32⟩) +
        UInt256.mul
          (uInt256OfByteArray
            (cd.readBytes
              ((((⟨4⟩ : UInt256) + calldataWord cd 4)).toNat) 32)) ⟨1⟩))
      (UInt256.ofNat cd.size) = ⟨0⟩ := by
  let off := (calldataWord cd 4).toNat
  let n := (calldataWord cd (4 + (calldataWord cd 4).toNat)).toNat
  have hpayloadLe :
      4 + off + 32 + n ≤ cd.size := by
    simpa [off, n, Nat.add_assoc] using
      calldataPayloadStartLen_le_of_payload cd hlenWord hpayload
  have hnLeMax : n ≤ ABI.solcMaxU64 := by
    simpa [n] using Nat.le_of_not_gt hlenMax
  have hmulToNat :
      (UInt256.mul
          (uInt256OfByteArray
            (cd.readBytes
              ((((⟨4⟩ : UInt256) + calldataWord cd 4)).toNat) 32)) ⟨1⟩).toNat = n := by
    rw [calldataLengthWord_eq_abi cd hoffMax]
    rw [u256_mul_toNat]
    rw [show (⟨1⟩ : UInt256).toNat = 1 from by decide]
    rw [Nat.mul_one]
    exact Nat.mod_eq_of_lt (by
      have hmax : ABI.solcMaxU64 < UInt256.size := by
        norm_num [ABI.solcMaxU64, UInt256.size]
      exact lt_of_le_of_lt hnLeMax hmax)
  have hpayloadEndToNat :
      (((((⟨4⟩ : UInt256) + calldataWord cd 4) + ⟨32⟩) +
        UInt256.mul
          (uInt256OfByteArray
            (cd.readBytes
              ((((⟨4⟩ : UInt256) + calldataWord cd 4)).toNat) 32)) ⟨1⟩)).toNat =
        4 + off + 32 + n := by
    rw [uadd_toNat]
    rw [calldataPayloadStart_toNat cd hoffMax]
    rw [hmulToNat]
    exact Nat.mod_eq_of_lt (lt_of_le_of_lt hpayloadLe hsize)
  apply ugt_zero
  rw [hpayloadEndToNat, ulit_toNat' cd.size hsize]
  exact hpayloadLe

theorem calldataPayloadWord_one_of_payload_short
    (cd : ByteArray)
    (hsize : cd.size < UInt256.size)
    (hoffMax : ¬ ABI.solcMaxU64 < (calldataWord cd 4).toNat)
    (hlenWord : 4 + (calldataWord cd 4).toNat + 32 ≤ cd.size)
    (hlenMax :
      ¬ ABI.solcMaxU64 <
        (calldataWord cd (4 + (calldataWord cd 4).toNat)).toNat)
    (hpayloadList :
      ((((cd.toList.drop 4).drop ((calldataWord cd 4).toNat + 32)).take
        (calldataWord cd (4 + (calldataWord cd 4).toNat)).toNat).length ≠
        (calldataWord cd (4 + (calldataWord cd 4).toNat)).toNat)) :
    UInt256.gt
      (((((⟨4⟩ : UInt256) + calldataWord cd 4) + ⟨32⟩) +
        UInt256.mul
          (uInt256OfByteArray
            (cd.readBytes
              ((((⟨4⟩ : UInt256) + calldataWord cd 4)).toNat) 32)) ⟨1⟩))
      (UInt256.ofNat cd.size) = ⟨1⟩ := by
  let off := (calldataWord cd 4).toNat
  let n := (calldataWord cd (4 + (calldataWord cd 4).toNat)).toNat
  have hpayloadShortNat :
      cd.size < 4 + off + 32 + n := by
    simpa [off, n, Nat.add_assoc] using
      calldataPayloadShort_size_lt cd hlenWord hpayloadList
  have hoffLeMax : off ≤ ABI.solcMaxU64 := by
    simpa [off] using Nat.le_of_not_gt hoffMax
  have hnLeMax : n ≤ ABI.solcMaxU64 := by
    simpa [n] using Nat.le_of_not_gt hlenMax
  have hmulToNat :
      (UInt256.mul
          (uInt256OfByteArray
            (cd.readBytes
              ((((⟨4⟩ : UInt256) + calldataWord cd 4)).toNat) 32)) ⟨1⟩).toNat = n := by
    rw [calldataLengthWord_eq_abi cd hoffMax]
    rw [u256_mul_toNat]
    rw [show (⟨1⟩ : UInt256).toNat = 1 from by decide]
    rw [Nat.mul_one]
    exact Nat.mod_eq_of_lt (by
      have hmax : ABI.solcMaxU64 < UInt256.size := by
        norm_num [ABI.solcMaxU64, UInt256.size]
      exact lt_of_le_of_lt hnLeMax hmax)
  have hpayloadEndToNat :
      (((((⟨4⟩ : UInt256) + calldataWord cd 4) + ⟨32⟩) +
        UInt256.mul
          (uInt256OfByteArray
            (cd.readBytes
              ((((⟨4⟩ : UInt256) + calldataWord cd 4)).toNat) 32)) ⟨1⟩)).toNat =
        4 + off + 32 + n := by
    rw [uadd_toNat]
    rw [calldataPayloadStart_toNat cd hoffMax]
    rw [hmulToNat]
    exact Nat.mod_eq_of_lt (by
      apply lt_size_of_lt_sign
      norm_num [ABI.solcMaxU64] at hoffLeMax hnLeMax ⊢
      omega)
  apply ugt_one
  rw [hpayloadEndToNat, ulit_toNat' cd.size hsize]
  exact hpayloadShortNat

theorem calldataLengthMaxWord_of_abi
    (cd : ByteArray)
    (hoffMax : ¬ ABI.solcMaxU64 < (calldataWord cd 4).toNat)
    (hlenMax :
      ¬ ABI.solcMaxU64 <
        (calldataWord cd (4 + (calldataWord cd 4).toNat)).toNat) :
    UInt256.gt
        (uInt256OfByteArray
          (cd.readBytes
            ((((⟨4⟩ : UInt256) + calldataWord cd 4)).toNat) 32))
        ⟨18446744073709551615⟩ = ⟨0⟩ := by
  rw [calldataLengthWord_eq_abi cd hoffMax]
  apply ugt_zero
  rw [show (⟨18446744073709551615⟩ : UInt256).toNat = ABI.solcMaxU64 by decide]
  exact Nat.le_of_not_gt hlenMax

theorem calldataLengthMaxWord_one_of_abi
    (cd : ByteArray)
    (hoffMax : ¬ ABI.solcMaxU64 < (calldataWord cd 4).toNat)
    (hlenHuge :
      ABI.solcMaxU64 <
        (calldataWord cd (4 + (calldataWord cd 4).toNat)).toNat) :
    UInt256.gt
        (uInt256OfByteArray
          (cd.readBytes
            ((((⟨4⟩ : UInt256) + calldataWord cd 4)).toNat) 32))
        ⟨18446744073709551615⟩ = ⟨1⟩ := by
  rw [calldataLengthWord_eq_abi cd hoffMax]
  apply ugt_one
  rw [show (⟨18446744073709551615⟩ : UInt256).toNat = ABI.solcMaxU64 by decide]
  exact hlenHuge

theorem recoveredAddress_masked {o : ByteArray}
    (ho32 : 32 ≤ o.size) :
    (.address (AccountAddress.ofNat (fromByteArrayBigEndian (o.extract 0 32))) : Value) =
      .address (AccountAddress.ofNat
        (UInt256.land (UInt256.ofNat (fromByteArrayBigEndian (o.extract 0 32)))
          solcAddrMask).toNat) := by
  let recovered := fromByteArrayBigEndian (o.extract 0 32)
  have hrecoveredLt : recovered < UInt256.size :=
    fromByteArrayBigEndian_extract0_32_lt ho32
  calc
    (.address (AccountAddress.ofNat recovered) : Value)
        = .address (AccountAddress.ofNat (UInt256.ofNat recovered).toNat) := by
          rw [UInt256.toNat_ofNat_of_lt hrecoveredLt]
    _ = .address (AccountAddress.ofNat
          (UInt256.land solcAddrMask (UInt256.ofNat recovered)).toNat) := by
          exact solcAddressValue_masked (UInt256.ofNat recovered)
    _ = .address (AccountAddress.ofNat
          (UInt256.land (UInt256.ofNat recovered) solcAddrMask).toNat) := by
          rw [u256_land_comm solcAddrMask (UInt256.ofNat recovered)]

theorem recoveredAddress_ne_zero_of_mask_ne_zero {o : ByteArray}
    (ho32 : 32 ≤ o.size)
    (hnz :
      UInt256.land (UInt256.ofNat (fromByteArrayBigEndian (o.extract 0 32))) solcAddrMask ≠
        ⟨0⟩) :
    (.address (AccountAddress.ofNat (fromByteArrayBigEndian (o.extract 0 32))) : Value) ≠
      .address (AccountAddress.ofNat 0) := by
  let recovered := fromByteArrayBigEndian (o.extract 0 32)
  have hrecoveredLt : recovered < UInt256.size :=
    fromByteArrayBigEndian_extract0_32_lt ho32
  have hmasked :
      (.address (AccountAddress.ofNat recovered) : Value) =
        .address (AccountAddress.ofNat
          (UInt256.land solcAddrMask (UInt256.ofNat recovered)).toNat) := by
    calc
      (.address (AccountAddress.ofNat recovered) : Value)
          = .address (AccountAddress.ofNat (UInt256.ofNat recovered).toNat) := by
            rw [UInt256.toNat_ofNat_of_lt hrecoveredLt]
      _ = .address (AccountAddress.ofNat
            (UInt256.land solcAddrMask (UInt256.ofNat recovered)).toNat) := by
            exact solcAddressValue_masked (UInt256.ofNat recovered)
  intro hzero
  apply hnz
  have hmaskedZero :
      (.address (AccountAddress.ofNat
          (UInt256.land solcAddrMask (UInt256.ofNat recovered)).toNat) : Value) =
        .address (AccountAddress.ofNat 0) := by
    rw [← hmasked]
    exact hzero
  injection hmaskedZero with haddr
  apply u256_inj
  have hcanon :
      (UInt256.land (UInt256.ofNat recovered) solcAddrMask).toNat < AccountAddress.size := by
    simpa [AccountAddress.size, EVM.addressModulus] using
      solcAddrMask_result_canonical (UInt256.ofNat recovered)
  have hval := congrArg Fin.val haddr
  unfold AccountAddress.ofNat at hval
  simp only [Fin.val_ofNat] at hval
  rw [u256_land_comm solcAddrMask (UInt256.ofNat recovered)] at hval
  rw [Nat.mod_eq_of_lt hcanon] at hval
  simpa using hval

theorem recoveredAddress_eq_zero_of_mask_eq_zero {o : ByteArray}
    (ho32 : 32 ≤ o.size)
    (hzero :
      UInt256.land (UInt256.ofNat (fromByteArrayBigEndian (o.extract 0 32))) solcAddrMask =
        ⟨0⟩) :
    (.address (AccountAddress.ofNat (fromByteArrayBigEndian (o.extract 0 32))) : Value) =
      .address (AccountAddress.ofNat 0) := by
  calc
    (.address (AccountAddress.ofNat (fromByteArrayBigEndian (o.extract 0 32))) : Value)
        = .address (AccountAddress.ofNat
            (UInt256.land (UInt256.ofNat (fromByteArrayBigEndian (o.extract 0 32)))
              solcAddrMask).toNat) := recoveredAddress_masked ho32
    _ = .address (AccountAddress.ofNat 0) := by
          rw [hzero]
          simp

theorem recoveredPaddedAddress_masked {o : ByteArray} :
    (.address (AccountAddress.ofNat (fromByteArrayBigEndian (o.readWithPadding 0 32))) :
        Value) =
      .address (AccountAddress.ofNat
        (UInt256.land (UInt256.ofNat (fromByteArrayBigEndian (o.readWithPadding 0 32)))
          solcAddrMask).toNat) := by
  let recovered := fromByteArrayBigEndian (o.readWithPadding 0 32)
  have hrecoveredLt : recovered < UInt256.size :=
    fromByteArrayBigEndian_readWithPadding0_32_lt o
  calc
    (.address (AccountAddress.ofNat recovered) : Value)
        = .address (AccountAddress.ofNat (UInt256.ofNat recovered).toNat) := by
          rw [UInt256.toNat_ofNat_of_lt hrecoveredLt]
    _ = .address (AccountAddress.ofNat
          (UInt256.land solcAddrMask (UInt256.ofNat recovered)).toNat) := by
          exact solcAddressValue_masked (UInt256.ofNat recovered)
    _ = .address (AccountAddress.ofNat
          (UInt256.land (UInt256.ofNat recovered) solcAddrMask).toNat) := by
          rw [u256_land_comm solcAddrMask (UInt256.ofNat recovered)]

theorem recoveredPaddedAddress_ne_zero_of_mask_ne_zero {o : ByteArray}
    (hnz :
      UInt256.land (UInt256.ofNat (fromByteArrayBigEndian (o.readWithPadding 0 32)))
          solcAddrMask ≠
        ⟨0⟩) :
    (.address (AccountAddress.ofNat (fromByteArrayBigEndian (o.readWithPadding 0 32))) :
        Value) ≠
      .address (AccountAddress.ofNat 0) := by
  let recovered := fromByteArrayBigEndian (o.readWithPadding 0 32)
  have hrecoveredLt : recovered < UInt256.size :=
    fromByteArrayBigEndian_readWithPadding0_32_lt o
  have hmasked :
      (.address (AccountAddress.ofNat recovered) : Value) =
        .address (AccountAddress.ofNat
          (UInt256.land solcAddrMask (UInt256.ofNat recovered)).toNat) := by
    calc
      (.address (AccountAddress.ofNat recovered) : Value)
          = .address (AccountAddress.ofNat (UInt256.ofNat recovered).toNat) := by
            rw [UInt256.toNat_ofNat_of_lt hrecoveredLt]
      _ = .address (AccountAddress.ofNat
            (UInt256.land solcAddrMask (UInt256.ofNat recovered)).toNat) := by
            exact solcAddressValue_masked (UInt256.ofNat recovered)
  intro hzero
  apply hnz
  have hmaskedZero :
      (.address (AccountAddress.ofNat
          (UInt256.land solcAddrMask (UInt256.ofNat recovered)).toNat) : Value) =
        .address (AccountAddress.ofNat 0) := by
    rw [← hmasked]
    exact hzero
  injection hmaskedZero with haddr
  apply u256_inj
  have hcanon :
      (UInt256.land (UInt256.ofNat recovered) solcAddrMask).toNat < AccountAddress.size := by
    simpa [AccountAddress.size, EVM.addressModulus] using
      solcAddrMask_result_canonical (UInt256.ofNat recovered)
  have hval := congrArg Fin.val haddr
  unfold AccountAddress.ofNat at hval
  simp only [Fin.val_ofNat] at hval
  rw [u256_land_comm solcAddrMask (UInt256.ofNat recovered)] at hval
  rw [Nat.mod_eq_of_lt hcanon] at hval
  simpa using hval

theorem recoveredPaddedAddress_eq_zero_of_mask_eq_zero {o : ByteArray}
    (hzero :
      UInt256.land (UInt256.ofNat (fromByteArrayBigEndian (o.readWithPadding 0 32)))
          solcAddrMask =
        ⟨0⟩) :
    (.address (AccountAddress.ofNat (fromByteArrayBigEndian (o.readWithPadding 0 32))) :
        Value) =
      .address (AccountAddress.ofNat 0) := by
  calc
    (.address (AccountAddress.ofNat (fromByteArrayBigEndian (o.readWithPadding 0 32))) :
        Value)
        = .address (AccountAddress.ofNat
            (UInt256.land (UInt256.ofNat (fromByteArrayBigEndian (o.readWithPadding 0 32)))
              solcAddrMask).toNat) := recoveredPaddedAddress_masked
    _ = .address (AccountAddress.ofNat 0) := by
          rw [hzero]
          simp

theorem digestPrefix_toList :
    (ByteArray.mk #[0x19, 0x01]).toList = [0x19, 0x01] := by
  decide +kernel

/-- `decodeABIValues?` for the `(abiBytes32, address)` head tuple under `legacySolc05`.
The legacy solc-0.5 decoder does not enforce the address canonical-form check, so `_hcanon` is
retained only for interface parity with the `modern` lemma. -/
theorem decodeABIValues_bytes32_address_legacy {bytes : List UInt8}
    (hlen0 : (bytes.take 32).length = 32)
    (hlen32 : ((bytes.drop 32).take 32).length = 32)
    (_hcanon : (ABI.bytesToWord ((bytes.drop 32).take 32)).toNat < EVM.addressModulus) :
    decodeABIValues? [abiBytes32, .elem .address] bytes 0 0 64 64 DecodeMode.legacySolc05 =
      some ([.fixedBytes abiBytes32Width (bytes.take 32),
        .address (Ethereum.AccountAddress.ofNat
          (ABI.bytesToWord ((bytes.drop 32).take 32)).toNat)], 64) := by
  simp [decodeABIValues?, abiBytes32, abiBytes32Width, isDynamicABIType,
    staticABIEncodedSize?, decodeABIValue?, readBytes?, hlen0]
  simp [readWord?, readBytes?, decodeABIWord?, hlen32, UInt256.toNat]

theorem biteIlkBytes_len_min {I : ExecutionEnv} (hsz36 : 36 ≤ I.calldata.size) :
    min 32 (I.calldata.toList.length - 4) = abiBytes32Width.val + 1 := by
  have htlen : I.calldata.toList.length = I.calldata.size := by
    rw [byteArray_toList_eq, Array.length_toList]; rfl
  rw [htlen]; simp [abiBytes32Width]; omega

theorem encodeABIValue_bool (b : Bool) :
    encodeABIValue? (.elem .bool) (.bool b) =
      some (EVM.Word.toBytesBE b.toUInt256) := by
  cases b <;> simp [encodeABIValue?, encodeABIWord?, Bool.toUInt256]

theorem encodeABIValue_addr_masked (w : UInt256) :
    encodeABIValue? abiAddress
      (.address (AccountAddress.ofNat (UInt256.land w solcAddrMask).toNat)) =
      some (EVM.Word.toBytesBE (UInt256.land w solcAddrMask)) := by
  have hcanon := solcAddrMask_result_canonical w
  have haddrMod : (UInt256.land w solcAddrMask).toNat % AccountAddress.size =
      (UInt256.land w solcAddrMask).toNat := by
    apply Nat.mod_eq_of_lt
    simpa [EVM.addressModulus, EVM.twoPow, AccountAddress.size] using hcanon
  have hword : EVM.word (UInt256.land w solcAddrMask).toNat = UInt256.land w solcAddrMask := by
    exact u256_ofNat_toNat _
  simp [abiAddress, encodeABIValue?, encodeABIWord?, AccountAddress.ofNat, haddrMod, hword]

theorem encodePacked_bytes32_of_length {bytes : List UInt8}
    (hlen : bytes.length = fixedBytesSize abiBytes32Width) :
    encodePackedValue? abiBytes32 (.fixedBytes abiBytes32Width bytes) = some bytes := by
  simp [encodePackedValue?, abiBytes32, abiBytes32Width, fixedBytesSize, hlen]

theorem encodePacked_uint256' (value : UInt256) :
    encodePackedValue? abiUInt256 (.int (Int.ofNat value.toNat)) =
      some (EVM.Word.toBytesBE value) := by
  have hword : EVM.word value.toNat = value := u256_ofNat_toNat value
  have hlt : value.toNat < EVM.twoPow 256 := by
    change value.val.val < EVM.twoPow 256
    exact value.val.isLt
  simp [encodePackedValue?, abiUInt256, abiUInt256Int, encodeABIWord?, hword, hlt]

theorem decodeABIValue_legacy_bytes32_ok {bytes : List UInt8} {start : Nat}
    (hlen : ((bytes.drop start).take 32).length = 32) :
    decodeABIValue? (ABIType.elem (ElemType.bytes abiBytes32Width)) bytes start
        DecodeMode.legacySolc05 =
      some (.fixedBytes abiBytes32Width ((bytes.drop start).take 32), start + 32) := by
  simp only [abiBytes32Width, decodeABIValue?, readBytes?, bind, Option.bind]
  rw [if_pos hlen]
  have htake : List.take 32 ((bytes.drop start).take 32) = (bytes.drop start).take 32 :=
    List.take_of_length_le (by rw [hlen])
  simp [htake]

theorem barkAddressArgEncodingMasked (w : UInt256)
    (hcanon : w.toNat < EVM.addressModulus) :
    ABI.encodeABIValue? (.elem .address) (.address (AccountAddress.ofUInt256 w)) =
      some (EVM.Word.toBytesBE w) := by
  simp [ABI.encodeABIValue?, ABI.encodeABIWord?, barkAddressWord_ofUInt256_masked w hcanon]

theorem valueToWord_ctorIlk (ilk : UInt256) :
    valueToWord (.fixedBytes abiBytes32Width (EVM.Word.toBytesBE ilk)) = some ilk := by
  have hlen : (EVM.Word.toBytesBE ilk).length = 32 := by
    simpa using word_toBytesBE_toByteArray_size ilk
  have hword : EVM.Word.ofNat (fromBytesBigEndian (EVM.Word.toBytesBE ilk)) = ilk := by
    apply u256_inj
    have hfrom : fromBytesBigEndian (EVM.Word.toBytesBE ilk) = ilk.toNat := by
      have h := congrArg fromByteArrayBigEndian (word_toBytesBE_toByteArray_eq_toByteArray ilk)
      simpa [fromByteArrayBigEndian, byteArray_toList_eq] using
        h.trans (fromByteArrayBigEndian_toByteArray ilk)
    rw [EVM.Word.ofNat, hfrom]
    exact Nat.mod_eq_of_lt ilk.val.isLt
  simp [valueToWord, abiBytes32Width, hlen, hword]

theorem decodeABIValues_legacy_ok {bytes : List UInt8}
    (hlen0 : (bytes.take 32).length = 32)
    (hlen32 : ((bytes.drop 32).take 32).length = 32) :
    decodeABIValues? [abiBytes32, abiBool] bytes 0 0 64 64 DecodeMode.legacySolc05 =
      some ([.fixedBytes abiBytes32Width (bytes.take 32),
        .bool (ABI.bytesToWord ((bytes.drop 32).take 32) ≠ ⟨0⟩)], 64) := by
  have hbytes0 : decodeABIValue? abiBytes32 bytes 0 DecodeMode.legacySolc05 =
      some (.fixedBytes abiBytes32Width (bytes.take 32), 32) := by
    simp [decodeABIValue?, abiBytes32, abiBytes32Width, readBytes?, hlen0]
  by_cases hhas : ABI.bytesToWord ((bytes.drop 32).take 32) = ⟨0⟩
  · have hbool : decodeABIValue? abiBool bytes 32 DecodeMode.legacySolc05 =
        some (.bool false, 64) := by
      rw [decodeABIValue_scalarWordWithMode_eq (mode := DecodeMode.legacySolc05)
        (ty := abiBool) (bytes := bytes) (start := 32) (by decide)]
      exact decodeScalarWordWithMode_legacy_bool_false (bytes := bytes) (start := 32)
        hlen32 hhas
    simp only [decodeABIValues?, abiBytes32, abiBytes32Width, abiBool, isDynamicABIType,
      Bool.false_eq_true,
      if_false, staticABIEncodedSize?, bind, Option.bind, Nat.zero_add]
    simp only [abiBytes32, abiBytes32Width] at hbytes0
    simp only [abiBool] at hbool
    rw [hbytes0, hbool]
    simp [hhas]
  · have hbool : decodeABIValue? abiBool bytes 32 DecodeMode.legacySolc05 =
        some (.bool true, 64) := by
      rw [decodeABIValue_scalarWordWithMode_eq (mode := DecodeMode.legacySolc05)
        (ty := abiBool) (bytes := bytes) (start := 32) (by decide)]
      exact decodeScalarWordWithMode_legacy_bool_true (bytes := bytes) (start := 32)
        hlen32 hhas
    simp only [decodeABIValues?, abiBytes32, abiBytes32Width, abiBool, isDynamicABIType,
      Bool.false_eq_true,
      if_false, staticABIEncodedSize?, bind, Option.bind, Nat.zero_add]
    simp only [abiBytes32, abiBytes32Width] at hbytes0
    simp only [abiBool] at hbool
    rw [hbytes0, hbool]
    simp [hhas]

theorem forkIlkBytes_len (I : ExecutionEnv) (hsz164 : 164 ≤ I.calldata.size) :
    ((I.calldata.toList.drop 4).take 32).length = ↑abiBytes32Width + 1 := by
  have htlen : I.calldata.toList.length = I.calldata.size := by
    rw [byteArray_toList_eq, Array.length_toList]
    rfl
  rw [List.length_take, List.length_drop, htlen]
  simp [abiBytes32Width]
  omega

theorem frobIBytes_len (I : ExecutionEnv) (hsz196 : 196 ≤ I.calldata.size) :
    ((I.calldata.toList.drop 4).take 32).length = ↑abiBytes32Width + 1 := by
  have htlen : I.calldata.toList.length = I.calldata.size := by
    rw [byteArray_toList_eq, Array.length_toList]
    rfl
  rw [List.length_take, List.length_drop, htlen]
  simp [abiBytes32Width]
  omega

theorem initIlkBytes_length {I : ExecutionEnv} (hsz36 : 36 ≤ I.calldata.size) :
    ((I.calldata.toList.drop 4).take 32).length = ↑abiBytes32Width + 1 := by
  rw [List.length_take, List.length_drop]
  have htlen : I.calldata.toList.length = I.calldata.size := by
    rw [byteArray_toList_eq, Array.length_toList]
    rfl
  rw [htlen]
  simp [abiBytes32Width]
  omega

/-- Every successful ABI encoding of a `abiBytes32` value is exactly one 32-byte word. -/
theorem encodeABIValue_bytes32_length {v : Value} {bs : List UInt8}
    (h : ABI.encodeABIValue? abiBytes32 v = some bs) : bs.length = 32 := by
  cases v <;> simp [abiBytes32, abiBytes32Width, ABI.encodeABIValue?, ABI.encodeABIWord?] at h
  case fixedBytes n bytes =>
    rcases h with ⟨⟨rfl, hlen⟩, hbs⟩
    subst bs
    simp [ABI.zeroBytes, hlen]

/-- A successful ABI encoding of a `abiBytes32[]` element tail has one 32-byte word per element. -/
theorem encodeABIStaticArrayElems_bytes32_length {vs : List Value} {elemBytes : List UInt8}
    (h : ABI.encodeABIStaticArrayElems? abiBytes32 vs = some elemBytes) :
    elemBytes.length = 32 * vs.length := by
  induction vs generalizing elemBytes with
  | nil =>
      simp [ABI.encodeABIStaticArrayElems?] at h
      subst elemBytes
      simp
  | cons v rest ih =>
      simp [ABI.encodeABIStaticArrayElems?] at h
      rcases hv : ABI.encodeABIValue? abiBytes32 v with _ | enc <;> simp [hv] at h
      rcases hr : ABI.encodeABIStaticArrayElems? abiBytes32 rest with _ | encRest <;>
        simp [hr] at h
      subst elemBytes
      have henc := encodeABIValue_bytes32_length (v := v) (bs := enc) hv
      have hrest := ih hr
      simp [henc, hrest]
      omega

theorem encodePacked_bytes32' (secret : UInt256) :
    encodePackedValue? abiBytes32
      (.fixedBytes ⟨31, by decide⟩ (EVM.Word.toBytesBE secret)) =
        some (EVM.Word.toBytesBE secret) := by
  have hlen := word_toBytesBE_length_32 secret
  simp [encodePackedValue?, abiBytes32, abiBytes32Width, fixedBytesSize, hlen]

theorem valueToKey_bytes32_of_length {bs : List UInt8}
    (hlen : bs.length = 32) :
    valueToKey? (.fixedBytes abiBytes32Width bs) = some (.fixedBytes abiBytes32Width bs) := by
  simpa [valueToKey?, abiBytes32Width, hlen]

theorem valueToKey_bytes32_toBytesBE (w : UInt256) :
    valueToKey? (.fixedBytes abiBytes32Width (EVM.Word.toBytesBE w)) =
      some (.fixedBytes abiBytes32Width (EVM.Word.toBytesBE w)) := by
  have hlen : (EVM.Word.toBytesBE w).length = 32 := by
    simpa using word_toBytesBE_toByteArray_size w
  exact valueToKey_bytes32_of_length hlen

theorem valueToKey_address (a : AccountAddress) :
    valueToKey? (.address a) = some (.address a) := by
  rfl

theorem listUInt8_decide_eq_beq (xs ys : List UInt8) :
    decide (xs = ys) = (xs == ys) := by
  by_cases h : xs = ys
  · subst ys
    simp
  · have hb : (xs == ys) = false := by
      exact beq_eq_false_iff_ne.mpr h
    simp [h, hb]

theorem fromBytes'_zero_iff_all_zero (xs : List UInt8) :
    fromBytes' xs = 0 ↔ xs.all (· == 0) = true := by
  induction xs with
  | nil => simp [fromBytes']
  | cons x xs ih =>
      constructor
      · intro h
        simp only [List.all_cons, Bool.and_eq_true]
        unfold fromBytes' at h
        have hxnat : x.toNat = 0 := (Nat.add_eq_zero_iff.mp h).1
        have htail : fromBytes' xs = 0 := by
          have hprod : UInt8.size * fromBytes' xs = 0 := (Nat.add_eq_zero_iff.mp h).2
          have hsize : 0 < UInt8.size := by decide
          omega
        have hx : x = 0 := UInt8.toNat_inj.mp hxnat
        exact ⟨by simpa [hx], ih.mp htail⟩
      · intro h
        simp only [List.all_cons, Bool.and_eq_true] at h
        rcases h with ⟨hx, hxs⟩
        have hx0 : x = 0 := eq_of_beq hx
        unfold fromBytes'
        simp [hx0, ih.mpr hxs]

theorem fromBytesBigEndian_zero_iff_all_zero (xs : List UInt8) :
    fromBytesBigEndian xs = 0 ↔ xs.all (· == 0) = true := by
  unfold fromBytesBigEndian Function.comp
  rw [fromBytes'_zero_iff_all_zero]
  simp

theorem bytesToWord_toNat_of_len (xs : List UInt8) (hlen : xs.length = 32) :
    (ABI.bytesToWord xs).toNat = fromBytesBigEndian xs := by
  unfold ABI.bytesToWord fromByteArrayBigEndian
  rw [ulit_toNat']
  · simp [byteArray_toList_eq]
  · change fromByteArrayBigEndian { data := xs.toArray } < UInt256.size
    unfold fromByteArrayBigEndian
    simp [byteArray_toList_eq]
    rw [show UInt256.size = 2 ^ (8 * xs.length) by rw [hlen]; rfl]
    exact fromBytesBigEndian_bound xs

theorem list_drop_take_full_chunk_succ (xs : List UInt8) (i fuel : Nat) :
    (xs.drop (32 * i)).take (32 * (fuel + 1)) =
      (xs.drop (32 * i)).take 32 ++
        (xs.drop (32 * (i + 1))).take (32 * fuel) := by
  rw [show 32 * (fuel + 1) = 32 + 32 * fuel by omega]
  rw [List.take_add]
  rw [List.drop_drop]
  rw [show 32 * i + 32 = 32 * (i + 1) by omega]

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

theorem decodeReturnValues_legacyUInt256UInt256_none_short {out : ByteArray}
    (hshort : out.size < 64) :
    ABI.decodeReturnValuesWithMode? DecodeMode.legacySolc05 [abiUInt256, abiUInt256] out =
      none := by
  have hlen : out.toList.length = out.size := by
    rw [byteArray_toList_eq, Array.length_toList]
    rfl
  unfold ABI.decodeReturnValuesWithMode?
  rw [abiTupleHeadSize_scalarWords_eq (types := [abiUInt256, abiUInt256]) (by decide)]
  simp only [bind, Option.bind]
  rw [decodeABIValues_scalarWordsWithMode_eq (mode := DecodeMode.legacySolc05)
    (types := [abiUInt256, abiUInt256]) (bytes := out.toList) (cursor := 0)
    (total := 32 * [abiUInt256, abiUInt256].length)
    (by decide) (by simp)]
  simp only [decodeScalarWordsWithMode?]
  by_cases hfirst : ((out.toList.drop 0).take 32).length = 32
  · rw [decodeScalarWordWithMode_uint256_ok (mode := DecodeMode.legacySolc05)
      (bytes := out.toList) (start := 0) hfirst]
    simp only [Option.bind_eq_bind, Option.bind_some]
    have htake32n : ¬ ((out.toList.drop 32).take 32).length = 32 := by
      rw [List.length_take, List.length_drop, hlen]
      omega
    rw [decodeScalarWordWithMode_uint256_none_short (mode := DecodeMode.legacySolc05)
      (bytes := out.toList) (start := 32) htake32n]
    simp
  · rw [decodeScalarWordWithMode_uint256_none_short (mode := DecodeMode.legacySolc05)
      (bytes := out.toList) (start := 0) hfirst]
    simp

theorem selector_toNat_readBytes4 (cd : ByteArray) :
    (UInt256.shiftRight (uInt256OfByteArray (ByteArray.readBytes cd 0 32)) ⟨224⟩).toNat
      = fromBytesBigEndian ((ByteArray.readBytes cd 0 32).data.toList.take 4) := by
  have hlen := readBytes32_len cd
  have hV : fromBytes' (ByteArray.readBytes cd 0 32).data.toList.reverse < 2 ^ 256 := by
    have := fromBytes'_le (bs := (ByteArray.readBytes cd 0 32).data.toList.reverse)
    rwa [List.length_reverse, hlen] at this
  unfold UInt256.shiftRight uInt256OfByteArray
  rw [if_neg (by decide : ¬ ((⟨224⟩ : UInt256).val ≥ 256))]
  show ((UInt256.ofNat _).val >>> (⟨224⟩ : UInt256).val).val = _
  rw [Fin.shiftRight_val]
  show (UInt256.ofNat _).val.val >>> (224 : ℕ) = _
  rw [Nat.shiftRight_eq_div_pow]
  show (fromBytes' _ % UInt256.size) / 2 ^ 224 = _
  rw [show UInt256.size = 2 ^ 256 from rfl, Nat.mod_eq_of_lt hV]
  show fromBytesBigEndian (ByteArray.readBytes cd 0 32).data.toList / 2 ^ 224 = _
  conv_lhs => rw [← List.take_append_drop 4 (ByteArray.readBytes cd 0 32).data.toList]
  rw [show (224 : ℕ) = 8 * ((ByteArray.readBytes cd 0 32).data.toList.drop 4).length from by
        rw [List.length_drop, hlen], fromBytesBigEndian_append_div]

theorem selectorWord_short_mod_256_zero {cd : ByteArray}
    (hshort : cd.size < 4) :
    (UInt256.shiftRight (uInt256OfByteArray (cd.readBytes 0 32)) ⟨224⟩).toNat % 256 = 0 := by
  rw [selector_toNat_readBytes4]
  have htake32eq4 : cd.data.toList.take 32 = cd.data.toList.take 4 := by
    have htake32 : cd.data.toList.take 32 = cd.data.toList := by
      rw [List.take_of_length_le]
      simpa [Array.length_toList] using (show cd.size ≤ 32 by omega)
    have htake4 : cd.data.toList.take 4 = cd.data.toList := by
      rw [List.take_of_length_le]
      simpa [Array.length_toList] using (show cd.size ≤ 4 by omega)
    rw [htake32, htake4]
  have hpad :
      (ByteArray.readBytes cd 0 32).data.toList.take 4 =
        cd.data.toList.take 4 ++ List.replicate (4 - cd.size) 0 := by
    rw [readBytes32_toList]
    have hlenTake32 : (cd.data.toList.take 32).length = cd.size := by
      rw [List.length_take, Array.length_toList]
      simpa using min_eq_right (show cd.size ≤ 32 by omega)
    rw [List.take_append, List.take_take, show min 4 32 = 4 by decide, hlenTake32]
    congr 1
    rw [List.take_replicate]
    rw [min_eq_left]
    omega
  rw [hpad, fromBytesBigEndian_append_zeros]
  have hpos : 1 ≤ 4 - cd.size := by
    omega
  have hsplit : 2 ^ (8 * (4 - cd.size)) = 256 * 2 ^ (8 * (4 - cd.size) - 8) := by
    rw [show 256 = 2 ^ 8 by norm_num]
    calc
      2 ^ (8 * (4 - cd.size)) = 2 ^ (8 + (8 * (4 - cd.size) - 8)) := by
        congr
        omega
      _ = 2 ^ 8 * 2 ^ (8 * (4 - cd.size) - 8) := by rw [Nat.pow_add]
  rw [hsplit]
  simpa [Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm] using
    (Nat.mul_mod_right 256
      (fromBytesBigEndian (List.take 4 cd.data.toList) * 2 ^ (8 * (4 - cd.size) - 8)))

theorem selectorWord_ne_of_short {cd : ByteArray} {sel : UInt256}
    (hshort : cd.size < 4) (hlow : sel.toNat % 256 ≠ 0) :
    UInt256.shiftRight (uInt256OfByteArray (cd.readBytes 0 32)) ⟨224⟩ ≠ sel := by
  intro heq
  have hmod := selectorWord_short_mod_256_zero (cd := cd) hshort
  have : sel.toNat % 256 = 0 := by
    simpa [heq] using hmod
  exact hlow this

theorem selectorWord_ne_of_selector_false
    {cd : ByteArray} {sel : UInt256} {c0 c1 c2 c3 : UInt8}
    (hsz : 4 ≤ cd.size)
    (hselNat : (fromBytesBigEndian [c0, c1, c2, c3] : ℕ) = sel.toNat)
    (hfalse : ((⟨#[c0, c1, c2, c3]⟩ : ByteArray) == cd.extract 0 4) = false) :
    UInt256.shiftRight (uInt256OfByteArray (cd.readBytes 0 32)) ⟨224⟩ ≠ sel := by
  intro heq
  have h := evmSelectorDecode hsz c0 c1 c2 c3 sel hselNat
  rw [hfalse, heq, u256_eq_refl] at h
  cases h

def packedUint256BoolBytes32ValueMem (mem : ByteArray) (base value : UInt256) :
    ByteArray :=
  (UInt256.toByteArray value).write 0 mem base.toNat 32

def packedUint256BoolBytes32FakeMem (mem : ByteArray) (base fakeWord : UInt256) :
    ByteArray :=
  (UInt256.toByteArray (UInt256.shiftLeft (UInt256.isZero (UInt256.isZero fakeWord)) ⟨248⟩)).write
    0 mem base.toNat 32

def packedUint256BoolBytes32SecretMem (mem : ByteArray) (base secret : UInt256) :
    ByteArray :=
  (UInt256.toByteArray secret).write 0 mem base.toNat 32

def packedUint256BoolBytes32LenMem (mem : ByteArray) (base len : UInt256) :
    ByteArray :=
  (UInt256.toByteArray len).write 0 mem base.toNat 32

def packedUint256BoolBytes32FreePtrMem (mem : ByteArray) (freePtr : UInt256) :
    ByteArray :=
  (UInt256.toByteArray freePtr).write 0 mem 64 32

def packedUint256BoolBytes32Bytes (value : UInt256) (fake : Bool) (secret : UInt256) : List UInt8 :=
  EVM.Word.toBytesBE value ++ [if fake then (1 : UInt8) else 0] ++ EVM.Word.toBytesBE secret

def packedUint256BoolBytes32HashValue (value : UInt256) (fake : Bool) (secret : UInt256) : Value :=
  .fixedBytes ⟨31, abiBytes32Width.isLt⟩
    (KEC (ByteArray.mk (packedUint256BoolBytes32Bytes value fake secret).toArray)).toList

theorem packedUint256BoolBytes32HashWord_toBytesBE (value : UInt256) (fake : Bool)
    (secret : UInt256) :
    EVM.Word.toBytesBE
        (uInt256OfByteArray
          (KEC (ByteArray.mk (packedUint256BoolBytes32Bytes value fake secret).toArray))) =
      (KEC (ByteArray.mk (packedUint256BoolBytes32Bytes value fake secret).toArray)).toList :=
  toBytesBE_keccak_uInt256OfByteArray _

theorem packedUint256BoolBytes32Hash_ne_of_word_ne {blinded value secret : UInt256}
    {fake : Bool}
    (hne :
      blinded ≠
        uInt256OfByteArray
          (KEC (ByteArray.mk (packedUint256BoolBytes32Bytes value fake secret).toArray))) :
    EVM.Word.toBytesBE blinded ≠
      (KEC (ByteArray.mk (packedUint256BoolBytes32Bytes value fake secret).toArray)).toList := by
  intro hbytes
  apply hne
  apply word_toBytesBE_inj
  rw [hbytes, packedUint256BoolBytes32HashWord_toBytesBE value fake secret]

theorem packedUint256BoolBytes32Hash_eq_of_u256_eq_one {blinded value secret : UInt256}
    {fake : Bool}
    (h :
      UInt256.eq blinded
          (uInt256OfByteArray
            (KEC (ByteArray.mk (packedUint256BoolBytes32Bytes value fake secret).toArray))) =
        ⟨1⟩) :
    EVM.Word.toBytesBE blinded =
      (KEC (ByteArray.mk (packedUint256BoolBytes32Bytes value fake secret).toArray)).toList := by
  have hword := uInt256_eq_one_eq h
  rw [hword, packedUint256BoolBytes32HashWord_toBytesBE value fake secret]

theorem packedUint256BoolBytes32Hash_ne_of_u256_eq_zero {blinded value secret : UInt256}
    {fake : Bool}
    (h :
      UInt256.eq blinded
          (uInt256OfByteArray
            (KEC (ByteArray.mk (packedUint256BoolBytes32Bytes value fake secret).toArray))) =
        ⟨0⟩) :
    EVM.Word.toBytesBE blinded ≠
      (KEC (ByteArray.mk (packedUint256BoolBytes32Bytes value fake secret).toArray)).toList := by
  exact packedUint256BoolBytes32Hash_ne_of_word_ne
    (word_ne_of_u256_eq_zero h)

theorem packedUint256BoolBytes32Mem_readWithPadding {mem : ByteArray}
    {fp value fakeWord secret : UInt256} {fake : Bool}
    (hfit : fp.toNat + 97 < UInt256.size)
    (hmemle : mem.size ≤ fp.toNat + 32)
    (hgap : fp.toNat + 32 - mem.size < USize.size)
    (hfp64 : 64 ≤ fp.toNat)
    (hfake : fakeWord = if fake then (⟨1⟩ : UInt256) else ⟨0⟩) :
    let base := (⟨32⟩ : UInt256) + fp
    let fakeBase := base + ⟨32⟩
    let secretBase := base + ⟨33⟩
    let newFree := (⟨65⟩ : UInt256) + base
    let packedLen := UInt256.sub (UInt256.sub newFree fp) ⟨32⟩
    let mem1 := packedUint256BoolBytes32ValueMem mem base value
    let mem2 := packedUint256BoolBytes32FakeMem mem1 fakeBase fakeWord
    let mem3 := packedUint256BoolBytes32SecretMem mem2 secretBase secret
    let mem4 := packedUint256BoolBytes32LenMem mem3 fp packedLen
    let mem5 := packedUint256BoolBytes32FreePtrMem mem4 newFree
    mem5.readWithPadding base.toNat packedLen.toNat =
      ByteArray.mk (packedUint256BoolBytes32Bytes value fake secret).toArray := by
  intro base fakeBase secretBase newFree packedLen mem1 mem2 mem3 mem4 mem5
  have hbaseNat : base.toNat = fp.toNat + 32 := by
    dsimp [base]
    rw [uadd_toNat]
    have hlt : 32 + fp.toNat < UInt256.size := by omega
    change (32 + fp.toNat) % UInt256.size = fp.toNat + 32
    rw [Nat.mod_eq_of_lt hlt]
    omega
  have hfakeBaseNat : fakeBase.toNat = fp.toNat + 64 := by
    dsimp [fakeBase]
    rw [uadd_toNat, hbaseNat]
    have hlt : (fp.toNat + 32) + 32 < UInt256.size := by omega
    change (fp.toNat + 32 + 32) % UInt256.size = fp.toNat + 64
    rw [Nat.mod_eq_of_lt hlt]
  have hsecretBaseNat : secretBase.toNat = fp.toNat + 65 := by
    dsimp [secretBase]
    rw [uadd_toNat, hbaseNat]
    have hlt : (fp.toNat + 32) + 33 < UInt256.size := by omega
    change (fp.toNat + 32 + 33) % UInt256.size = fp.toNat + 65
    rw [Nat.mod_eq_of_lt hlt]
  have hnewFreeNat : newFree.toNat = fp.toNat + 97 := by
    dsimp [newFree]
    rw [uadd_toNat, hbaseNat]
    have hlt : 65 + (fp.toNat + 32) < UInt256.size := by omega
    change (65 + (fp.toNat + 32)) % UInt256.size = fp.toNat + 97
    rw [Nat.mod_eq_of_lt hlt]
    omega
  have hpackedLenNat : packedLen.toNat = 65 := by
    have hsub1 : (UInt256.sub newFree fp).toNat = 97 := by
      rw [usub_toNat]
      · rw [hnewFreeNat]
        omega
      · rw [hnewFreeNat]
        omega
    dsimp [packedLen]
    rw [usub_toNat]
    · rw [hsub1]
      change 97 - 32 = 65
      norm_num
    · rw [hsub1]
      change 32 ≤ 97
      norm_num
  have hmem1_read : mem1.readWithPadding base.toNat 32 = UInt256.toByteArray value := by
    dsimp [mem1, packedUint256BoolBytes32ValueMem]
    rw [toByteArray_write_read_back_of_gap]
    simpa [hbaseNat] using hgap
  have hmem1_size : mem1.size = fp.toNat + 64 := by
    dsimp [mem1, packedUint256BoolBytes32ValueMem]
    rw [toByteArray_write_eq _ _ base.toNat]
    · rw [ByteArray.size_append, ByteArray.size_append, ByteArray_zeroes_size, toByteArray_size]
      omega
    · rw [hbaseNat]; exact hmemle
    · simpa [hbaseNat] using hgap
  have hmem2_value : mem2.readWithPadding base.toNat 32 = UInt256.toByteArray value := by
    dsimp [mem2, packedUint256BoolBytes32FakeMem]
    rw [write32_read_below
      (src := UInt256.toByteArray
        (UInt256.shiftLeft (UInt256.isZero (UInt256.isZero fakeWord)) ⟨248⟩))
      (base := mem1) (destAddr := fakeBase.toNat) (readAddr := base.toNat)
      (hsrc := by rw [toByteArray_size])
      (hlo := by rw [hmem1_size, hfakeBaseNat])
      (hbelow := by rw [hbaseNat, hfakeBaseNat])]
    exact hmem1_read
  have hmem2_fake : mem2.readWithPadding fakeBase.toNat 1 =
      ByteArray.mk #[if fake then (1 : UInt8) else 0] := by
    dsimp [mem2, packedUint256BoolBytes32FakeMem]
    rw [write32_read_prefix_len]
    · subst fakeWord
      rw [toByteArray_eq_toBytesBE]
      cases fake <;> decide +kernel
    · rw [toByteArray_size]
    · rw [hmem1_size, hfakeBaseNat]
    · omega
    · norm_num
    · norm_num
  have hmem2_size : mem2.size = fp.toNat + 96 := by
    dsimp [mem2, packedUint256BoolBytes32FakeMem]
    rw [show fakeBase.toNat = mem1.size by rw [hmem1_size, hfakeBaseNat]]
    rw [write_at_end_eq]
    · rw [ByteArray.size_append, ByteArray.size_extract, toByteArray_size, hmem1_size]
      omega
    · decide
    · rw [toByteArray_size]
  have hmem3_value : mem3.readWithPadding base.toNat 32 = UInt256.toByteArray value := by
    dsimp [mem3, packedUint256BoolBytes32SecretMem]
    rw [write32_read_below
      (src := UInt256.toByteArray secret) (base := mem2)
      (destAddr := secretBase.toNat) (readAddr := base.toNat)
      (hsrc := by rw [toByteArray_size])
      (hlo := by rw [hmem2_size, hsecretBaseNat]; omega)
      (hbelow := by rw [hbaseNat, hsecretBaseNat]; omega)]
    exact hmem2_value
  have hmem3_fake : mem3.readWithPadding fakeBase.toNat 1 =
      ByteArray.mk #[if fake then (1 : UInt8) else 0] := by
    dsimp [mem3, packedUint256BoolBytes32SecretMem]
    rw [write32_read_below_len
      (src := UInt256.toByteArray secret) (base := mem2)
      (dest := secretBase.toNat) (read := fakeBase.toNat) (len := 1)
      (hsrc := by rw [toByteArray_size])
      (hlo := by rw [hmem2_size, hsecretBaseNat]; omega)
      (hbelow := by rw [hfakeBaseNat, hsecretBaseNat])
      (hin := by rw [hmem2_size, hfakeBaseNat]; omega)
      (hpos := by norm_num) (hlen64 := by norm_num)]
    exact hmem2_fake
  have hmem3_secret : mem3.readWithPadding secretBase.toNat 32 = UInt256.toByteArray secret := by
    dsimp [mem3, packedUint256BoolBytes32SecretMem]
    rw [write32_read_back]
    · rw [show (UInt256.toByteArray secret).extract 0 32 = UInt256.toByteArray secret by
        rw [show 32 = (UInt256.toByteArray secret).size by rw [toByteArray_size]]
        exact byteArray_extract_self _]
    · rw [toByteArray_size]
    · rw [hmem2_size, hsecretBaseNat]; omega
  have hmem3_size : mem3.size = fp.toNat + 97 := by
    dsimp [mem3, packedUint256BoolBytes32SecretMem]
    rw [write32_eq _ _ secretBase.toNat]
    · rw [ByteArray.size_append, ByteArray.size_append, ByteArray.size_extract,
        ByteArray.size_extract, ByteArray.size_extract, toByteArray_size, hmem2_size,
        hsecretBaseNat]
      omega
    · rw [toByteArray_size]
    · rw [hmem2_size, hsecretBaseNat]; omega
  have hmem4_value : mem4.readWithPadding base.toNat 32 = UInt256.toByteArray value := by
    dsimp [mem4, packedUint256BoolBytes32LenMem]
    rw [write32_read_above
      (src := UInt256.toByteArray packedLen) (base := mem3)
      (destAddr := fp.toNat) (readAddr := base.toNat)
      (hsrc := by rw [toByteArray_size])
      (hlo := by rw [hmem3_size]; omega)
      (habove := by rw [hbaseNat])
      (hin := by rw [hmem3_size, hbaseNat]; omega)]
    exact hmem3_value
  have hmem4_fake : mem4.readWithPadding fakeBase.toNat 1 =
      ByteArray.mk #[if fake then (1 : UInt8) else 0] := by
    dsimp [mem4, packedUint256BoolBytes32LenMem]
    rw [write32_read_above_len
      (src := UInt256.toByteArray packedLen) (base := mem3)
      (dest := fp.toNat) (read := fakeBase.toNat) (len := 1)
      (hsrc := by rw [toByteArray_size])
      (hlo := by rw [hmem3_size]; omega)
      (habove := by rw [hfakeBaseNat]; omega)
      (hin := by rw [hmem3_size, hfakeBaseNat]; omega)
      (hpos := by norm_num) (hlen64 := by norm_num)]
    exact hmem3_fake
  have hmem4_secret : mem4.readWithPadding secretBase.toNat 32 = UInt256.toByteArray secret := by
    dsimp [mem4, packedUint256BoolBytes32LenMem]
    rw [write32_read_above
      (src := UInt256.toByteArray packedLen) (base := mem3)
      (destAddr := fp.toNat) (readAddr := secretBase.toNat)
      (hsrc := by rw [toByteArray_size])
      (hlo := by rw [hmem3_size]; omega)
      (habove := by rw [hsecretBaseNat]; omega)
      (hin := by rw [hmem3_size, hsecretBaseNat])]
    exact hmem3_secret
  have hmem4_size : mem4.size = fp.toNat + 97 := by
    dsimp [mem4, packedUint256BoolBytes32LenMem]
    rw [write32_eq _ _ fp.toNat]
    · rw [ByteArray.size_append, ByteArray.size_append, ByteArray.size_extract,
        ByteArray.size_extract, ByteArray.size_extract, toByteArray_size, hmem3_size]
      omega
    · rw [toByteArray_size]
    · rw [hmem3_size]; omega
  have hmem5_value : mem5.readWithPadding base.toNat 32 = UInt256.toByteArray value := by
    dsimp [mem5, packedUint256BoolBytes32FreePtrMem]
    rw [write32_read_above
      (src := UInt256.toByteArray newFree) (base := mem4)
      (destAddr := 64) (readAddr := base.toNat)
      (hsrc := by rw [toByteArray_size])
      (hlo := by rw [hmem4_size]; omega)
      (habove := by rw [hbaseNat]; omega)
      (hin := by rw [hmem4_size, hbaseNat]; omega)]
    exact hmem4_value
  have hmem5_fake : mem5.readWithPadding fakeBase.toNat 1 =
      ByteArray.mk #[if fake then (1 : UInt8) else 0] := by
    dsimp [mem5, packedUint256BoolBytes32FreePtrMem]
    rw [write32_read_above_len
      (src := UInt256.toByteArray newFree) (base := mem4)
      (dest := 64) (read := fakeBase.toNat) (len := 1)
      (hsrc := by rw [toByteArray_size])
      (hlo := by rw [hmem4_size]; omega)
      (habove := by rw [hfakeBaseNat]; omega)
      (hin := by rw [hmem4_size, hfakeBaseNat]; omega)
      (hpos := by norm_num) (hlen64 := by norm_num)]
    exact hmem4_fake
  have hmem5_secret : mem5.readWithPadding secretBase.toNat 32 = UInt256.toByteArray secret := by
    dsimp [mem5, packedUint256BoolBytes32FreePtrMem]
    rw [write32_read_above
      (src := UInt256.toByteArray newFree) (base := mem4)
      (destAddr := 64) (readAddr := secretBase.toNat)
      (hsrc := by rw [toByteArray_size])
      (hlo := by rw [hmem4_size]; omega)
      (habove := by rw [hsecretBaseNat]; omega)
      (hin := by rw [hmem4_size, hsecretBaseNat])]
    exact hmem4_secret
  have hmem5_size : mem5.size = fp.toNat + 97 := by
    dsimp [mem5, packedUint256BoolBytes32FreePtrMem]
    rw [write32_eq _ _ 64]
    · rw [ByteArray.size_append, ByteArray.size_append, ByteArray.size_extract,
        ByteArray.size_extract, ByteArray.size_extract, toByteArray_size, hmem4_size]
      omega
    · rw [toByteArray_size]
    · rw [hmem4_size]; omega
  rw [hpackedLenNat]
  rw [readWithPadding_split_32_1_32 mem5 base.toNat]
  · rw [hmem5_value]
    rw [show base.toNat + 32 = fakeBase.toNat by omega]
    rw [hmem5_fake]
    rw [show base.toNat + 33 = secretBase.toNat by omega]
    rw [hmem5_secret]
    rw [toByteArray_eq_toBytesBE value, toByteArray_eq_toBytesBE secret]
    cases fake <;> rfl
  · rw [hmem5_size, hbaseNat]

theorem packedUint256BoolBytes32Mem_hash {mem : ByteArray}
    {fp value fakeWord secret : UInt256} {fake : Bool}
    (hfit : fp.toNat + 97 < UInt256.size)
    (hmemle : mem.size ≤ fp.toNat + 32)
    (hgap : fp.toNat + 32 - mem.size < USize.size)
    (hfp64 : 64 ≤ fp.toNat)
    (hfake : fakeWord = if fake then (⟨1⟩ : UInt256) else ⟨0⟩) :
    let base := (⟨32⟩ : UInt256) + fp
    let fakeBase := base + ⟨32⟩
    let secretBase := base + ⟨33⟩
    let newFree := (⟨65⟩ : UInt256) + base
    let packedLen := UInt256.sub (UInt256.sub newFree fp) ⟨32⟩
    let mem1 := packedUint256BoolBytes32ValueMem mem base value
    let mem2 := packedUint256BoolBytes32FakeMem mem1 fakeBase fakeWord
    let mem3 := packedUint256BoolBytes32SecretMem mem2 secretBase secret
    let mem4 := packedUint256BoolBytes32LenMem mem3 fp packedLen
    let mem5 := packedUint256BoolBytes32FreePtrMem mem4 newFree
    UInt256.ofNat
        (fromByteArrayBigEndian (KEC (mem5.readWithPadding base.toNat packedLen.toNat))) =
      uInt256OfByteArray
        (KEC (ByteArray.mk (packedUint256BoolBytes32Bytes value fake secret).toArray)) := by
  intro base fakeBase secretBase newFree packedLen mem1 mem2 mem3 mem4 mem5
  have hread :
      mem5.readWithPadding base.toNat packedLen.toNat =
        ByteArray.mk (packedUint256BoolBytes32Bytes value fake secret).toArray := by
    simpa [base, fakeBase, secretBase, newFree, packedLen, mem1, mem2, mem3, mem4, mem5]
      using packedUint256BoolBytes32Mem_readWithPadding
        (mem := mem) (fp := fp) (value := value) (fakeWord := fakeWord)
        (secret := secret) (fake := fake) hfit hmemle hgap hfp64 hfake
  rw [hread, uInt256OfByteArray_eq]

theorem packedUint256BoolBytes32Mem_len_read {mem : ByteArray}
    {fp value fakeWord secret : UInt256}
    (hfit : fp.toNat + 97 < UInt256.size)
    (hmemle : mem.size ≤ fp.toNat + 32)
    (hgap : fp.toNat + 32 - mem.size < USize.size)
    (hfp96 : 96 ≤ fp.toNat) :
    let base := (⟨32⟩ : UInt256) + fp
    let fakeBase := base + ⟨32⟩
    let secretBase := base + ⟨33⟩
    let newFree := (⟨65⟩ : UInt256) + base
    let packedLen := UInt256.sub (UInt256.sub newFree fp) ⟨32⟩
    let mem1 := packedUint256BoolBytes32ValueMem mem base value
    let mem2 := packedUint256BoolBytes32FakeMem mem1 fakeBase fakeWord
    let mem3 := packedUint256BoolBytes32SecretMem mem2 secretBase secret
    let mem4 := packedUint256BoolBytes32LenMem mem3 fp packedLen
    let mem5 := packedUint256BoolBytes32FreePtrMem mem4 newFree
    mem5.readWithPadding fp.toNat 32 = UInt256.toByteArray packedLen := by
  intro base fakeBase secretBase newFree packedLen mem1 mem2 mem3 mem4 mem5
  have hbaseNat : base.toNat = fp.toNat + 32 := by
    dsimp [base]
    rw [uadd_toNat]
    have hlt : 32 + fp.toNat < UInt256.size := by omega
    change (32 + fp.toNat) % UInt256.size = fp.toNat + 32
    rw [Nat.mod_eq_of_lt hlt]
    omega
  have hfakeBaseNat : fakeBase.toNat = fp.toNat + 64 := by
    dsimp [fakeBase]
    rw [uadd_toNat, hbaseNat]
    have hlt : (fp.toNat + 32) + 32 < UInt256.size := by omega
    change (fp.toNat + 32 + 32) % UInt256.size = fp.toNat + 64
    rw [Nat.mod_eq_of_lt hlt]
  have hsecretBaseNat : secretBase.toNat = fp.toNat + 65 := by
    dsimp [secretBase]
    rw [uadd_toNat, hbaseNat]
    have hlt : (fp.toNat + 32) + 33 < UInt256.size := by omega
    change (fp.toNat + 32 + 33) % UInt256.size = fp.toNat + 65
    rw [Nat.mod_eq_of_lt hlt]
  have hmem1_size : mem1.size = fp.toNat + 64 := by
    dsimp [mem1, packedUint256BoolBytes32ValueMem]
    rw [toByteArray_write_eq _ _ base.toNat]
    · rw [ByteArray.size_append, ByteArray.size_append, ByteArray_zeroes_size, toByteArray_size]
      omega
    · rw [hbaseNat]; exact hmemle
    · simpa [hbaseNat] using hgap
  have hmem2_size : mem2.size = fp.toNat + 96 := by
    dsimp [mem2, packedUint256BoolBytes32FakeMem]
    rw [show fakeBase.toNat = mem1.size by rw [hmem1_size, hfakeBaseNat]]
    rw [write_at_end_eq]
    · rw [ByteArray.size_append, ByteArray.size_extract, toByteArray_size, hmem1_size]
      omega
    · decide
    · rw [toByteArray_size]
  have hmem3_size : mem3.size = fp.toNat + 97 := by
    dsimp [mem3, packedUint256BoolBytes32SecretMem]
    rw [write32_eq _ _ secretBase.toNat]
    · rw [ByteArray.size_append, ByteArray.size_append, ByteArray.size_extract,
        ByteArray.size_extract, ByteArray.size_extract, toByteArray_size, hmem2_size,
        hsecretBaseNat]
      omega
    · rw [toByteArray_size]
    · rw [hmem2_size, hsecretBaseNat]; omega
  have hmem4_read : mem4.readWithPadding fp.toNat 32 = UInt256.toByteArray packedLen := by
    dsimp [mem4, packedUint256BoolBytes32LenMem]
    rw [write32_read_back]
    · rw [show (UInt256.toByteArray packedLen).extract 0 32 = UInt256.toByteArray packedLen by
        rw [show 32 = (UInt256.toByteArray packedLen).size by rw [toByteArray_size]]
        exact byteArray_extract_self _]
    · rw [toByteArray_size]
    · rw [hmem3_size]; omega
  have hmem4_size : mem4.size = fp.toNat + 97 := by
    dsimp [mem4, packedUint256BoolBytes32LenMem]
    rw [write32_eq _ _ fp.toNat]
    · rw [ByteArray.size_append, ByteArray.size_append, ByteArray.size_extract,
        ByteArray.size_extract, ByteArray.size_extract, toByteArray_size, hmem3_size]
      omega
    · rw [toByteArray_size]
    · rw [hmem3_size]; omega
  dsimp [mem5, packedUint256BoolBytes32FreePtrMem]
  rw [write32_read_above
    (src := UInt256.toByteArray newFree) (base := mem4)
    (destAddr := 64) (readAddr := fp.toNat)
    (hsrc := by rw [toByteArray_size])
    (hlo := by rw [hmem4_size]; omega)
    (habove := by omega)
      (hin := by rw [hmem4_size]; omega)]
  exact hmem4_read

theorem packedUint256BoolBytes32Mem_beforeFreePtr_size {mem : ByteArray}
    {fp value fakeWord secret : UInt256}
    (hfit : fp.toNat + 97 < UInt256.size)
    (hmemle : mem.size ≤ fp.toNat + 32)
    (hgap : fp.toNat + 32 - mem.size < USize.size) :
    let base := (⟨32⟩ : UInt256) + fp
    let fakeBase := base + ⟨32⟩
    let secretBase := base + ⟨33⟩
    let newFree := (⟨65⟩ : UInt256) + base
    let packedLen := UInt256.sub (UInt256.sub newFree fp) ⟨32⟩
    let mem1 := packedUint256BoolBytes32ValueMem mem base value
    let mem2 := packedUint256BoolBytes32FakeMem mem1 fakeBase fakeWord
    let mem3 := packedUint256BoolBytes32SecretMem mem2 secretBase secret
    let mem4 := packedUint256BoolBytes32LenMem mem3 fp packedLen
    mem4.size = fp.toNat + 97 := by
  intro base fakeBase secretBase newFree packedLen mem1 mem2 mem3 mem4
  have hbaseNat : base.toNat = fp.toNat + 32 := by
    dsimp [base]
    rw [uadd_toNat]
    have hlt : 32 + fp.toNat < UInt256.size := by omega
    change (32 + fp.toNat) % UInt256.size = fp.toNat + 32
    rw [Nat.mod_eq_of_lt hlt]
    omega
  have hfakeBaseNat : fakeBase.toNat = fp.toNat + 64 := by
    dsimp [fakeBase]
    rw [uadd_toNat, hbaseNat]
    have hlt : (fp.toNat + 32) + 32 < UInt256.size := by omega
    change (fp.toNat + 32 + 32) % UInt256.size = fp.toNat + 64
    rw [Nat.mod_eq_of_lt hlt]
  have hsecretBaseNat : secretBase.toNat = fp.toNat + 65 := by
    dsimp [secretBase]
    rw [uadd_toNat, hbaseNat]
    have hlt : (fp.toNat + 32) + 33 < UInt256.size := by omega
    change (fp.toNat + 32 + 33) % UInt256.size = fp.toNat + 65
    rw [Nat.mod_eq_of_lt hlt]
  have hmem1_size : mem1.size = fp.toNat + 64 := by
    dsimp [mem1, packedUint256BoolBytes32ValueMem]
    rw [toByteArray_write_eq _ _ base.toNat]
    · rw [ByteArray.size_append, ByteArray.size_append, ByteArray_zeroes_size, toByteArray_size]
      omega
    · rw [hbaseNat]; exact hmemle
    · simpa [hbaseNat] using hgap
  have hmem2_size : mem2.size = fp.toNat + 96 := by
    dsimp [mem2, packedUint256BoolBytes32FakeMem]
    rw [show fakeBase.toNat = mem1.size by rw [hmem1_size, hfakeBaseNat]]
    rw [write_at_end_eq]
    · rw [ByteArray.size_append, ByteArray.size_extract, toByteArray_size, hmem1_size]
      omega
    · decide
    · rw [toByteArray_size]
  have hmem3_size : mem3.size = fp.toNat + 97 := by
    dsimp [mem3, packedUint256BoolBytes32SecretMem]
    rw [write32_eq _ _ secretBase.toNat]
    · rw [ByteArray.size_append, ByteArray.size_append, ByteArray.size_extract,
        ByteArray.size_extract, ByteArray.size_extract, toByteArray_size, hmem2_size,
        hsecretBaseNat]
      omega
    · rw [toByteArray_size]
    · rw [hmem2_size, hsecretBaseNat]; omega
  dsimp [mem4, packedUint256BoolBytes32LenMem]
  rw [write32_eq _ _ fp.toNat]
  · rw [ByteArray.size_append, ByteArray.size_append, ByteArray.size_extract,
      ByteArray.size_extract, ByteArray.size_extract, toByteArray_size, hmem3_size]
    omega
  · rw [toByteArray_size]
  · rw [hmem3_size]; omega

theorem packedUint256BoolBytes32Mem_size {mem : ByteArray}
    {fp value fakeWord secret : UInt256}
    (hfit : fp.toNat + 97 < UInt256.size)
    (hmemle : mem.size ≤ fp.toNat + 32)
    (hgap : fp.toNat + 32 - mem.size < USize.size) :
    let base := (⟨32⟩ : UInt256) + fp
    let fakeBase := base + ⟨32⟩
    let secretBase := base + ⟨33⟩
    let newFree := (⟨65⟩ : UInt256) + base
    let packedLen := UInt256.sub (UInt256.sub newFree fp) ⟨32⟩
    let mem1 := packedUint256BoolBytes32ValueMem mem base value
    let mem2 := packedUint256BoolBytes32FakeMem mem1 fakeBase fakeWord
    let mem3 := packedUint256BoolBytes32SecretMem mem2 secretBase secret
    let mem4 := packedUint256BoolBytes32LenMem mem3 fp packedLen
    let mem5 := packedUint256BoolBytes32FreePtrMem mem4 newFree
    mem5.size = fp.toNat + 97 := by
  intro base fakeBase secretBase newFree packedLen mem1 mem2 mem3 mem4 mem5
  have hmem4_size : mem4.size = fp.toNat + 97 := by
    simpa [base, fakeBase, secretBase, newFree, packedLen, mem1, mem2, mem3, mem4]
      using packedUint256BoolBytes32Mem_beforeFreePtr_size
        (mem := mem) (fp := fp) (value := value) (fakeWord := fakeWord)
        (secret := secret) hfit hmemle hgap
  dsimp [mem5, packedUint256BoolBytes32FreePtrMem]
  rw [write32_eq _ _ 64]
  · rw [ByteArray.size_append, ByteArray.size_append, ByteArray.size_extract,
      ByteArray.size_extract, ByteArray.size_extract, toByteArray_size, hmem4_size]
    omega
  · rw [toByteArray_size]
  · rw [hmem4_size]; omega

theorem packedUint256BoolBytes32Mem_freePtr_read {mem : ByteArray}
    {fp value fakeWord secret : UInt256}
    (hfit : fp.toNat + 97 < UInt256.size)
    (hmemle : mem.size ≤ fp.toNat + 32)
    (hgap : fp.toNat + 32 - mem.size < USize.size) :
    let base := (⟨32⟩ : UInt256) + fp
    let fakeBase := base + ⟨32⟩
    let secretBase := base + ⟨33⟩
    let newFree := (⟨65⟩ : UInt256) + base
    let packedLen := UInt256.sub (UInt256.sub newFree fp) ⟨32⟩
    let mem1 := packedUint256BoolBytes32ValueMem mem base value
    let mem2 := packedUint256BoolBytes32FakeMem mem1 fakeBase fakeWord
    let mem3 := packedUint256BoolBytes32SecretMem mem2 secretBase secret
    let mem4 := packedUint256BoolBytes32LenMem mem3 fp packedLen
    let mem5 := packedUint256BoolBytes32FreePtrMem mem4 newFree
    mem5.readWithPadding 64 32 = UInt256.toByteArray newFree := by
  intro base fakeBase secretBase newFree packedLen mem1 mem2 mem3 mem4 mem5
  have hmem4_size : mem4.size = fp.toNat + 97 := by
    simpa [base, fakeBase, secretBase, newFree, packedLen, mem1, mem2, mem3, mem4]
      using packedUint256BoolBytes32Mem_beforeFreePtr_size
        (mem := mem) (fp := fp) (value := value) (fakeWord := fakeWord)
        (secret := secret) hfit hmemle hgap
  dsimp [mem5, packedUint256BoolBytes32FreePtrMem]
  rw [write32_read_back]
  · rw [show (UInt256.toByteArray newFree).extract 0 32 =
        UInt256.toByteArray newFree by
      rw [show 32 = (UInt256.toByteArray newFree).size by rw [toByteArray_size]]
      exact byteArray_extract_self _]
  · rw [toByteArray_size]
  · rw [hmem4_size]; omega

theorem packedUint256BoolBytes32Prefix_size {mem : ByteArray}
    {fp value fakeWord secret : UInt256}
    (hfit : fp.toNat + 97 < UInt256.size)
    (hmemle : mem.size ≤ fp.toNat + 32)
    (hgap : fp.toNat + 32 - mem.size < USize.size) :
    let base := (⟨32⟩ : UInt256) + fp
    let fakeBase := base + ⟨32⟩
    let secretBase := base + ⟨33⟩
    let mem1 := packedUint256BoolBytes32ValueMem mem base value
    let mem2 := packedUint256BoolBytes32FakeMem mem1 fakeBase fakeWord
    let mem3 := packedUint256BoolBytes32SecretMem mem2 secretBase secret
    mem3.size = fp.toNat + 97 := by
  intro base fakeBase secretBase mem1 mem2 mem3
  have hbaseNat : base.toNat = fp.toNat + 32 := by
    dsimp [base]
    rw [uadd_toNat]
    have hlt : 32 + fp.toNat < UInt256.size := by omega
    change (32 + fp.toNat) % UInt256.size = fp.toNat + 32
    rw [Nat.mod_eq_of_lt hlt]
    omega
  have hfakeBaseNat : fakeBase.toNat = fp.toNat + 64 := by
    dsimp [fakeBase]
    rw [uadd_toNat, hbaseNat]
    have hlt : (fp.toNat + 32) + 32 < UInt256.size := by omega
    change (fp.toNat + 32 + 32) % UInt256.size = fp.toNat + 64
    rw [Nat.mod_eq_of_lt hlt]
  have hsecretBaseNat : secretBase.toNat = fp.toNat + 65 := by
    dsimp [secretBase]
    rw [uadd_toNat, hbaseNat]
    have hlt : (fp.toNat + 32) + 33 < UInt256.size := by omega
    change (fp.toNat + 32 + 33) % UInt256.size = fp.toNat + 65
    rw [Nat.mod_eq_of_lt hlt]
  have hmem1_size : mem1.size = fp.toNat + 64 := by
    dsimp [mem1, packedUint256BoolBytes32ValueMem]
    rw [toByteArray_write_eq _ _ base.toNat]
    · rw [ByteArray.size_append, ByteArray.size_append, ByteArray_zeroes_size, toByteArray_size]
      omega
    · rw [hbaseNat]; exact hmemle
    · simpa [hbaseNat] using hgap
  have hmem2_size : mem2.size = fp.toNat + 96 := by
    dsimp [mem2, packedUint256BoolBytes32FakeMem]
    rw [show fakeBase.toNat = mem1.size by rw [hmem1_size, hfakeBaseNat]]
    rw [write_at_end_eq]
    · rw [ByteArray.size_append, ByteArray.size_extract, toByteArray_size, hmem1_size]
      omega
    · decide
    · rw [toByteArray_size]
  dsimp [mem3, packedUint256BoolBytes32SecretMem]
  rw [write32_eq _ _ secretBase.toNat]
  · rw [ByteArray.size_append, ByteArray.size_append, ByteArray.size_extract,
      ByteArray.size_extract, ByteArray.size_extract, toByteArray_size, hmem2_size,
      hsecretBaseNat]
    omega
  · rw [toByteArray_size]
  · rw [hmem2_size, hsecretBaseNat]; omega

theorem packedUint256BoolBytes32Prefix_preserve_fp {mem : ByteArray}
    {fp value fakeWord secret : UInt256}
    (hfit : fp.toNat + 97 < UInt256.size)
    (hmemle : mem.size ≤ fp.toNat + 32)
    (hgap : fp.toNat + 32 - mem.size < USize.size)
    (hread : mem.readWithPadding 64 32 = UInt256.toByteArray fp)
    (hmem96 : 96 ≤ mem.size) (hfp64 : 64 ≤ fp.toNat) :
    let base := (⟨32⟩ : UInt256) + fp
    let fakeBase := base + ⟨32⟩
    let secretBase := base + ⟨33⟩
    let mem1 := packedUint256BoolBytes32ValueMem mem base value
    let mem2 := packedUint256BoolBytes32FakeMem mem1 fakeBase fakeWord
    let mem3 := packedUint256BoolBytes32SecretMem mem2 secretBase secret
    mem3.readWithPadding 64 32 = UInt256.toByteArray fp := by
  intro base fakeBase secretBase mem1 mem2 mem3
  have hbaseNat : base.toNat = fp.toNat + 32 := by
    dsimp [base]
    rw [uadd_toNat]
    have hlt : 32 + fp.toNat < UInt256.size := by omega
    change (32 + fp.toNat) % UInt256.size = fp.toNat + 32
    rw [Nat.mod_eq_of_lt hlt]
    omega
  have hfakeBaseNat : fakeBase.toNat = fp.toNat + 64 := by
    dsimp [fakeBase]
    rw [uadd_toNat, hbaseNat]
    have hlt : (fp.toNat + 32) + 32 < UInt256.size := by omega
    change (fp.toNat + 32 + 32) % UInt256.size = fp.toNat + 64
    rw [Nat.mod_eq_of_lt hlt]
  have hsecretBaseNat : secretBase.toNat = fp.toNat + 65 := by
    dsimp [secretBase]
    rw [uadd_toNat, hbaseNat]
    have hlt : (fp.toNat + 32) + 33 < UInt256.size := by omega
    change (fp.toNat + 32 + 33) % UInt256.size = fp.toNat + 65
    rw [Nat.mod_eq_of_lt hlt]
  have hmem1_read : mem1.readWithPadding 64 32 = UInt256.toByteArray fp := by
    dsimp [mem1, packedUint256BoolBytes32ValueMem]
    rw [toByteArray_write_read_below_of_gap]
    · exact hread
    · exact hmem96
    · rw [hbaseNat]; omega
    · simpa [hbaseNat] using hgap
  have hmem1_size : mem1.size = fp.toNat + 64 := by
    dsimp [mem1, packedUint256BoolBytes32ValueMem]
    rw [toByteArray_write_eq _ _ base.toNat]
    · rw [ByteArray.size_append, ByteArray.size_append, ByteArray_zeroes_size, toByteArray_size]
      omega
    · rw [hbaseNat]; exact hmemle
    · simpa [hbaseNat] using hgap
  have hmem2_read : mem2.readWithPadding 64 32 = UInt256.toByteArray fp := by
    dsimp [mem2, packedUint256BoolBytes32FakeMem]
    rw [toByteArray_write_read_below_of_gap]
    · exact hmem1_read
    · rw [hmem1_size]; omega
    · rw [hfakeBaseNat]; omega
    · rw [hmem1_size, hfakeBaseNat]
      have hpos : 0 < USize.size := USize.size_pos
      omega
  have hmem2_size : mem2.size = fp.toNat + 96 := by
    dsimp [mem2, packedUint256BoolBytes32FakeMem]
    rw [show fakeBase.toNat = mem1.size by rw [hmem1_size, hfakeBaseNat]]
    rw [write_at_end_eq]
    · rw [ByteArray.size_append, ByteArray.size_extract, toByteArray_size, hmem1_size]
      omega
    · decide
    · rw [toByteArray_size]
  dsimp [mem3, packedUint256BoolBytes32SecretMem]
  rw [toByteArray_write_read_below_of_gap]
  · exact hmem2_read
  · rw [hmem2_size]; omega
  · rw [hsecretBaseNat]; omega
  · rw [hmem2_size, hsecretBaseNat]
    have hpos : 0 < USize.size := USize.size_pos
    omega

theorem packedUint256BoolBytes32_aw_facts {aw fp : UInt256}
    (haw : 3 ≤ aw.toNat) (hawSmall : aw.toNat * 32 < UInt256.size)
    (hfit128 : fp.toNat + 128 < UInt256.size) :
    let awP1 := UInt256.ofNat (MachineState.M aw.toNat (⟨64⟩ : UInt256).toNat 32)
    let base := (⟨32⟩ : UInt256) + fp
    let fakeBase := base + ⟨32⟩
    let secretBase := base + ⟨33⟩
    let newFree := (⟨65⟩ : UInt256) + base
    let packedLen := UInt256.sub (UInt256.sub newFree fp) ⟨32⟩
    let awP2 := UInt256.ofNat (MachineState.M awP1.toNat base.toNat 32)
    let awP3 := UInt256.ofNat (MachineState.M awP2.toNat fakeBase.toNat 32)
    let awP4 := UInt256.ofNat (MachineState.M awP3.toNat secretBase.toNat 32)
    let aw1 := UInt256.ofNat (MachineState.M awP4.toNat (⟨64⟩ : UInt256).toNat 32)
    let aw2 := UInt256.ofNat (MachineState.M aw1.toNat fp.toNat 32)
    let aw3 := UInt256.ofNat (MachineState.M aw2.toNat (⟨64⟩ : UInt256).toNat 32)
    let aw4 := UInt256.ofNat (MachineState.M aw3.toNat fp.toNat 32)
    let aw5 := UInt256.ofNat (MachineState.M aw4.toNat base.toNat packedLen.toNat)
    newFree.toNat = fp.toNat + 97 ∧ packedLen.toNat = 65 ∧
      3 ≤ aw2.toNat ∧ aw2.toNat * 32 < UInt256.size ∧
      3 ≤ awP4.toNat ∧ awP4.toNat * 32 < UInt256.size ∧
      3 ≤ aw3.toNat ∧ aw3.toNat * 32 < UInt256.size ∧
      3 ≤ aw5.toNat ∧ aw5.toNat * 32 < UInt256.size := by
  intro awP1 base fakeBase secretBase newFree packedLen awP2 awP3 awP4 aw1 aw2 aw3 aw4
    aw5
  have hbaseNat : base.toNat = fp.toNat + 32 := by
    dsimp [base]
    rw [uadd_toNat]
    have hlt : 32 + fp.toNat < UInt256.size := by omega
    change (32 + fp.toNat) % UInt256.size = fp.toNat + 32
    rw [Nat.mod_eq_of_lt hlt]
    omega
  have hfakeBaseNat : fakeBase.toNat = fp.toNat + 64 := by
    dsimp [fakeBase]
    rw [uadd_toNat, hbaseNat]
    have hlt : (fp.toNat + 32) + 32 < UInt256.size := by omega
    change (fp.toNat + 32 + 32) % UInt256.size = fp.toNat + 64
    rw [Nat.mod_eq_of_lt hlt]
  have hsecretBaseNat : secretBase.toNat = fp.toNat + 65 := by
    dsimp [secretBase]
    rw [uadd_toNat, hbaseNat]
    have hlt : (fp.toNat + 32) + 33 < UInt256.size := by omega
    change (fp.toNat + 32 + 33) % UInt256.size = fp.toNat + 65
    rw [Nat.mod_eq_of_lt hlt]
  have hnewFreeNat : newFree.toNat = fp.toNat + 97 := by
    dsimp [newFree]
    rw [uadd_toNat, hbaseNat]
    have hlt : 65 + (fp.toNat + 32) < UInt256.size := by omega
    change (65 + (fp.toNat + 32)) % UInt256.size = fp.toNat + 97
    rw [Nat.mod_eq_of_lt hlt]
    omega
  have hpackedLenNat : packedLen.toNat = 65 := by
    have hsub1 : (UInt256.sub newFree fp).toNat = 97 := by
      rw [usub_toNat]
      · rw [hnewFreeNat]
        omega
      · rw [hnewFreeNat]
        omega
    dsimp [packedLen]
    rw [usub_toNat]
    · rw [hsub1]
      change 97 - 32 = 65
      norm_num
    · rw [hsub1]
      change 32 ≤ 97
      norm_num
  have hawP1_ge : 3 ≤ awP1.toNat := by
    simpa [awP1] using reveal_aw_M_ge3
      (aw := aw) (off := (⟨64⟩ : UInt256)) (len := ⟨32⟩) haw
  have hawP1_small : awP1.toNat * 32 < UInt256.size := by
    simpa [awP1] using reveal_aw_M_small
      (aw := aw) (off := (⟨64⟩ : UInt256)) (len := ⟨32⟩) hawSmall
      (by decide)
  have hawP2_ge : 3 ≤ awP2.toNat := by
    simpa [awP2] using reveal_aw_M_ge3
      (aw := awP1) (off := base) (len := ⟨32⟩) hawP1_ge
  have hawP2_small : awP2.toNat * 32 < UInt256.size := by
    simpa [awP2] using reveal_aw_M_small
      (aw := awP1) (off := base) (len := ⟨32⟩) hawP1_small
      (by
        rw [hbaseNat]
        change fp.toNat + 32 + 32 + 31 < UInt256.size
        omega)
  have hawP3_ge : 3 ≤ awP3.toNat := by
    simpa [awP3] using reveal_aw_M_ge3
      (aw := awP2) (off := fakeBase) (len := ⟨32⟩) hawP2_ge
  have hawP3_small : awP3.toNat * 32 < UInt256.size := by
    simpa [awP3] using reveal_aw_M_small
      (aw := awP2) (off := fakeBase) (len := ⟨32⟩) hawP2_small
      (by
        rw [hfakeBaseNat]
        change fp.toNat + 64 + 32 + 31 < UInt256.size
        omega)
  have hawP4_ge : 3 ≤ awP4.toNat := by
    simpa [awP4] using reveal_aw_M_ge3
      (aw := awP3) (off := secretBase) (len := ⟨32⟩) hawP3_ge
  have hawP4_small : awP4.toNat * 32 < UInt256.size := by
    simpa [awP4] using reveal_aw_M_small
      (aw := awP3) (off := secretBase) (len := ⟨32⟩) hawP3_small
      (by
        rw [hsecretBaseNat]
        change fp.toNat + 65 + 32 + 31 < UInt256.size
        omega)
  have haw1_ge : 3 ≤ aw1.toNat := by
    simpa [aw1] using reveal_aw_M_ge3
      (aw := awP4) (off := (⟨64⟩ : UInt256)) (len := ⟨32⟩) hawP4_ge
  have haw1_small : aw1.toNat * 32 < UInt256.size := by
    simpa [aw1] using reveal_aw_M_small
      (aw := awP4) (off := (⟨64⟩ : UInt256)) (len := ⟨32⟩) hawP4_small
      (by decide)
  have haw2_ge : 3 ≤ aw2.toNat := by
    simpa [aw2] using reveal_aw_M_ge3
      (aw := aw1) (off := fp) (len := ⟨32⟩) haw1_ge
  have haw2_small : aw2.toNat * 32 < UInt256.size := by
    simpa [aw2] using reveal_aw_M_small
      (aw := aw1) (off := fp) (len := ⟨32⟩) haw1_small
      (by
        change fp.toNat + 32 + 31 < UInt256.size
        omega)
  have haw3_ge : 3 ≤ aw3.toNat := by
    simpa [aw3] using reveal_aw_M_ge3
      (aw := aw2) (off := (⟨64⟩ : UInt256)) (len := ⟨32⟩) haw2_ge
  have haw3_small : aw3.toNat * 32 < UInt256.size := by
    simpa [aw3] using reveal_aw_M_small
      (aw := aw2) (off := (⟨64⟩ : UInt256)) (len := ⟨32⟩) haw2_small
      (by decide)
  have haw4_ge : 3 ≤ aw4.toNat := by
    simpa [aw4] using reveal_aw_M_ge3
      (aw := aw3) (off := fp) (len := ⟨32⟩) haw3_ge
  have haw4_small : aw4.toNat * 32 < UInt256.size := by
    simpa [aw4] using reveal_aw_M_small
      (aw := aw3) (off := fp) (len := ⟨32⟩) haw3_small
      (by
        change fp.toNat + 32 + 31 < UInt256.size
        omega)
  have haw5_ge : 3 ≤ aw5.toNat := by
    simpa [aw5] using reveal_aw_M_ge3
      (aw := aw4) (off := base) (len := packedLen) haw4_ge
  have haw5_small : aw5.toNat * 32 < UInt256.size := by
    simpa [aw5] using reveal_aw_M_small
      (aw := aw4) (off := base) (len := packedLen) haw4_small
      (by
        rw [hbaseNat, hpackedLenNat]
        change fp.toNat + 32 + 65 + 31 < UInt256.size
        omega)
  exact ⟨hnewFreeNat, hpackedLenNat, haw2_ge, haw2_small, hawP4_ge, hawP4_small,
    haw3_ge, haw3_small, haw5_ge, haw5_small⟩

theorem encodePacked_bool (fake : Bool) :
    encodePackedValue? abiBool (.bool fake) = some [if fake then (1 : UInt8) else 0] := by
  cases fake <;> simp [encodePackedValue?, abiBool]

end Reasoning.Theory
