import Benchmarks.Safe.Common

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Safe

-- LIBRARY CANDIDATE: expose the guards and value decoder for a nonempty static ABI tuple.
theorem decodeStaticCalldata {cd : ByteArray} {names : List Solm.Ident}
    {ty : ABIType} {types : List ABIType} {headSize : ℕ}
    (hlong : 4 ≤ cd.size)
    (hdyn : (ty :: types).any isDynamicABIType = false)
    (htotal : solcTotalSizeDynamicGuard (ty :: types) = false)
    (hhead : abiTupleHeadSize? (ty :: types) = some headSize) :
    decodeCalldata names (ty :: types) cd =
      if 2 ^ 255 ≤ cd.size - 4 then none
      else if cd.size - 4 < headSize then none
      else (do
        let (values, _) ← decodeABIValues? (ty :: types) (cd.toList.drop 4) 0 0 headSize headSize
        decodeCalldata.insertValues names values ∅) := by
  have hlist : cd.toList.length = cd.size := by
    rw [byteArray_toList_eq, Array.length_toList]; rfl
  unfold decodeCalldata
  simp only [hlist, if_neg (by omega : ¬cd.size < 4), hdyn, Bool.false_eq_true,
    false_and, if_false, List.isEmpty_cons, true_and, List.length_drop, htotal,
    decodeCalldata.decodeArgs, hhead, bind, Option.bind]
  by_cases hbig : 2 ^ 255 ≤ cd.size - 4
  · simp only [hbig, if_true]
  · simp only [hbig, if_false]
    by_cases hshort : cd.size - 4 < headSize
    · simp [hshort]
    · simp only [hshort, if_false]
      cases decodeABIValues? (ty :: types) (cd.toList.drop 4) 0 0 headSize headSize with
      | none => rfl
      | some v =>
          rcases v with ⟨values, endOffset⟩
          simp only []
          cases decodeCalldata.insertValues names values ∅ <;> rfl

theorem decodeAddressBytes32Guard {cd : ByteArray} {x y : Solm.Ident}
    (hlong : 4 ≤ cd.size) :
    decodeCalldata [x, y] [abiAddress, abiBytes32] cd =
      if 2 ^ 255 ≤ cd.size - 4 then none
      else if cd.size - 4 < 64 then none
      else (do
        let (values, _) ← decodeABIValues? [abiAddress, abiBytes32]
          (cd.toList.drop 4) 0 0 64 64
        decodeCalldata.insertValues [x, y] values ∅) :=
  decodeStaticCalldata hlong (by decide) (by decide)
    (by simp [abiTupleHeadSize?, staticABIEncodedSize?, isDynamicABIType,
      abiBytes32, abiBytes32Width, bind, Option.bind])

-- LIBRARY CANDIDATE: modern address/bytes32 tuple decoding, including malformed branches.
theorem decodeAddressBytes32 {cd : ByteArray} {x y : Solm.Ident}
    (hlen : 68 ≤ cd.size) (hbig : cd.size < 2 ^ 255 + 4)
    (hcanon : (calldataWord cd 4).toNat < EVM.addressModulus) :
    decodeCalldata [x, y] [abiAddress, abiBytes32] cd =
      some (((∅ : Store).insert x (.address (AccountAddress.ofNat (calldataWord cd
        4).toNat))).insert
        y (wordBytes32Value (calldataWord cd 36))) := by
  rw [decodeAddressBytes32Guard (by omega), if_neg (by omega), if_neg (by omega)]
  have hlist : cd.toList.length = cd.size := by
    rw [byteArray_toList_eq, Array.length_toList]; rfl
  have htake4 : ((cd.toList.drop 4).take 32).length = 32 := by
    simp only [List.length_take, List.length_drop, hlist]; omega
  have htake36 : (((cd.toList.drop 4).drop 32).take 32).length = 32 := by
    simp only [List.length_take, List.length_drop, hlist]; omega
  have hword4 : ABI.bytesToWord ((cd.toList.drop 4).take 32) = calldataWord cd 4 :=
    decode_word_at_eq_any cd 4 (by omega)
  have hword36 : ABI.bytesToWord ((cd.toList.drop 36).take 32) = calldataWord cd 36 :=
    decode_word_at_eq_any cd 36 hlen
  have hbytes : EVM.Word.toBytesBE (calldataWord cd 36) = (cd.toList.drop 36).take 32 := by
    rw [← hword36]
    apply toBytesBE_bytesToWord_of_length
    simp only [List.length_take, List.length_drop, hlist]; omega
  simp only [decodeABIValues?, isDynamicABIType, Bool.false_eq_true, if_false,
    staticABIEncodedSize?, bind, Option.bind, Nat.zero_add]
  rw [decodeABIValue_address_ok (start := 0) (by simpa using htake4)
    (by simpa only [List.drop_zero, hword4] using hcanon)]
  rw [decodeABIValue_bytes32_ok (start := 32) htake36]
  simp [decodeCalldata.insertValues, wordBytes32Value, hbytes, hword4, List.drop_drop]

theorem decodeAddressBytes32Noncanon {cd : ByteArray} {x y : Solm.Ident}
    (hlen : 68 ≤ cd.size) (hbig : cd.size < 2 ^ 255 + 4)
    (hcanon : ¬ (calldataWord cd 4).toNat < EVM.addressModulus) :
    decodeCalldata [x, y] [abiAddress, abiBytes32] cd = none := by
  rw [decodeAddressBytes32Guard (by omega), if_neg (by omega), if_neg (by omega)]
  have hlist : cd.toList.length = cd.size := by
    rw [byteArray_toList_eq, Array.length_toList]; rfl
  have htake4 : ((cd.toList.drop 4).take 32).length = 32 := by
    simp only [List.length_take, List.length_drop, hlist]; omega
  have hword4 : ABI.bytesToWord ((cd.toList.drop 4).take 32) = calldataWord cd 4 :=
    decode_word_at_eq_any cd 4 (by omega)
  simp only [decodeABIValues?, isDynamicABIType, Bool.false_eq_true, if_false,
    staticABIEncodedSize?, bind, Option.bind, Nat.zero_add]
  rw [decodeABIValue_address_none_noncanon (start := 0) (by simpa using htake4)
    (by simpa only [List.drop_zero, hword4] using hcanon)]
theorem decodeAddressBytes32Short {cd : ByteArray} {x y : Solm.Ident}
    (hlong : 4 ≤ cd.size) (hshort : cd.size < 68) :
    decodeCalldata [x, y] [abiAddress, abiBytes32] cd = none := by
  rw [decodeAddressBytes32Guard hlong, if_neg (by omega), if_pos (by omega)]

theorem decodeAddressBytes32Huge {cd : ByteArray} {x y : Solm.Ident}
    (hbig : 2 ^ 255 + 4 ≤ cd.size) :
    decodeCalldata [x, y] [abiAddress, abiBytes32] cd = none := by
  rw [decodeAddressBytes32Guard (by omega), if_pos (by omega)]

end Benchmarks.Safe
