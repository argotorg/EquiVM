import Reasoning.ABI

open Solm ABI Ethereum Ethereum.EVM

namespace Reasoning.Theory

-- LIBRARY CANDIDATE: combine any two static 32-byte ABI decoders, including fixed bytes.
theorem decodeCalldata_twoWords_ok {cd : ByteArray} {x y : Ident} {s t : ABIType}
    {v w : Value} (hs : isDynamicABIType s = false) (ht : isDynamicABIType t = false)
    (hss : staticABIEncodedSize? s = some 32) (hts : staticABIEncodedSize? t = some 32)
    (hlen : 68 ≤ cd.size) (hhi : cd.size < 2 ^ 255 + 4)
    (hv : decodeABIValue? s (cd.toList.drop 4) 0 = some (v, 32))
    (hw : decodeABIValue? t (cd.toList.drop 4) 32 = some (w, 64)) :
    decodeCalldata [x, y] [s, t] cd = some (((∅ : Store).insert x v).insert y w) := by
  have hlenList : cd.toList.length = cd.size := by
    rw [byteArray_toList_eq, Array.length_toList]; rfl
  have hshort : ¬ cd.toList.length < 4 := by omega
  have hhuge : ¬ 2 ^ 255 ≤ (cd.toList.drop 4).length := by
    rw [List.length_drop, hlenList]; omega
  have hshortArgs : ¬ (cd.toList.drop 4).length < 64 := by
    rw [List.length_drop, hlenList]; omega
  simp only [decodeCalldata, hshort, ↓reduceIte, List.any_cons, hs, ht, List.any_nil,
    Bool.or_self, Bool.false_eq_true, false_and, List.isEmpty_cons, hhuge,
    solcTotalSizeDynamicGuard, decodeCalldata.decodeArgs, abiTupleHeadSize?,
    hss, hts, bind, Option.bind, Nat.add_zero, hshortArgs]
  simp only [decodeABIValues?, hs, ht, Bool.false_eq_true, ↓reduceIte, hss, hts,
    bind, Option.bind, Nat.zero_add, hv, hw, decodeCalldata.insertValues]
  rfl

-- LIBRARY CANDIDATE: the top-level ABI head-size guard, for arbitrary nonempty type lists.
theorem decodeCalldata_head_none_short {cd : ByteArray} {names : List Ident}
    {ty : ABIType} {types : List ABIType} {headSize : Nat}
    (hhead : abiTupleHeadSize? (ty :: types) = some headSize)
    (hshort : cd.size < 4 + headSize) :
    decodeCalldata names (ty :: types) cd = none := by
  have hlenList : cd.toList.length = cd.size := by
    rw [byteArray_toList_eq, Array.length_toList]; rfl
  simp only [decodeCalldata]
  split_ifs with h4 hdyn hhuge htotal
  · rfl
  · rfl
  · rfl
  · rfl
  · have hshortArgs : (cd.toList.drop 4).length < headSize := by
      rw [List.length_drop, hlenList]; omega
    simp only [decodeCalldata.decodeArgs, hhead, bind, Option.bind, hshortArgs, ↓reduceIte]

-- LIBRARY CANDIDATE: the signed argument-size guard, independent of the ABI types.
theorem decodeCalldata_nonempty_none_huge {cd : ByteArray} {names : List Ident}
    {ty : ABIType} {types : List ABIType} (hhi : 2 ^ 255 + 4 ≤ cd.size) :
    decodeCalldata names (ty :: types) cd = none := by
  have hlenList : cd.toList.length = cd.size := by
    rw [byteArray_toList_eq, Array.length_toList]; rfl
  have h4 : ¬ cd.toList.length < 4 := by omega
  have hargs : 2 ^ 255 ≤ (cd.toList.drop 4).length := by
    rw [List.length_drop, hlenList]; omega
  unfold decodeCalldata
  rw [if_neg h4]
  split_ifs <;> simp only [List.isEmpty_cons, hargs, and_self, ↓reduceIte]

-- LIBRARY CANDIDATE: express a decoded bytes32 argument using the corresponding EVM word.
theorem calldata_bytes32_value {cd : ByteArray} {off : Nat}
    (hlen : off + 32 ≤ cd.size) (hoff : off < 2 ^ 64) :
    Value.fixedBytes abiBytes32Width ((cd.toList.drop off).take 32) =
      wordBytes32Value (calldataWord cd off) := by
  have h32 : ((cd.toList.drop off).take 32).length = 32 := by
    have hlenList : cd.toList.length = cd.size := by
      rw [byteArray_toList_eq, Array.length_toList]; rfl
    rw [List.length_take, List.length_drop, hlenList]
    exact Nat.min_eq_left (by omega)
  have hword : ABI.bytesToWord ((cd.toList.drop off).take 32) = calldataWord cd off :=
    decode_word_at_eq cd off hlen hoff
  rw [wordBytes32Value, ← hword, toBytesBE_bytesToWord_of_length h32]

end Reasoning.Theory
