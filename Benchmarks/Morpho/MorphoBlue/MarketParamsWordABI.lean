import Benchmarks.Morpho.MorphoBlue.MarketParamsABI

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.Morpho.MorphoBlue
set_option maxRecDepth 1000

-- A static market tuple followed by a full-width word (the setFee signature).
theorem decodeCalldata_marketParams_uint256_eq (cd : ByteArray) (name arg : Ident) :
    decodeCalldata [name, arg] [marketParamsABIType, abiUInt256] cd =
      if cd.size < 196 ∨ 2 ^ 255 + 4 ≤ cd.size then none
      else (decodeScalarWords? marketParamsABIFields (cd.toList.drop 4) 0).bind (fun values ↦
        (decodeScalarWord? abiUInt256 (cd.toList.drop 4) 160).map (fun x ↦
          (((∅ : Store).insert name (.tuple values)).insert arg x.1))) := by
  have htlen : cd.toList.length = cd.size := by
    rw [byteArray_toList_eq, Array.length_toList]; rfl
  have hdyn : isDynamicABIType marketParamsABIType = false := rfl
  have hstatic : staticABIEncodedSize? marketParamsABIType = some 160 := rfl
  have hhead : abiTupleHeadSize? [marketParamsABIType, abiUInt256] = some 192 := by
    simp only [abiTupleHeadSize?, hdyn, hstatic, isDynamicABIType, abiUInt256,
      staticABIEncodedSize?, Bool.false_eq_true, ↓reduceIte, bind, Option.bind, pure]
  have htotal : solcTotalSizeDynamicGuard [marketParamsABIType, abiUInt256] = false := rfl
  unfold decodeCalldata
  simp only [List.length_drop, htlen, List.any_cons, List.any_nil, hdyn,
    show isDynamicABIType abiUInt256 = false from rfl, Bool.or_false, Bool.false_eq_true,
    false_and, ↓reduceIte, List.isEmpty_cons, and_self, true_and, htotal]
  by_cases h4 : cd.size < 4
  · simp only [h4, ↓reduceIte, show cd.size < 196 ∨ 2 ^ 255 + 4 ≤ cd.size by omega]
  · simp only [h4, ↓reduceIte]
    by_cases hbig : 2 ^ 255 ≤ cd.size - 4
    · simp only [hbig, ↓reduceIte, show cd.size < 196 ∨ 2 ^ 255 + 4 ≤ cd.size by omega]
    · simp only [hbig, ↓reduceIte, decodeCalldata.decodeArgs, hhead, bind, Option.bind,
        List.length_drop, htlen]
      by_cases hshort : cd.size - 4 < 192
      · simp only [hshort, ↓reduceIte, show cd.size < 196 ∨ 2 ^ 255 + 4 ≤ cd.size by omega]
      · simp only [hshort, ↓reduceIte, show ¬ (cd.size < 196 ∨ 2 ^ 255 + 4 ≤ cd.size) by omega,
          decodeABIValues?, hdyn, Bool.false_eq_true, ↓reduceIte, hstatic, bind, Option.bind, Nat.zero_add]
        rw [show marketParamsABIType = .tuple marketParamsABIFields from rfl,
          decodeABIValue_scalarTuple_eq (by decide)]
        cases hv : decodeScalarWords? marketParamsABIFields (cd.toList.drop 4) 0 with
        | none => rfl
        | some values =>
          simp only [Option.map, marketParamsABIFields, List.length_cons, List.length_nil, Nat.reduceAdd,
            Nat.reduceMul, bind, Option.bind]
          simp only [show isDynamicABIType abiUInt256 = false from rfl,
            show staticABIEncodedSize? abiUInt256 = some 32 from rfl,
            Bool.false_eq_true, ↓reduceIte, bind, Option.bind, Nat.reduceAdd]
          rw [decodeABIValue_scalarWord_eq (by decide)]
          have hx := decodeScalarWord_calldata_uint256 (cd := cd) (off := 160) (by omega) (by norm_num)
          simp only [decodeScalarWords?, hx, bind, Option.bind, pure, Option.map,
            decodeCalldata.insertValues, Nat.reduceAdd, ↓reduceIte]


theorem decodeCalldata_marketParams_uint256_ok {cd : ByteArray} {name arg : Ident}
    (hlen : 196 ≤ cd.size) (hbig : cd.size < 2 ^ 255 + 4)
    (hc : (marketParamsFromCalldata cd).Canonical) :
    decodeCalldata [name, arg] [marketParamsABIType, abiUInt256] cd =
      some ((((∅ : Store).insert name (marketParamsFromCalldata cd).value).insert arg
        (.int (Int.ofNat (calldataWord cd 164).toNat)))) := by
  rw [decodeCalldata_marketParams_uint256_eq, if_neg (by omega), decodeScalarWords_marketParams_ok (by omega) hc]
  simp only [Option.bind_some]
  rw [decodeScalarWord_calldata_uint256 (off := 160) hlen (by norm_num)]
  rfl

theorem decodeCalldata_marketParams_uint256_noncanonical {cd : ByteArray} {name arg : Ident}
    (hlen : 196 ≤ cd.size) (hc : ¬ (marketParamsFromCalldata cd).Canonical) :
    decodeCalldata [name, arg] [marketParamsABIType, abiUInt256] cd = none := by
  rw [decodeCalldata_marketParams_uint256_eq]
  split
  · rfl
  · rw [decodeScalarWords_marketParams_noncanonical (by omega) hc]; rfl

theorem decodeCalldata_marketParams_uint256_badSize {cd : ByteArray} {name arg : Ident}
    (hbad : cd.size < 196 ∨ 2 ^ 255 + 4 ≤ cd.size) :
    decodeCalldata [name, arg] [marketParamsABIType, abiUInt256] cd = none := by
  rw [decodeCalldata_marketParams_uint256_eq, if_pos hbad]

end Benchmarks.Morpho.MorphoBlue
