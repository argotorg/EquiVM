import Benchmarks.EAS.Attester.ArrayBounds

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Reasoning.Theory

-- LIBRARY CANDIDATE: successful dynamic-array decoding consumes every offset word.
theorem decodeDynamicElems_head_bounds {ty : ABIType} {n : Nat} {bytes : List UInt8}
    {base cursor headSize maxEnd endOffset : Nat} {values : List Value}
    (hbase : base + cursor ≤ bytes.length)
    (h : decodeABIArrayDynamicElemsFrom? ty n bytes base cursor headSize maxEnd .modern =
      some (values, endOffset)) :
    base + cursor + 32 * n ≤ bytes.length ∧ values.length = n := by
  induction n generalizing cursor maxEnd values endOffset with
  | zero =>
      simp only [decodeABIArrayDynamicElemsFrom?, Option.some.injEq, Prod.mk.injEq] at h
      rcases h with ⟨rfl, rfl⟩
      exact ⟨by omega, rfl⟩
  | succ n ih =>
      rw [decodeABIArrayDynamicElemsFrom?] at h
      cases hr : readNat? bytes (base + cursor) with
      | none => simp [hr] at h
      | some relative =>
          simp only [hr, solcRejectsDynamicArrayElementOffset_modern, Bool.false_eq_true,
            if_false, bind, Option.bind] at h
          cases hv : decodeABIValue? ty bytes (solcDynamicArrayElementTarget .modern base relative)
              .modern with
          | none => simp [hv] at h
          | some value =>
              simp only [hv, Option.bind_some] at h
              cases ht : decodeABIArrayDynamicElemsFrom? ty n bytes base (cursor + 32)
                  headSize (max maxEnd value.2) .modern with
              | none => simp [ht] at h
              | some tail =>
                  simp only [ht, Option.bind_some, Option.some.injEq, Prod.mk.injEq] at h
                  have hb := readNat?_some_length hr
                  have hh := ih (cursor := cursor + 32) (values := tail.1)
                    (endOffset := tail.2) (by omega) ht
                  constructor
                  · omega
                  · rw [← h.1, List.length_cons, hh.2]

-- LIBRARY CANDIDATE: bounds and length of the offset table of a decoded nested array.
theorem decodeDynamicArray_head_facts {ty : ABIType} {bytes : List UInt8}
    {start endOffset : Nat} {value : Value}
    (hdyn : isDynamicABIType ty = true)
    (h : decodeABIValue? (.dynamicArray ty) bytes start .modern = some (value, endOffset)) :
    ∃ len values, readNat? bytes start = some len ∧ len ≤ solcMaxU64 ∧
      value = .array values ∧ values.length = len ∧ start + 32 + 32 * len ≤ bytes.length := by
  have hbool : ty ≠ .elem .bool := by intro heq; subst ty; contradiction
  rw [decodeABIValue?] at h
  cases hr : readNat? bytes start with
  | none => simp [hr] at h
  | some len =>
      by_cases hmax : solcMaxU64 < len
      · simp [hr, hmax] at h
      simp only [hr, solcMaxLen_modern, hmax, if_false, hbool, hdyn, if_true,
        bind, Option.bind] at h
      cases he : decodeABIArrayDynamicElems? ty len bytes (start + 32) .modern with
      | none => simp [he] at h
      | some elems =>
          simp only [he, Option.bind_some, Option.some.injEq, Prod.mk.injEq] at h
          simp only [decodeABIArrayDynamicElems?] at he
          have hb := decodeDynamicElems_head_bounds (values := elems.1) (endOffset := elems.2)
            (by simpa using readNat?_some_length hr) he
          exact ⟨len, elems.1, rfl, by omega, h.1.symm, hb.2, by simpa using hb.1⟩

end Reasoning.Theory

namespace Benchmarks.EAS.Attester

def decodeArrays? (elem : ABIType) (cd : ByteArray) : Option (Value × Value) := do
  if cd.size < 68 ∨ 2 ^ 255 ≤ cd.size then none else do
  let off0 := (calldataWord cd 4).toNat
  let off1 := (calldataWord cd 36).toNat
  if solcMaxU64 < off0 then none else do
  let first ← decodeABIValue? bytes32Array (cd.toList.drop 4) off0
  if solcMaxU64 < off1 then none else do
  let second ← decodeABIValue? (.dynamicArray (.dynamicArray elem)) (cd.toList.drop 4) off1
  some (first.1, second.1)

theorem decodeCalldata_arrays_eq (elem : ABIType) (x y : Ident) (cd : ByteArray) :
    decodeCalldataWithMode .modern [x, y] [bytes32Array, .dynamicArray (.dynamicArray elem)] cd =
      (decodeArrays? elem cd).map (fun vs ↦ ((∅ : Store).insert x vs.1).insert y vs.2) := by
  have hl : cd.toList.length = cd.size := by rw [byteArray_toList_eq, Array.length_toList]; rfl
  change decodeCalldata [x, y] [bytes32Array, .dynamicArray (.dynamicArray elem)] cd = _
  by_cases hs : cd.size < 68
  · rw [decodeCalldata_head_none_short (types := [.dynamicArray (.dynamicArray elem)])
      (ty := bytes32Array) (headSize := 64)
      (by simp [abiTupleHeadSize?, bytes32Array, isDynamicABIType]) hs]
    simp only [decodeArrays?, hs, true_or, if_true, Option.map_none]
  by_cases hh : 2 ^ 255 ≤ cd.size
  · simp only [decodeCalldata, hl, show ¬ cd.size < 4 by omega, if_false,
      bytes32Array, isDynamicABIType, List.any_cons, Bool.true_or, true_and, hh, if_true,
      decodeArrays?, or_true, Option.map_none]
  have hr0 := readNat_drop4_at_eq_calldataWord (cd := cd) 0 (by omega)
  have hr1 := readNat_drop4_at_eq_calldataWord (cd := cd) 32 (by omega)
  simp only [Nat.add_zero, Nat.reduceAdd] at hr0 hr1
  simp only [decodeCalldataWithMode, decodeCalldata, hl, show ¬ cd.size < 4 by omega,
    if_false, bytes32Array, isDynamicABIType, List.any_cons, Bool.true_or, and_self,
    hh, and_false, List.isEmpty_cons, Bool.false_eq_true, List.length_drop,
    show ¬ 2 ^ 255 ≤ cd.size - 4 by omega, solcTotalSizeDynamicGuard,
    decodeCalldata.decodeArgs, abiTupleHeadSize?, bind, Option.bind,
    show ¬ cd.size - 4 < 64 by omega, decodeABIValues?, Nat.zero_add,
    Nat.reduceAdd, hr0, hr1, solcMaxLen_modern, if_true,
    decodeArrays?, hs, false_or, decodeCalldata.insertValues]
  by_cases h0 : solcMaxU64 < (calldataWord cd 4).toNat
  · simp [h0]
  simp only [h0, if_false]
  cases hv0 : decodeABIValue? (.dynamicArray bytes32) (cd.toList.drop 4) (calldataWord cd 4).toNat
  · simp [hv0]
  · simp only [hv0]
    by_cases h1 : solcMaxU64 < (calldataWord cd 36).toNat
    · simp [h1]
    simp only [h1, if_false]
    cases hv1 : decodeABIValue? (.dynamicArray (.dynamicArray elem))
        (cd.toList.drop 4) (calldataWord cd 36).toNat <;>
      simp [hv1, decodeCalldata.insertValues]

theorem decodeArrays_some_facts {elem : ABIType} {cd : ByteArray} {values : Value × Value}
    (h : decodeArrays? elem cd = some values) :
    ∃ end0 end1, 68 ≤ cd.size ∧ cd.size < 2 ^ 255 ∧
      (calldataWord cd 4).toNat ≤ solcMaxU64 ∧ (calldataWord cd 36).toNat ≤ solcMaxU64 ∧
      decodeABIValue? bytes32Array (cd.toList.drop 4) (calldataWord cd 4).toNat = some (values.1,
          end0) ∧
      decodeABIValue? (.dynamicArray (.dynamicArray elem)) (cd.toList.drop 4)
        (calldataWord cd 36).toNat = some (values.2, end1) := by
  unfold decodeArrays? at h
  dsimp only at h
  by_cases hs : cd.size < 68 ∨ 2 ^ 255 ≤ cd.size
  · simp only [hs, if_true, Option.noConfusion] at h; cases h
  by_cases h0 : solcMaxU64 < (calldataWord cd 4).toNat
  · simp only [hs, h0, if_false, if_true, Option.noConfusion] at h; cases h
  simp only [hs, h0, if_false] at h
  cases hv0 : decodeABIValue? bytes32Array (cd.toList.drop 4) (calldataWord cd 4).toNat with
  | none => simp [hv0] at h
  | some first =>
      simp only [hv0, bind, Option.bind] at h
      by_cases h1 : solcMaxU64 < (calldataWord cd 36).toNat
      · simp only [h1, if_true, Option.noConfusion] at h; cases h
      simp only [h1, if_false] at h
      cases hv1 : decodeABIValue? (.dynamicArray (.dynamicArray elem)) (cd.toList.drop 4)
          (calldataWord cd 36).toNat with
      | none => simp [hv1] at h
      | some second =>
          simp only [hv1, bind, Option.bind, Option.some.injEq] at h
          subst values
          exact ⟨first.2, second.2, by omega, by omega, by omega, by omega, rfl, rfl⟩

theorem arrayHeadChecks_of_readBound {cd : ByteArray} {off len : Nat}
    (hsize : cd.size < 2 ^ 255) (hoff : (calldataWord cd off).toNat ≤ solcMaxU64)
    (hread : readNat? (cd.toList.drop 4) (calldataWord cd off).toNat = some len)
    (hlen : len ≤ solcMaxU64)
    (hbound : (calldataWord cd off).toNat + 32 + 32 * len ≤ (cd.toList.drop 4).length) :
    ArrayHeadChecks cd (arrayHead cd off) := by
  have hl : cd.toList.length = cd.size := by rw [byteArray_toList_eq, Array.length_toList]; rfl
  have hreadbound := readNat?_some_length hread
  rw [List.length_drop, hl] at hbound hreadbound
  have hr := readNat_drop4_at_eq_calldataWord (cd := cd) (calldataWord cd off).toNat (by omega)
  rw [hr, Option.some.injEq] at hread
  have hw : (calldataWord cd (arrayHead cd off).toNat).toNat = len := by
    rw [arrayHead_toNat hoff]; exact hread
  exact ArrayHeadChecks.of_bounds hsize (by rw [hw]; exact hlen)
    (by rw [hw, arrayHead_toNat hoff]; omega)

theorem decodeArrays_some_checks {elem : ABIType} {cd : ByteArray} {values : Value × Value}
    (h : decodeArrays? elem cd = some values) : MultiHeadChecks cd := by
  obtain ⟨end0, end1, hsize, hhi, hoff0, hoff1, hd0, hd1⟩ := decodeArrays_some_facts h
  obtain ⟨schemas, hschemas⟩ := decodeABIValue_dynamicArray_is_array hd0
  rw [hschemas] at hd0
  obtain ⟨len0, hr0, hb0, hend0, hbound0, hlength0⟩ := decodeABIValue_dynamicArray_elem32_facts hd0
  obtain ⟨len1, inputs, hr1, hb1, _hinputs, _hlength1, hbound1⟩ :=
    decodeDynamicArray_head_facts (by rfl) hd1
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · change UInt256.isZero (UInt256.slt (UInt256.sub (UInt256.ofNat cd.size) ⟨4⟩) ⟨64⟩) ≠ ⟨0⟩
    rw [solcDecodeLenCheckOk_4_64 hsize (by omega) (lt_size_of_lt_sign hhi)]; decide
  · rw [ugt_zero hoff0]; decide
  · exact arrayHeadChecks_of_readBound hhi hoff0 hr0 (Nat.le_of_not_gt hb0) (hend0 ▸ hbound0)
  · rw [ugt_zero hoff1]; decide
  · exact arrayHeadChecks_of_readBound hhi hoff1 hr1 hb1 hbound1

theorem decodeCalldata_arrays_none_of_bad_heads (elem : ABIType) (x y : Ident) (cd : ByteArray)
    (h : ¬ MultiHeadChecks cd) :
    decodeCalldataWithMode .modern [x, y] [bytes32Array,
        .dynamicArray (.dynamicArray elem)] cd = none := by
  rw [decodeCalldata_arrays_eq]
  cases hd : decodeArrays? elem cd with
  | none => rfl
  | some values => exact False.elim (h (decodeArrays_some_checks hd))

end Benchmarks.EAS.Attester
