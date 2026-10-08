import Benchmarks.EAS.Attester.ArrayABI
import Benchmarks.EAS.Attester.NestedPrefix

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Reasoning.Theory

-- LIBRARY CANDIDATE: expose the shared dynamic-array element decoder.
theorem decodeDynamicArray_elems_iff {ty : ABIType} {bytes : List UInt8}
    {start endOffset : Nat} {values : List Value} (hdyn : isDynamicABIType ty = true) :
    decodeABIValue? (.dynamicArray ty) bytes start .modern = some (.array values, endOffset) ↔
      ∃ len, readNat? bytes start = some len ∧ len ≤ solcMaxU64 ∧
        decodeABIArrayDynamicElems? ty len bytes (start + 32) .modern = some (values,
            endOffset) := by
  have hbool : ty ≠ .elem .bool := by intro heq; subst ty; contradiction
  rw [decodeABIValue?]
  cases hr : readNat? bytes start with
  | none => simp [hr]
  | some len =>
      simp only [hr, solcMaxLen_modern, hbool, hdyn, if_true, bind, Option.bind,
        Option.some.injEq, exists_eq_left']
      by_cases hl : solcMaxU64 < len
      · simp [hl, show ¬ len ≤ solcMaxU64 by omega]
      · simp only [hl, if_false, show len ≤ solcMaxU64 by omega, true_and]
        cases he : decodeABIArrayDynamicElems? ty len bytes (start + 32) .modern with
        | none => simp
        | some value =>
            rcases value with ⟨vs, e⟩
            simp only [Option.bind_some, Option.some.injEq, Prod.mk.injEq, Value.array.injEq]

-- LIBRARY CANDIDATE: each decoded nested-array element retains its offset and value witness.
theorem decodeDynamicElems_lookup {ty : ABIType} {bytes : List UInt8}
    {n base cursor headSize maxEnd endOffset i : Nat} {values : List Value}
    (h : decodeABIArrayDynamicElemsFrom? ty n bytes base cursor headSize maxEnd .modern =
      some (values, endOffset)) (hi : i < n) :
    ∃ relative value valueEnd,
      readNat? bytes (base + cursor + 32 * i) = some relative ∧
      decodeABIValue? ty bytes (solcDynamicArrayElementTarget .modern base relative) .modern =
        some (value, valueEnd) ∧ values[i]? = some value := by
  induction n generalizing cursor maxEnd values endOffset i with
  | zero => omega
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
                  rcases h with ⟨rfl, rfl⟩
                  cases i with
                  | zero => exact ⟨relative, value.1, value.2, by simpa using hr, hv, rfl⟩
                  | succ i =>
                      obtain ⟨rel, val, vend, hread, hval, hlookup⟩ := ih (i := i) ht (by omega)
                      exact ⟨rel, val, vend, by
                        simpa only [show base + cursor + 32 * (i + 1) =
                          base + (cursor + 32) + 32 * i by omega] using hread,
                        hval, hlookup⟩

-- LIBRARY CANDIDATE: decoding a finite offset table succeeds when every pointed-to value decodes.
theorem decodeDynamicElems_exists {ty : ABIType} {bytes : List UInt8}
    {n base cursor headSize maxEnd : Nat}
    (h : ∀ i < n, ∃ relative value valueEnd,
      readNat? bytes (base + cursor + 32 * i) = some relative ∧
      decodeABIValue? ty bytes (solcDynamicArrayElementTarget .modern base relative) .modern =
        some (value, valueEnd)) :
    ∃ values endOffset, decodeABIArrayDynamicElemsFrom? ty n bytes base cursor headSize maxEnd
        .modern =
      some (values, endOffset) := by
  induction n generalizing cursor maxEnd with
  | zero => exact ⟨[], maxEnd, by simp only [decodeABIArrayDynamicElemsFrom?]⟩
  | succ n ih =>
      obtain ⟨relative, value, valueEnd, hr, hv⟩ := h 0 (by omega)
      simp only [Nat.mul_zero, Nat.add_zero] at hr
      obtain ⟨values, endOffset, ht⟩ := ih (cursor := cursor + 32) (maxEnd := max maxEnd valueEnd)
        (by intro i hi
            simpa only [show base + cursor + 32 * (i + 1) =
              base + (cursor + 32) + 32 * i by omega] using h (i + 1) (by omega))
      refine ⟨value :: values, endOffset, ?_⟩
      rw [decodeABIArrayDynamicElemsFrom?]
      simp only [hr, solcRejectsDynamicArrayElementOffset_modern, Bool.false_eq_true,
        if_false, bind, Option.bind, hv, ht]

-- LIBRARY CANDIDATE: restoring a stripped selector commutes with a wrapped ABI target in range.
theorem nestedTarget_add4 {base : Nat} {relative : UInt256}
    (hb : 4 + base < UInt256.size)
    (ht : 4 + solcDynamicArrayElementTarget .modern base relative.toNat < UInt256.size) :
    (UInt256.ofNat (4 + base) + relative).toNat =
      4 + solcDynamicArrayElementTarget .modern base relative.toNat := by
  rw [uadd_toNat, ulit_toNat' _ hb]
  simp only [solcDynamicArrayElementTarget, EVM.wordModulus, EVM.twoPow] at ht ⊢
  rw [show UInt256.size = 2 ^ 256 by norm_num [UInt256.size]] at hb ht ⊢
  have hr : relative.toNat < 2 ^ 256 := relative.val.isLt
  omega

theorem nestedTarget_sub4 {base : Nat} {relative : UInt256}
    (hb : 4 + base < UInt256.size)
    (ht : 4 ≤ (UInt256.ofNat (4 + base) + relative).toNat) :
    solcDynamicArrayElementTarget .modern base relative.toNat =
      (UInt256.ofNat (4 + base) + relative).toNat - 4 := by
  have he := uadd_toNat (UInt256.ofNat (4 + base)) relative
  rw [ulit_toNat' _ hb] at he
  simp only [solcDynamicArrayElementTarget, EVM.wordModulus, EVM.twoPow]
  rw [show UInt256.size = 2 ^ 256 by norm_num [UInt256.size]] at hb he
  have hr : relative.toNat < 2 ^ 256 := relative.val.isLt
  omega

end Reasoning.Theory

namespace Benchmarks.EAS.Attester

theorem rowEntry_toNat {base i : Nat} (h : base + 32 * i < UInt256.size) :
    (rowEntry (UInt256.ofNat base) i).toNat = base + 32 * i := by
  rw [rowEntry, ofNat_mul_words, ofNat_add_words, ulit_toNat' _ h]

theorem nestedArrayDecoded_facts {cd : ByteArray} {elem : ElemType}
    {base i relative endOffset : Nat} {values : List Value}
    (hs : cd.size < 2 ^ 255) (hb : 4 + base + 32 ≤ cd.size)
    (he : 4 + base + 32 * i + 32 ≤ cd.size)
    (hr : readNat? (cd.toList.drop 4) (base + 32 * i) = some relative)
    (hd : decodeABIValue? (.dynamicArray (.elem elem)) (cd.toList.drop 4)
      (solcDynamicArrayElementTarget .modern base relative) = some (.array values, endOffset)) :
    NestedHeadChecks cd (UInt256.ofNat (4 + base)) (rowEntry (UInt256.ofNat (4 + base)) i) ∧
      (rowLength cd (UInt256.ofNat (4 + base)) i).toNat = values.length ∧
      (rowHead cd (UInt256.ofNat (4 + base)) i).toNat =
        4 + solcDynamicArrayElementTarget .modern base relative ∧
      (rowHead cd (UInt256.ofNat (4 + base)) i).toNat + 32 + 32 * values.length ≤ cd.size := by
  have hsize := lt_size_of_lt_sign hs
  have hl : cd.toList.length = cd.size := by rw [byteArray_toList_eq, Array.length_toList]; rfl
  obtain ⟨len, hread, hcap, hend, hbound, hlength⟩ := decodeABIValue_dynamicArray_elem32_facts hd
  rw [hend, List.length_drop, hl] at hbound
  have hr' := readNat_drop4_at_eq_calldataWord (cd := cd) (base + 32 * i) (by omega)
  rw [hr', Option.some.injEq] at hr
  have heq : (rowEntry (UInt256.ofNat (4 + base)) i).toNat = 4 + (base + 32 * i) := by
    rw [rowEntry_toNat (by omega)]; omega
  have htarget : (rowHead cd (UInt256.ofNat (4 + base)) i).toNat =
      4 + solcDynamicArrayElementTarget .modern base relative := by
    unfold rowHead nestedHead
    rw [heq, nestedTarget_add4 (by omega) (by rw [hr]; omega), hr]
  have hread' := readNat_drop4_at_eq_calldataWord (cd := cd)
    (solcDynamicArrayElementTarget .modern base relative) (by omega)
  rw [hread', Option.some.injEq] at hread
  have hlen : (rowLength cd (UInt256.ofNat (4 + base)) i).toNat = len := by
    rw [rowLength, htarget]; exact hread
  refine ⟨?_, hlen.trans hlength.symm, htarget, ?_⟩
  · apply NestedHeadChecks.of_bounds hs
      (by rw [ulit_toNat' _ (by omega)]; omega)
    · change (rowLength cd (UInt256.ofNat (4 + base)) i).toNat ≤ solcMaxU64
      rw [hlen]; omega
    · change (rowHead cd (UInt256.ofNat (4 + base)) i).toNat + 32 +
        32 * (rowLength cd (UInt256.ofNat (4 + base)) i).toNat ≤ cd.size
      rw [htarget, hlen]; omega
  · rw [htarget, hlength]; omega

theorem nestedArray_decode_exists {cd : ByteArray} {elem : ABIType} {base i : Nat}
    (helem : elem = bytes32 ∨ elem = uint256)
    (hs : cd.size < 2 ^ 255) (hb : 4 + base + 32 ≤ cd.size)
    (he : 4 + base + 32 * i + 32 ≤ cd.size)
    (hc : NestedHeadChecks cd (UInt256.ofNat (4 + base)) (rowEntry (UInt256.ofNat (4 + base)) i))
    (hne : rowLength cd (UInt256.ofNat (4 + base)) i ≠ ⟨0⟩)
    (hp : 4 ≤ (rowHead cd (UInt256.ofNat (4 + base)) i).toNat) :
    ∃ relative values endOffset,
      readNat? (cd.toList.drop 4) (base + 32 * i) = some relative ∧
      decodeABIValue? (.dynamicArray elem) (cd.toList.drop 4)
        (solcDynamicArrayElementTarget .modern base relative) = some (.array values, endOffset) ∧
      values.length = (rowLength cd (UInt256.ofNat (4 + base)) i).toNat := by
  have hsize := lt_size_of_lt_sign hs
  have hbf : 4 + base < UInt256.size := by omega
  have hl : cd.toList.length = cd.size := by rw [byteArray_toList_eq, Array.length_toList]; rfl
  have hbound := hc.bounds hs (by rw [ulit_toNat' _ hbf]; exact hb) hne
  change (rowHead cd (UInt256.ofNat (4 + base)) i).toNat + 32 +
    32 * (rowLength cd (UInt256.ofNat (4 + base)) i).toNat ≤ cd.size at hbound
  have hcap := uint64Bound_of_isZero_gt hc.length
  change (rowLength cd (UInt256.ofNat (4 + base)) i).toNat ≤ solcMaxU64 at hcap
  have heq : (rowEntry (UInt256.ofNat (4 + base)) i).toNat = 4 + (base + 32 * i) := by
    rw [rowEntry_toNat (by omega)]; omega
  let relative := (calldataWord cd (4 + (base + 32 * i))).toNat
  have hr := readNat_drop4_at_eq_calldataWord (cd := cd) (base + 32 * i) (by omega)
  have htarget : solcDynamicArrayElementTarget .modern base relative =
      (rowHead cd (UInt256.ofNat (4 + base)) i).toNat - 4 := by
    unfold rowHead nestedHead
    rw [heq]
    exact nestedTarget_sub4 hbf (by simpa only [rowHead, nestedHead, heq] using hp)
  have hpadd : 4 + ((rowHead cd (UInt256.ofNat (4 + base)) i).toNat - 4) =
      (rowHead cd (UInt256.ofNat (4 + base)) i).toNat := by omega
  have hread := readNat_drop4_at_eq_calldataWord (cd := cd)
    ((rowHead cd (UInt256.ofNat (4 + base)) i).toNat - 4) (by omega)
  rw [hpadd] at hread
  have hend : (rowHead cd (UInt256.ofNat (4 + base)) i).toNat - 4 + 32 +
      32 * (rowLength cd (UInt256.ofNat (4 + base)) i).toNat ≤ (cd.toList.drop 4).length := by
    rw [List.length_drop, hl]; omega
  have hv : ∃ values, decodeABIValue? (.dynamicArray elem) (cd.toList.drop 4)
      ((rowHead cd (UInt256.ofNat (4 + base)) i).toNat - 4) =
        some (.array values, (rowHead cd (UInt256.ofNat (4 + base)) i).toNat - 4 + 32 +
          32 * (rowLength cd (UInt256.ofNat (4 + base)) i).toNat) ∧
      values.length = (rowLength cd (UInt256.ofNat (4 + base)) i).toNat := by
    rcases helem with rfl | rfl
    · exact decodeABIValue_dynamicArray_bytes32_exists hread (by omega) hend
    · exact decodeABIValue_dynamicArray_uint256_exists hread (by omega) hend
  obtain ⟨values, hd, hvlen⟩ := hv
  exact ⟨relative, values, _, hr, by rw [htarget]; exact hd, hvlen⟩

end Benchmarks.EAS.Attester
