import Benchmarks.EAS.Attester.NestedABI

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.EAS.Attester

def BatchShape (cd : ByteArray) : Prop :=
  0 < arrayCount cd 4 ∧ arrayCount cd 36 = arrayCount cd 4

def BatchRowsValid (cd : ByteArray) : Prop :=
  ∀ i < arrayCount cd 36, RowValid cd (UInt256.ofNat (arrayDataNat cd 36)) i

theorem arrayReadLength {cd : ByteArray} {off : Nat}
    (h : ArrayHeadChecks cd (arrayHead cd off))
    (hoff : (calldataWord cd off).toNat ≤ solcMaxU64) (hsize : cd.size < UInt256.size) :
    readNat? (cd.toList.drop 4) (calldataWord cd off).toNat = some (arrayCount cd off) := by
  have hb := h.outer_bounds hoff hsize
  rw [readNat_drop4_at_eq_calldataWord _ (by omega), arrayCount, arrayHead_toNat hoff]

theorem decodeArrays_first_facts {cd : ByteArray} {elem : ABIType} {vs : Value × Value}
    (h : decodeArrays? elem cd = some vs) :
    ∃ schemas rows endOffset,
      vs = (.array schemas, .array rows) ∧
      schemas.length = arrayCount cd 4 ∧ rows.length = arrayCount cd 36 ∧
      decodeABIArrayDynamicElems? (.dynamicArray elem) (arrayCount cd 36)
        (cd.toList.drop 4) ((calldataWord cd 36).toNat + 32) =
          some (rows, endOffset) := by
  obtain ⟨end0, end1, hsize, hsign, hoff0, hoff1, hd0, hd1⟩ := decodeArrays_some_facts h
  obtain ⟨schemas, hs⟩ := decodeABIValue_dynamicArray_is_array hd0
  obtain ⟨rows, hr⟩ := decodeABIValue_dynamicArray_is_array hd1
  rw [hs] at hd0
  rw [hr] at hd1
  obtain ⟨len0, hread0, _hcap0, _hend0, _hbound0, hlen0⟩ :=
    decodeABIValue_dynamicArray_elem32_facts hd0
  obtain ⟨len1, hread1, _hcap1, he⟩ := (decodeDynamicArray_elems_iff (by rfl)).mp hd1
  have checks := decodeArrays_some_checks h
  rw [arrayReadLength checks.first hoff0 (lt_size_of_lt_sign hsign), Option.some.injEq] at hread0
  rw [arrayReadLength checks.second hoff1 (lt_size_of_lt_sign hsign), Option.some.injEq] at hread1
  subst len0
  subst len1
  have he' := he
  simp only [decodeABIArrayDynamicElems?] at he'
  have hstart := readNat?_some_length
    (arrayReadLength checks.second hoff1 (lt_size_of_lt_sign hsign))
  have hrows := decodeDynamicElems_head_bounds (values := rows)
    (by simpa only [Nat.add_zero] using hstart) he'
  exact ⟨schemas, rows, end1, Prod.ext hs hr, hlen0, hrows.2, he⟩

theorem decodedRows_lookup {cd : ByteArray} {elem : ElemType} {rows : List Value} {endOffset i :
    Nat}
    (hc : MultiHeadChecks cd) (hs : cd.size < 2 ^ 255)
    (hd : decodeABIArrayDynamicElems? (.dynamicArray (.elem elem)) (arrayCount cd 36)
      (cd.toList.drop 4) ((calldataWord cd 36).toNat + 32) = some (rows, endOffset))
    (hi : i < arrayCount cd 36) :
    ∃ values endInner, rows[i]? = some (.array values) ∧
      decodeABIValue? (.dynamicArray (.elem elem)) (cd.toList.drop 4)
        ((rowHead cd (UInt256.ofNat (arrayDataNat cd 36)) i).toNat - 4) =
          some (.array values, endInner) ∧
      NestedHeadChecks cd (UInt256.ofNat (arrayDataNat cd 36))
        (rowEntry (UInt256.ofNat (arrayDataNat cd 36)) i) ∧
      (rowLength cd (UInt256.ofNat (arrayDataNat cd 36)) i).toNat = values.length ∧
      (rowHead cd (UInt256.ofNat (arrayDataNat cd 36)) i).toNat + 32 +
        32 * values.length ≤ cd.size := by
  have hoff := uint64Bound_of_isZero_gt hc.secondOffset
  have hbound := hc.second.outer_bounds hoff (lt_size_of_lt_sign hs)
  change arrayDataNat cd 36 + 32 * arrayCount cd 36 ≤ cd.size at hbound
  simp only [decodeABIArrayDynamicElems?] at hd
  obtain ⟨relative, value, valueEnd, hr, hv, hlookup⟩ := decodeDynamicElems_lookup hd hi
  obtain ⟨values, hvalue⟩ := decodeABIValue_dynamicArray_is_array hv
  rw [hvalue] at hv hlookup
  simp only [Nat.add_zero] at hr
  have ha : 4 + ((calldataWord cd 36).toNat + 32) = arrayDataNat cd 36 := by
    unfold arrayDataNat; omega
  have hf := nestedArrayDecoded_facts hs (by rw [ha]; omega)
    (by rw [ha]; omega) hr hv
  rw [ha] at hf
  refine ⟨values, valueEnd, hlookup, ?_, hf.1, hf.2.1, hf.2.2.2⟩
  rw [hf.2.2.1, Nat.add_sub_cancel_left]
  exact hv

theorem decodeArrays_exists_of_rows {cd : ByteArray} {elem : ABIType}
    (helem : elem = bytes32 ∨ elem = uint256)
    (hc : MultiHeadChecks cd) (hsize : cd.size < UInt256.size) (hfour : 4 ≤ cd.size)
    (hrows : ∀ i < arrayCount cd 36,
      NestedHeadChecks cd (UInt256.ofNat (arrayDataNat cd 36))
        (rowEntry (UInt256.ofNat (arrayDataNat cd 36)) i) ∧
      rowLength cd (UInt256.ofNat (arrayDataNat cd 36)) i ≠ ⟨0⟩ ∧
      4 ≤ (rowHead cd (UInt256.ofNat (arrayDataNat cd 36)) i).toNat) :
    ∃ vs, decodeArrays? elem cd = some vs := by
  have hsign := hc.size_lt_sign hsize
  have hhead := hc.head_size hsize hfour
  have hoff0 := uint64Bound_of_isZero_gt hc.firstOffset
  have hoff1 := uint64Bound_of_isZero_gt hc.secondOffset
  have hcap0 := uint64Bound_of_isZero_gt hc.first.length
  have hcap1 := uint64Bound_of_isZero_gt hc.second.length
  have hbound0 := hc.first.outer_bounds hoff0 hsize
  have hbound1 := hc.second.outer_bounds hoff1 hsize
  change arrayDataNat cd 36 + 32 * arrayCount cd 36 ≤ cd.size at hbound1
  have hl : cd.toList.length = cd.size := by rw [byteArray_toList_eq, Array.length_toList]; rfl
  obtain ⟨schemas, hs, hlen⟩ := decodeABIValue_dynamicArray_bytes32_exists
    (arrayReadLength hc.first hoff0 hsize) (by exact Nat.not_lt.mpr hcap0)
    (by rw [List.length_drop, hl]; exact Nat.le_sub_of_add_le (by
          simpa only [arrayCount, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hbound0))
  have ha : 4 + ((calldataWord cd 36).toNat + 32) = arrayDataNat cd 36 := by
    unfold arrayDataNat; omega
  obtain ⟨rows, endOffset, hd⟩ := decodeDynamicElems_exists
    (n := arrayCount cd 36) (base := (calldataWord cd 36).toNat + 32) (cursor := 0)
    (headSize := arrayCount cd 36 * 32)
    (maxEnd := (calldataWord cd 36).toNat + 32 + arrayCount cd 36 * 32)
    (ty := .dynamicArray elem) (bytes := cd.toList.drop 4)
    (by
      intro i hi
      obtain ⟨hcheck, hne, hp⟩ := hrows i hi
      rw [← ha] at hcheck hne hp
      obtain ⟨relative, values, endInner, hr, hv, _hlen⟩ := nestedArray_decode_exists
        helem hsign (by rw [ha]; omega) (by rw [ha]; omega) hcheck hne hp
      exact ⟨relative, .array values, endInner, by simpa only [Nat.add_zero] using hr, hv⟩)
  have hd' : decodeABIValue? (.dynamicArray (.dynamicArray elem)) (cd.toList.drop 4)
      (calldataWord cd 36).toNat = some (.array rows, endOffset) := by
    apply (decodeDynamicArray_elems_iff (by rfl)).mpr
    exact ⟨arrayCount cd 36, arrayReadLength hc.second hoff1 hsize, hcap1,
      by simpa only [decodeABIArrayDynamicElems?] using hd⟩
  change decodeABIValue? bytes32Array (cd.toList.drop 4) (calldataWord cd 4).toNat =
    some (.array schemas, _) at hs
  refine ⟨(.array schemas, .array rows), ?_⟩
  simp only [decodeArrays?, show ¬ (cd.size < 68 ∨ 2 ^ 255 ≤ cd.size) by omega,
    show ¬ solcMaxU64 < (calldataWord cd 4).toNat by omega,
    show ¬ solcMaxU64 < (calldataWord cd 36).toNat by omega,
    if_false, hs, bind, Option.bind, hd']

theorem BatchRowsValid.decode_exists {cd sel : ByteArray} {elem : ABIType}
    (hrows : BatchRowsValid cd) (helem : elem = bytes32 ∨ elem = uint256)
    (hc : MultiHeadChecks cd) (hsize : cd.size < UInt256.size) (hfour : 4 ≤ cd.size)
    (hsel : cd.extract 0 4 = sel)
    (hprefix : ∀ j : Fin 4, 0 < fromByteArrayBigEndian (sel.extract j.val 4)) :
    ∃ vs, decodeArrays? elem cd = some vs := by
  apply decodeArrays_exists_of_rows helem hc hsize hfour
  have hbound := hc.second.outer_bounds (uint64Bound_of_isZero_gt hc.secondOffset) hsize
  change arrayDataNat cd 36 + 32 * arrayCount cd 36 ≤ cd.size at hbound
  intro i hi
  have hvalid := hrows i hi
  have hb : (UInt256.ofNat (arrayDataNat cd 36)).toNat + 32 ≤ cd.size := by
    rw [ulit_toNat' _ (by omega)]; omega
  have ht := hvalid.1.bounds (hc.size_lt_sign hsize) hb hvalid.2
  change (rowHead cd (UInt256.ofNat (arrayDataNat cd 36)) i).toNat + 32 +
    32 * (rowLength cd (UInt256.ofNat (arrayDataNat cd 36)) i).toNat ≤ cd.size at ht
  exact ⟨hvalid.1, hvalid.2, calldata_uint64_past_selector hsel hprefix
    (by omega) (uint64Bound_of_isZero_gt hvalid.1.length)⟩

end Benchmarks.EAS.Attester
