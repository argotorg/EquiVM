import Benchmarks.EAS.Attester.MultiRevokeSourceLoop
import Benchmarks.EAS.Attester.MultiRevokeEncodeMemory
import Benchmarks.EAS.Attester.NestedPrefix

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Reasoning.Theory

-- LIBRARY CANDIDATE: a decoded bytes32 array agrees with its calldata words at every index.
theorem decodedBytes32Array_calldata_lookup {cd : ByteArray} {values : List Value}
    {start endOffset i : Nat}
    (hd : decodeABIValue? (.dynamicArray abiBytes32) (cd.toList.drop 4) start =
      some (.array values, endOffset)) (hi : i < values.length) :
    values[i]? = some (wordBytes32Value (calldataWord cd (4 + (start + 32 + 32 * i)))) := by
  obtain ⟨word, hv⟩ := decodeABIValue_dynamicArray_bytes32_lookup_shape hd hi
  have hr := decodeABIValue_dynamicArray_bytes32_lookup_readNat hd hv
  have hb := readNat?_some_length hr
  have hl : cd.toList.length = cd.size := by rw [byteArray_toList_eq, Array.length_toList]; rfl
  rw [List.length_drop, hl] at hb
  rw [readNat_drop4_at_eq_calldataWord _ (by omega), Option.some.injEq] at hr
  have he : word = calldataWord cd (4 + (start + 32 + 32 * i)) := by
    apply u256_inj
    exact hr.symm
  simpa only [lookupNth_eq_getElem, he] using hv

end Reasoning.Theory

namespace Benchmarks.EAS.Attester

theorem revokePairValues_eq_sequence {uids : List Value} {values : Nat → UInt256 × UInt256}
    {n : Nat} (hlen : uids.length = n)
    (hv : ∀ j < n, uids[j]? = some (wordBytes32Value (values j).1))
    (hz : ∀ j < n, (values j).2 = ⟨0⟩) :
    revokePairValues uids = pairSequenceValues values 0 n := by
  apply List.ext_getElem
    (by simp only [revokePairValues, List.length_map, pairSequenceValues_length, hlen])
  intro j hj hj'
  have hjn : j < n := by simpa only [revokePairValues, List.length_map, hlen] using hj
  have hl : (revokePairValues uids)[j]? =
      some (.tuple [wordBytes32Value (values j).1, .int 0]) := by
    simp only [revokePairValues, List.getElem?_map, hv j hjn, Option.map_some]
  have hr := pairSequenceValues_getElem values 0 n j hjn
  simp only [Nat.zero_add, wordPairValue, hz j hjn] at hr
  have he : (revokePairValues uids)[j]? = (pairSequenceValues values 0 n)[j]? := hl.trans hr.symm
  rw [List.getElem?_eq_getElem hj, List.getElem?_eq_getElem hj', Option.some.injEq] at he
  exact he

theorem multiRevokeDecodedViews {cd : ByteArray} {schemas rows : List Value}
    (hd : decodeArrays? bytes32 cd = some (.array schemas, .array rows))
    (hshape : BatchShape cd) (hsel : cd.extract 0 4 = attesterMultiRevokeSelBytes) :
    ∀ i < arrayCount cd 4,
      RevokeRowView schemas rows (pairRequestsValues (multiRevokeSchemas cd) (multiRevokeCounts cd)
        (multiRevokeValues cd) 0 (arrayCount cd 4)) i := by
  obtain ⟨end0, end1, hsize, hsign, hoff0, hoff1, hd0, hd1⟩ := decodeArrays_some_facts hd
  have hc := decodeArrays_some_checks hd
  obtain ⟨schemas', rows', endRows, hv, hlen0, hlen1, hdRows⟩ := decodeArrays_first_facts hd
  cases Prod.mk.inj hv |>.1
  cases Prod.mk.inj hv |>.2
  intro i hi
  obtain ⟨uids, endInner, hrow, hdInner, hcheck, hlen, hbound⟩ :=
    decodedRows_lookup hc hsign hdRows (by rw [hshape.2]; exact hi)
  have hfour : 4 ≤ (rowHead cd (UInt256.ofNat (arrayDataNat cd 36)) i).toNat :=
    multiRevoke_uint64_past_selector hsel (by omega)
      (uint64Bound_of_isZero_gt hcheck.length)
  have hdata : (rowData cd (UInt256.ofNat (arrayDataNat cd 36)) i).toNat =
      (rowHead cd (UInt256.ofNat (arrayDataNat cd 36)) i).toNat + 32 := by
    unfold rowData
    rw [uadd_toNat, Nat.mod_eq_of_lt (by
      change 32 + (rowHead cd (UInt256.ofNat (arrayDataNat cd 36)) i).toNat < UInt256.size
      have hh := lt_size_of_lt_sign hsign; omega)]
    change 32 + _ = _; omega
  have huid : ∀ j < uids.length,
      uids[j]? = some (wordBytes32Value (multiRevokeValues cd i j).1) := by
    intro j hj
    have hv := decodedBytes32Array_calldata_lookup hdInner hj
    simpa only [multiRevokeValues, hdata,
      show 4 + ((rowHead cd (UInt256.ofNat (arrayDataNat cd 36)) i).toNat - 4 + 32 + 32 * j) =
        (rowHead cd (UInt256.ofNat (arrayDataNat cd 36)) i).toNat + 32 + 32 * j by omega] using hv
  have hsch : schemas[i]? = some (wordBytes32Value (multiRevokeSchemas cd i)) := by
    have hs := decodedBytes32Array_calldata_lookup hd0 (by omega : i < schemas.length)
    simpa only [multiRevokeSchemas, arrayDataNat,
      show 4 + ((calldataWord cd 4).toNat + 32 + 32 * i) =
        4 + (calldataWord cd 4).toNat + 32 + 32 * i by omega] using hs
  have hpair : revokePairValues uids =
      pairSequenceValues (multiRevokeValues cd i) 0 (multiRevokeCounts cd i) :=
    revokePairValues_eq_sequence hlen.symm
      (by intro j hj; exact huid j (by change j < (rowLength cd _ i).toNat at hj; omega))
      (by intro j _; rfl)
  refine ⟨wordBytes32Value (multiRevokeSchemas cd i), uids, hsch, hrow, ?_, ?_, rfl, ?_⟩
  · simpa only [Nat.zero_add, pairRequestValue, hpair] using
      pairRequestsValues_getElem (multiRevokeSchemas cd) (multiRevokeCounts cd)
        (multiRevokeValues cd) 0 (arrayCount cd 4) i hi
  · have hh := uint64Bound_of_isZero_gt hcheck.length
    change (rowLength cd (UInt256.ofNat (arrayDataNat cd 36)) i).toNat ≤ solcMaxU64 at hh
    rw [hlen] at hh
    change uids.length < 2 ^ 256
    change uids.length ≤ 18446744073709551615 at hh
    omega
  · intro value hv
    obtain ⟨j, hj, hvalue⟩ := List.mem_iff_getElem.mp hv
    have hlookup := huid j hj
    rw [List.getElem?_eq_getElem hj, hvalue, Option.some.injEq] at hlookup
    rw [hlookup]
    rfl

theorem multiRevokeDecoded_nonempty_iff {cd : ByteArray} {schemas rows : List Value}
    (hd : decodeArrays? bytes32 cd = some (.array schemas, .array rows)) (hshape : BatchShape cd) :
    BatchRowsValid cd ↔ ∀ i < arrayCount cd 4, rows[i]? ≠ some (.array []) := by
  have hc := decodeArrays_some_checks hd
  obtain ⟨schemas', rows', endRows, hv, _h0, _h1, hdRows⟩ := decodeArrays_first_facts hd
  have hrows : rows = rows' := Value.array.inj (Prod.mk.inj hv).2
  subst rows'
  constructor
  · intro hvalid i hi he
    obtain ⟨uids, endInner, hrow, _, _, hlen, _⟩ :=
      decodedRows_lookup hc (hc.size_lt_sign (by
        have hh := decodeArrays_some_facts hd
        obtain ⟨_, _, _, hsign, _⟩ := hh
        exact lt_size_of_lt_sign hsign)) hdRows (by rw [hshape.2]; exact hi)
    rw [hrow, Option.some.injEq, Value.array.injEq] at he
    subst uids
    exact (hvalid i (by rw [hshape.2]; exact hi)).2 (uint256_toNat_eq_zero hlen)
  · intro hvalid i hi
    obtain ⟨uids, endInner, hrow, _, hcheck, hlen, _⟩ :=
      decodedRows_lookup hc (hc.size_lt_sign (by
        obtain ⟨_, _, _, hsign, _⟩ := decodeArrays_some_facts hd
        exact lt_size_of_lt_sign hsign)) hdRows hi
    refine ⟨hcheck, ?_⟩
    intro hz
    rw [hz] at hlen
    have hu : uids = [] := List.eq_nil_of_length_eq_zero hlen.symm
    exact hvalid i (by rwa [hshape.2] at hi) (by simpa only [hu] using hrow)

end Benchmarks.EAS.Attester
