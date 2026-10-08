import Benchmarks.EAS.Attester.MultiAttestSourceLoop
import Benchmarks.EAS.Attester.MultiAttestEncodeMemory
import Benchmarks.EAS.Attester.MultiRevokeSourceABI

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Reasoning.Theory

theorem decodedUInt256Array_calldata_lookup {cd : ByteArray} {values : List Value}
    {start endOffset i : Nat}
    (hd : decodeABIValue? (.dynamicArray abiUInt256) (cd.toList.drop 4) start =
      some (.array values, endOffset)) (hi : i < values.length) :
    values[i]? = some ((.int (Int.ofNat (calldataWord cd (4 + (start + 32 + 32 * i))).toNat))) := by
  obtain ⟨word, hv⟩ := decodeABIValue_dynamicArray_uint256_lookup_shape hd hi
  have hr := decodeABIValue_dynamicArray_uint256_lookup_readNat hd hv
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

theorem multiAttestDecodedViews {cd : ByteArray} {schemas rows : List Value}
    (hd : decodeArrays? uint256 cd = some (.array schemas, .array rows))
    (hshape : BatchShape cd) (hsel : cd.extract 0 4 = attesterMultiAttestSelBytes) :
    ∀ i < arrayCount cd 4,
      AttestRowView schemas rows (attestRequestsValues (multiAttestSchemas cd) (multiAttestCounts
          cd)
        (multiAttestValues cd) 0 (arrayCount cd 4)) (multiAttestCounts cd) (multiAttestValues cd) i
            := by
  obtain ⟨end0, end1, hsize, hsign, hoff0, hoff1, hd0, hd1⟩ := decodeArrays_some_facts hd
  have hc := decodeArrays_some_checks hd
  obtain ⟨schemas', rows', endRows, hv, hlen0, hlen1, hdRows⟩ := decodeArrays_first_facts hd
  cases Prod.mk.inj hv |>.1
  cases Prod.mk.inj hv |>.2
  intro i hi
  obtain ⟨inputs, endInner, hrow, hdInner, hcheck, hlen, hbound⟩ :=
    decodedRows_lookup hc hsign hdRows (by rw [hshape.2]; exact hi)
  have hfour : 4 ≤ (rowHead cd (UInt256.ofNat (arrayDataNat cd 36)) i).toNat :=
    multiAttest_uint64_past_selector hsel (by omega)
      (uint64Bound_of_isZero_gt hcheck.length)
  have hdata : (rowData cd (UInt256.ofNat (arrayDataNat cd 36)) i).toNat =
      (rowHead cd (UInt256.ofNat (arrayDataNat cd 36)) i).toNat + 32 := by
    unfold rowData
    rw [uadd_toNat, Nat.mod_eq_of_lt (by
      change 32 + (rowHead cd (UInt256.ofNat (arrayDataNat cd 36)) i).toNat < UInt256.size
      have hh := lt_size_of_lt_sign hsign; omega)]
    change 32 + _ = _; omega
  have huid : ∀ j < inputs.length,
      inputs[j]? = some (.int (Int.ofNat (multiAttestValues cd i j).toNat)) := by
    intro j hj
    have hv := decodedUInt256Array_calldata_lookup hdInner hj
    simpa only [multiAttestValues, hdata,
      show 4 + ((rowHead cd (UInt256.ofNat (arrayDataNat cd 36)) i).toNat - 4 + 32 + 32 * j) =
        (rowHead cd (UInt256.ofNat (arrayDataNat cd 36)) i).toNat + 32 + 32 * j by omega] using hv
  have hsch : schemas[i]? = some (wordBytes32Value (multiAttestSchemas cd i)) := by
    have hs := decodedBytes32Array_calldata_lookup hd0 (by omega : i < schemas.length)
    simpa only [multiAttestSchemas, arrayDataNat,
      show 4 + ((calldataWord cd 4).toNat + 32 + 32 * i) =
        4 + (calldataWord cd 4).toNat + 32 + 32 * i by omega] using hs
  refine ⟨wordBytes32Value (multiAttestSchemas cd i), inputs, hsch, hrow, ?_, hlen.symm, ?_, rfl,
      huid⟩
  · simpa only [Nat.zero_add, attestBatchRowValue, ← hlen] using
      attestRequestsValues_getElem (multiAttestSchemas cd) (multiAttestCounts cd)
        (multiAttestValues cd) 0 (arrayCount cd 4) i hi
  · have hh := uint64Bound_of_isZero_gt hcheck.length
    change (rowLength cd (UInt256.ofNat (arrayDataNat cd 36)) i).toNat ≤ solcMaxU64 at hh
    rw [hlen] at hh
    change inputs.length < 2 ^ 256
    change inputs.length ≤ 18446744073709551615 at hh
    omega
theorem multiAttestDecoded_nonempty_iff {cd : ByteArray} {schemas rows : List Value}
    (hd : decodeArrays? uint256 cd = some (.array schemas, .array rows)) (hshape : BatchShape cd) :
    BatchRowsValid cd ↔ ∀ i < arrayCount cd 4, rows[i]? ≠ some (.array []) := by
  have hc := decodeArrays_some_checks hd
  obtain ⟨schemas', rows', endRows, hv, _h0, _h1, hdRows⟩ := decodeArrays_first_facts hd
  have hrows : rows = rows' := Value.array.inj (Prod.mk.inj hv).2
  subst rows'
  constructor
  · intro hvalid i hi he
    obtain ⟨inputs, endInner, hrow, _, _, hlen, _⟩ :=
      decodedRows_lookup hc (hc.size_lt_sign (by
        have hh := decodeArrays_some_facts hd
        obtain ⟨_, _, _, hsign, _⟩ := hh
        exact lt_size_of_lt_sign hsign)) hdRows (by rw [hshape.2]; exact hi)
    rw [hrow, Option.some.injEq, Value.array.injEq] at he
    subst inputs
    exact (hvalid i (by rw [hshape.2]; exact hi)).2 (uint256_toNat_eq_zero hlen)
  · intro hvalid i hi
    obtain ⟨inputs, endInner, hrow, _, hcheck, hlen, _⟩ :=
      decodedRows_lookup hc (hc.size_lt_sign (by
        obtain ⟨_, _, _, hsign, _⟩ := decodeArrays_some_facts hd
        exact lt_size_of_lt_sign hsign)) hdRows hi
    refine ⟨hcheck, ?_⟩
    intro hz
    rw [hz] at hlen
    have hu : inputs = [] := List.eq_nil_of_length_eq_zero hlen.symm
    exact hvalid i (by rwa [hshape.2] at hi) (by simpa only [hu] using hrow)

end Benchmarks.EAS.Attester
