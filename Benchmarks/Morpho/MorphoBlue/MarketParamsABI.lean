import Benchmarks.Morpho.MorphoBlue.MarketParamsCommon

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.Morpho.MorphoBlue
set_option maxRecDepth 1000

-- LIBRARY CANDIDATE: a tuple of scalar ABI words reduces to the scalar-list decoder.
theorem decodeABIValue_scalarTuple_eq {types : List ABIType} {bytes : List UInt8}
    (hscalar : types.all isABIScalarWordType = true) :
    decodeABIValue? (.tuple types) bytes 0 =
      (decodeScalarWords? types bytes 0).map (fun values ↦
        (.tuple values, 32 * types.length)) := by
  rw [decodeABIValue?, abiTupleHeadSize_scalarWords_eq hscalar]
  simp only [bind, Option.bind, Nat.zero_add]
  rw [decodeABIValues_scalarWords_eq hscalar (by omega)]
  cases decodeScalarWords? types bytes 0 <;> rfl

def marketParamsABIFields : List ABIType :=
  [.elem .address, .elem .address, .elem .address, .elem .address, abiUInt256]

def marketParamsABIType : ABIType := .tuple marketParamsABIFields

theorem decodeCalldata_marketParams_eq (cd : ByteArray) (name : Ident) :
    decodeCalldata [name] [marketParamsABIType] cd =
      if cd.size < 164 ∨ 2 ^ 255 + 4 ≤ cd.size then none
      else (decodeScalarWords? marketParamsABIFields (cd.toList.drop 4) 0).map
        (fun values ↦ (∅ : Store).insert name (.tuple values)) := by
  have htlen : cd.toList.length = cd.size := by
    rw [byteArray_toList_eq, Array.length_toList]; rfl
  have hdyn : isDynamicABIType marketParamsABIType = false := rfl
  have hstatic : staticABIEncodedSize? marketParamsABIType = some 160 := rfl
  have hhead : abiTupleHeadSize? [marketParamsABIType] = some 160 := by
    simp only [abiTupleHeadSize?, hdyn, Bool.false_eq_true, ↓reduceIte, hstatic,
      bind, Option.bind, pure, Nat.add_zero]
  have htotal : solcTotalSizeDynamicGuard [marketParamsABIType] = false := rfl
  unfold decodeCalldata
  simp only [List.length_drop, htlen, List.any_cons, List.any_nil, hdyn,
    Bool.or_false, Bool.false_eq_true, false_and, ↓reduceIte, List.isEmpty_cons,
    and_self, true_and, htotal]
  by_cases h4 : cd.size < 4
  · simp only [h4, ↓reduceIte, show cd.size < 164 ∨ 2 ^ 255 + 4 ≤ cd.size by omega]
  · simp only [h4, ↓reduceIte]
    by_cases hbig : 2 ^ 255 ≤ cd.size - 4
    · simp only [hbig, ↓reduceIte, show cd.size < 164 ∨ 2 ^ 255 + 4 ≤ cd.size by omega]
    · simp only [hbig, ↓reduceIte, decodeCalldata.decodeArgs, hhead, bind, Option.bind,
        List.length_drop, htlen]
      by_cases hshort : cd.size - 4 < 160
      · simp only [hshort, ↓reduceIte, show cd.size < 164 ∨ 2 ^ 255 + 4 ≤ cd.size by omega]
      · simp only [hshort, ↓reduceIte, show ¬ (cd.size < 164 ∨ 2 ^ 255 + 4 ≤ cd.size) by omega,
          decodeABIValues?, hdyn, Bool.false_eq_true, ↓reduceIte, hstatic, bind, Option.bind,
          Nat.zero_add]
        rw [show marketParamsABIType = .tuple marketParamsABIFields from rfl,
          decodeABIValue_scalarTuple_eq (by decide)]
        cases decodeScalarWords? marketParamsABIFields (cd.toList.drop 4) 0 <;>
          simp [Option.map, marketParamsABIFields, decodeABIValues?, decodeCalldata.insertValues]

-- LIBRARY CANDIDATE: scalar decoders at a calldata argument's byte offset.
theorem decodeScalarWord_calldata_address {cd : ByteArray} {off : Nat}
    (hlen : off + 36 ≤ cd.size) (hoff : off + 4 < 2 ^ 64)
    (hc : (calldataWord cd (off + 4)).toNat < EVM.addressModulus) :
    decodeScalarWord? (.elem .address) (cd.toList.drop 4) off =
      some (.address (AccountAddress.ofNat (calldataWord cd (off + 4)).toNat), off + 32) := by
  have htlen : cd.toList.length = cd.size := by
    rw [byteArray_toList_eq, Array.length_toList]; rfl
  have hw : ABI.bytesToWord (((cd.toList.drop 4).drop off).take 32) =
      calldataWord cd (off + 4) := by
    simpa only [List.drop_drop, Nat.add_comm] using
      decode_word_at_eq cd (off + 4) (by omega) hoff
  have htake : (((cd.toList.drop 4).drop off).take 32).length = 32 := by
    simp only [List.length_take, List.length_drop, htlen]; omega
  rw [decodeScalarWord_address_ok htake (by rw [hw]; exact hc), hw]

theorem decodeScalarWord_calldata_uint256 {cd : ByteArray} {off : Nat}
    (hlen : off + 36 ≤ cd.size) (hoff : off + 4 < 2 ^ 64) :
    decodeScalarWord? abiUInt256 (cd.toList.drop 4) off =
      some (.int (Int.ofNat (calldataWord cd (off + 4)).toNat), off + 32) := by
  have htlen : cd.toList.length = cd.size := by
    rw [byteArray_toList_eq, Array.length_toList]; rfl
  have hw : ABI.bytesToWord (((cd.toList.drop 4).drop off).take 32) =
      calldataWord cd (off + 4) := by
    simpa only [List.drop_drop, Nat.add_comm] using
      decode_word_at_eq cd (off + 4) (by omega) hoff
  have htake : (((cd.toList.drop 4).drop off).take 32).length = 32 := by
    simp only [List.length_take, List.length_drop, htlen]; omega
  rw [decodeScalarWord_uint256_ok htake, hw]

theorem decodeScalarWord_calldata_address_noncanonical {cd : ByteArray} {off : Nat}
    (hlen : off + 36 ≤ cd.size) (hoff : off + 4 < 2 ^ 64)
    (hc : ¬ (calldataWord cd (off + 4)).toNat < EVM.addressModulus) :
    decodeScalarWord? (.elem .address) (cd.toList.drop 4) off = none := by
  have htlen : cd.toList.length = cd.size := by
    rw [byteArray_toList_eq, Array.length_toList]; rfl
  have hw : ABI.bytesToWord (((cd.toList.drop 4).drop off).take 32) =
      calldataWord cd (off + 4) := by
    simpa only [List.drop_drop, Nat.add_comm] using
      decode_word_at_eq cd (off + 4) (by omega) hoff
  apply decodeScalarWord_address_none_noncanon
  · simp only [List.length_take, List.length_drop, htlen]; omega
  · rw [hw]; exact hc

def marketParamsABIValues (p : MarketParamsWords) : List Value :=
  [.address (AccountAddress.ofNat p.loanToken.toNat),
    .address (AccountAddress.ofNat p.collateralToken.toNat),
    .address (AccountAddress.ofNat p.oracle.toNat), .address (AccountAddress.ofNat p.irm.toNat),
    .int (Int.ofNat p.lltv.toNat)]

theorem decodeScalarWords_marketParams_ok {cd : ByteArray}
    (hlen : 164 ≤ cd.size) (hc : (marketParamsFromCalldata cd).Canonical) :
    decodeScalarWords? marketParamsABIFields (cd.toList.drop 4) 0 =
      some (marketParamsABIValues (marketParamsFromCalldata cd)) := by
  dsimp only [MarketParamsWords.Canonical, marketParamsFromCalldata] at hc
  simp only [marketParamsABIFields, decodeScalarWords?, Nat.zero_add]
  rw [decodeScalarWord_calldata_address (off := 0) (by omega) (by norm_num) hc.1]
  simp only [bind, Option.bind]
  rw [decodeScalarWord_calldata_address (off := 32) (by omega) (by norm_num) hc.2.1]
  simp only [bind, Option.bind]
  rw [decodeScalarWord_calldata_address (off := 64) (by omega) (by norm_num) hc.2.2.1]
  simp only [bind, Option.bind]
  rw [decodeScalarWord_calldata_address (off := 96) (by omega) (by norm_num) hc.2.2.2]
  simp only [bind, Option.bind]
  rw [decodeScalarWord_calldata_uint256 (off := 128) (by omega) (by norm_num)]
  rfl

theorem decodeScalarWords_marketParams_noncanonical {cd : ByteArray}
    (hlen : 164 ≤ cd.size) (hc : ¬ (marketParamsFromCalldata cd).Canonical) :
    decodeScalarWords? marketParamsABIFields (cd.toList.drop 4) 0 = none := by
  dsimp only [MarketParamsWords.Canonical, marketParamsFromCalldata] at hc
  simp only [marketParamsABIFields, decodeScalarWords?, Nat.zero_add]
  by_cases h0 : (calldataWord cd 4).toNat < EVM.addressModulus
  · rw [decodeScalarWord_calldata_address (off := 0) (by omega) (by norm_num) h0]
    simp only [bind, Option.bind]
    by_cases h1 : (calldataWord cd 36).toNat < EVM.addressModulus
    · rw [decodeScalarWord_calldata_address (off := 32) (by omega) (by norm_num) h1]
      simp only [bind, Option.bind]
      by_cases h2 : (calldataWord cd 68).toNat < EVM.addressModulus
      · rw [decodeScalarWord_calldata_address (off := 64) (by omega) (by norm_num) h2]
        simp only [bind, Option.bind]
        have h3 : ¬ (calldataWord cd 100).toNat < EVM.addressModulus :=
          fun h3 ↦ hc ⟨h0, h1, h2, h3⟩
        rw [decodeScalarWord_calldata_address_noncanonical (off := 96)
          (by omega) (by norm_num) h3]
      · rw [decodeScalarWord_calldata_address_noncanonical (off := 64)
          (by omega) (by norm_num) h2]
    · rw [decodeScalarWord_calldata_address_noncanonical (off := 32)
        (by omega) (by norm_num) h1]
  · rw [decodeScalarWord_calldata_address_noncanonical (off := 0)
      (by omega) (by norm_num) h0]
    rfl

theorem decodeABIValue_marketParams_ok {cd : ByteArray}
    (hlen : 164 ≤ cd.size) (hc : (marketParamsFromCalldata cd).Canonical) :
    decodeABIValue? marketParamsABIType (cd.toList.drop 4) 0 =
      some ((marketParamsFromCalldata cd).value, 160) := by
  rw [marketParamsABIType, decodeABIValue_scalarTuple_eq (by decide),
    decodeScalarWords_marketParams_ok hlen hc]
  rfl

theorem decodeCalldata_marketParams_ok {cd : ByteArray} {name : Ident}
    (hlen : 164 ≤ cd.size) (hbig : cd.size < 2 ^ 255 + 4)
    (hc : (marketParamsFromCalldata cd).Canonical) :
    decodeCalldata [name] [marketParamsABIType] cd =
      some ((∅ : Store).insert name (marketParamsFromCalldata cd).value) := by
  rw [decodeCalldata_marketParams_eq, if_neg (by omega),
    decodeScalarWords_marketParams_ok hlen hc]
  rfl

theorem decodeCalldata_marketParams_noncanonical {cd : ByteArray} {name : Ident}
    (hlen : 164 ≤ cd.size) (hc : ¬ (marketParamsFromCalldata cd).Canonical) :
    decodeCalldata [name] [marketParamsABIType] cd = none := by
  rw [decodeCalldata_marketParams_eq]
  split
  · rfl
  · rw [decodeScalarWords_marketParams_noncanonical hlen hc]; rfl

theorem decodeCalldata_marketParams_short {cd : ByteArray} {name : Ident}
    (hlen : cd.size < 164) :
    decodeCalldata [name] [marketParamsABIType] cd = none := by
  rw [decodeCalldata_marketParams_eq, if_pos (Or.inl hlen)]

theorem decodeCalldata_marketParams_huge {cd : ByteArray} {name : Ident}
    (hbig : 2 ^ 255 + 4 ≤ cd.size) :
    decodeCalldata [name] [marketParamsABIType] cd = none := by
  rw [decodeCalldata_marketParams_eq, if_pos (Or.inr hbig)]

theorem encodeMarketParams (p : MarketParamsWords) (hc : p.Canonical) :
    encodeABIValue? Syntax.marketParamsABI p.value = some p.bytes.toList := by
  apply elementaryWordsTupleEncoding
    [(.address, .address (AccountAddress.ofNat p.loanToken.toNat), p.loanToken),
      (.address, .address (AccountAddress.ofNat p.collateralToken.toNat), p.collateralToken),
      (.address, .address (AccountAddress.ofNat p.oracle.toNat), p.oracle),
      (.address, .address (AccountAddress.ofNat p.irm.toNat), p.irm),
      (.int (.uint ⟨256, by decide⟩), .int (Int.ofNat p.lltv.toNat), p.lltv)]
  intro e he
  simp only [List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with rfl | rfl | rfl | rfl | rfl
  · simpa only [accountAddress_ofUInt256_eq_ofNat_toNat] using
      encodeABIValue_address_ofUInt256_of_canonical p.loanToken hc.1
  · simpa only [accountAddress_ofUInt256_eq_ofNat_toNat] using
      encodeABIValue_address_ofUInt256_of_canonical p.collateralToken hc.2.1
  · simpa only [accountAddress_ofUInt256_eq_ofNat_toNat] using
      encodeABIValue_address_ofUInt256_of_canonical p.oracle hc.2.2.1
  · simpa only [accountAddress_ofUInt256_eq_ofNat_toNat] using
      encodeABIValue_address_ofUInt256_of_canonical p.irm hc.2.2.2
  · exact encodeABIValue_uint256 p.lltv

end Benchmarks.Morpho.MorphoBlue
