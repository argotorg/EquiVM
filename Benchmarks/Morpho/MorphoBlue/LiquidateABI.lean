import Benchmarks.Morpho.MorphoBlue.StaticABIValues

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.Morpho.MorphoBlue
set_option maxRecDepth 1000

-- LIBRARY CANDIDATE: the final dynamic bytes argument, with extent metadata discarded.
theorem decodeABIValues_calldata_bytes_values {cd : ByteArray} {cursor head last : Nat}
    (hb : 4 + cursor + 32 ≤ cd.size) :
    (decodeABIValues? [.bytes] (cd.toList.drop 4) 0 cursor head last).map Prod.fst =
      if (calldataWord cd (4 + cursor)).toNat ≤ solcMaxU64 ∧
          CalldataBytesBounds cd (4 + (calldataWord cd (4 + cursor)).toNat) then
        some [.bytes (calldataBytesPayload cd (4 + (calldataWord cd (4 + cursor)).toNat))]
      else none := by
  simp only [decodeABIValues?, show isDynamicABIType ABIType.bytes = true from rfl,
    bind, Option.bind, ↓reduceIte, Nat.zero_add]
  rw [readNat_drop4_at_eq_calldataWord cursor (by omega)]
  simp only [solcMaxLen]
  by_cases ho : (calldataWord cd (4 + cursor)).toNat ≤ solcMaxU64
  swap
  · simp only [show solcMaxU64 < (calldataWord cd (4 + cursor)).toNat by omega,
      ↓reduceIte, Option.map_none, ho, false_and]
  simp only [show ¬ solcMaxU64 < (calldataWord cd (4 + cursor)).toNat by omega,
    ↓reduceIte, Nat.zero_add]
  rw [decodeABIValue_bytes_calldata_eq]
  by_cases hp : CalldataBytesBounds cd (4 + (calldataWord cd (4 + cursor)).toNat)
  · simp only [hp, ho, ↓reduceIte, Option.map_some, and_self]
  · simp only [hp, ho, ↓reduceIte, Option.map_none, and_false]

def LiquidateBounds (cd : ByteArray) : Prop :=
  292 ≤ cd.size ∧ cd.size < 2 ^ 255 ∧ (marketParamsFromCalldata cd).Canonical ∧
    (calldataWord cd 164).toNat < EVM.addressModulus ∧
    (calldataWord cd 260).toNat ≤ solcMaxU64 ∧
    CalldataBytesBounds cd (4 + (calldataWord cd 260).toNat)

instance (cd : ByteArray) : Decidable (LiquidateBounds cd) := by
  unfold LiquidateBounds
  infer_instance

def liquidateCalldataArgs (cd : ByteArray) : Store :=
  (((((∅ : Store).insert "marketParams" (marketParamsFromCalldata cd).value).insert
    "borrower" (.address (AccountAddress.ofNat (calldataWord cd 164).toNat))).insert
    "seizedAssets" (.int (Int.ofNat (calldataWord cd 196).toNat))).insert
    "repaidShares" (.int (Int.ofNat (calldataWord cd 228).toNat))).insert
    "data" (.bytes (calldataBytesPayload cd (4 + (calldataWord cd 260).toNat)))

theorem decodeCalldata_liquidate_eq (cd : ByteArray) :
    decodeCalldata ["marketParams", "borrower", "seizedAssets", "repaidShares", "data"]
      [marketParamsABIType, abiAddress, abiUInt256, abiUInt256, .bytes] cd =
      if LiquidateBounds cd then some (liquidateCalldataArgs cd) else none := by
  have hhead : abiTupleHeadSize? [marketParamsABIType, abiAddress, abiUInt256, abiUInt256, .bytes] = some 288 := by
    simp only [abiTupleHeadSize?, show isDynamicABIType marketParamsABIType = false from rfl,
      show staticABIEncodedSize? marketParamsABIType = some 160 from rfl,
      isDynamicABIType, staticABIEncodedSize?, abiUInt256, abiAddress, Bool.false_eq_true,
      ↓reduceIte, bind, Option.bind, pure]
  rw [decodeCalldata_dynamicValues cd _ _ 288 rfl hhead]
  by_cases hs : 292 ≤ cd.size ∧ cd.size < 2 ^ 255
  swap
  · rw [if_neg hs, if_neg (show ¬ LiquidateBounds cd from fun hb ↦ hs ⟨hb.1, hb.2.1⟩)]
  rw [if_pos hs, decodeABIValues_market_cons (by omega) (by decide)]
  by_cases hc : (marketParamsFromCalldata cd).Canonical
  swap
  · simp only [hc, ↓reduceIte, Option.bind_none,
      show ¬ LiquidateBounds cd from fun hb ↦ hc hb.2.2.1]
  rw [if_pos hc, decodeABIValues_calldata_address_cons_values (by omega) (by decide)]
  by_cases ha : (calldataWord cd 164).toNat < EVM.addressModulus
  swap
  · simp only [ha, ↓reduceIte, Option.bind_none, Option.map_none,
      show ¬ LiquidateBounds cd from fun hb ↦ ha hb.2.2.2.1]
  rw [if_pos ha, decodeABIValues_calldata_uint_cons_values (by omega) (by decide),
    decodeABIValues_calldata_uint_cons_values (by omega) (by decide),
    decodeABIValues_calldata_bytes_values (by omega)]
  by_cases hb : (calldataWord cd 260).toNat ≤ solcMaxU64 ∧ CalldataBytesBounds cd (4 + (calldataWord cd 260).toNat)
  · have hfull : LiquidateBounds cd := ⟨hs.1, hs.2, hc, ha, hb⟩
    simp only [hb, and_self, ↓reduceIte, Option.map_some, Option.bind_some, hfull,
      decodeCalldata.insertValues, liquidateCalldataArgs]
  · have hbad : ¬ LiquidateBounds cd := fun h ↦ hb h.2.2.2.2
    simp only [hb, ↓reduceIte, Option.map_none, Option.bind_none, hbad]

end Benchmarks.Morpho.MorphoBlue
