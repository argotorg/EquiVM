import Benchmarks.Morpho.MorphoBlue.MarketDynamicABI

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.Morpho.MorphoBlue
set_option maxRecDepth 1000

def MarketTwoWordsAddressBytesBounds (cd : ByteArray) : Prop :=
  292 ≤ cd.size ∧ cd.size < 2 ^ 255 ∧ (marketParamsFromCalldata cd).Canonical ∧
    (calldataWord cd 228).toNat < EVM.addressModulus ∧
    (calldataWord cd 260).toNat ≤ solcMaxU64 ∧
    CalldataBytesBounds cd (4 + (calldataWord cd 260).toNat)

instance (cd : ByteArray) : Decidable (MarketTwoWordsAddressBytesBounds cd) := by
  unfold MarketTwoWordsAddressBytesBounds MarketParamsWords.Canonical
  infer_instance

def marketTwoWordsAddressBytesArgs (cd : ByteArray) (a b c d e : Ident) : Store :=
  (((((∅ : Store).insert a (marketParamsFromCalldata cd).value).insert
    b (.int (Int.ofNat (calldataWord cd 164).toNat))).insert
    c (.int (Int.ofNat (calldataWord cd 196).toNat))).insert
    d (.address (AccountAddress.ofNat (calldataWord cd 228).toNat))).insert
    e (.bytes (calldataBytesPayload cd (4 + (calldataWord cd 260).toNat)))

theorem decodeCalldata_market_two_uint_address_bytes_eq (cd : ByteArray) (a b c d e : Ident) :
    decodeCalldata [a, b, c, d, e] [marketParamsABIType, abiUInt256, abiUInt256, abiAddress, .bytes] cd =
      if MarketTwoWordsAddressBytesBounds cd then some (marketTwoWordsAddressBytesArgs cd a b c d e) else none := by
  have hhead : abiTupleHeadSize? [marketParamsABIType, abiUInt256, abiUInt256, abiAddress, .bytes] = some 288 := by
    simp only [abiTupleHeadSize?, show isDynamicABIType marketParamsABIType = false from rfl,
      show staticABIEncodedSize? marketParamsABIType = some 160 from rfl,
      isDynamicABIType, staticABIEncodedSize?, abiUInt256, abiAddress, Bool.false_eq_true,
      ↓reduceIte, bind, Option.bind, pure]
  rw [decodeCalldata_dynamicValues cd _ _ 288 (by rfl) hhead]
  by_cases hs : 292 ≤ cd.size ∧ cd.size < 2 ^ 255
  swap
  · rw [if_neg hs, if_neg (show ¬ MarketTwoWordsAddressBytesBounds cd from fun hb ↦ hs ⟨hb.1, hb.2.1⟩)]
  rw [if_pos hs, decodeABIValues_market_cons (by omega) (by decide)]
  by_cases hc : (marketParamsFromCalldata cd).Canonical
  swap
  · simp only [hc, ↓reduceIte, Option.bind_none,
      show ¬ MarketTwoWordsAddressBytesBounds cd from fun hb ↦ hc hb.2.2.1]
  rw [if_pos hc, decodeABIValues_calldata_uint_cons_values (by omega) (by decide)]
  rw [decodeABIValues_calldata_uint_cons_values (by omega) (by decide)]
  rw [decodeABIValues_calldata_address_bytes (by omega) (by decide)]
  by_cases hb : AddressBytesBounds cd 224
  · have hfull : MarketTwoWordsAddressBytesBounds cd := ⟨hs.1, hs.2, hc, hb⟩
    simp only [hb, ↓reduceIte, Option.map_some, Option.bind_some, hfull,
      decodeCalldata.insertValues, marketTwoWordsAddressBytesArgs]
  · have hbad : ¬ MarketTwoWordsAddressBytesBounds cd := fun h ↦ hb h.2.2.2
    simp only [hb, ↓reduceIte, Option.map_none, Option.bind_none, hbad]

end Benchmarks.Morpho.MorphoBlue
