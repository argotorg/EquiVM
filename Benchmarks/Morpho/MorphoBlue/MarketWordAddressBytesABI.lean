import Benchmarks.Morpho.MorphoBlue.MarketDynamicABI

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.Morpho.MorphoBlue
set_option maxRecDepth 1000

def MarketWordAddressBytesBounds (cd : ByteArray) : Prop :=
  260 ≤ cd.size ∧ cd.size < 2 ^ 255 ∧ (marketParamsFromCalldata cd).Canonical ∧
    (calldataWord cd 196).toNat < EVM.addressModulus ∧
    (calldataWord cd 228).toNat ≤ solcMaxU64 ∧
    CalldataBytesBounds cd (4 + (calldataWord cd 228).toNat)

instance (cd : ByteArray) : Decidable (MarketWordAddressBytesBounds cd) := by
  unfold MarketWordAddressBytesBounds MarketParamsWords.Canonical
  infer_instance

def marketWordAddressBytesArgs (cd : ByteArray) (a b c d : Ident) : Store :=
  ((((∅ : Store).insert a (marketParamsFromCalldata cd).value).insert
    b (.int (Int.ofNat (calldataWord cd 164).toNat))).insert
    c (.address (AccountAddress.ofNat (calldataWord cd 196).toNat))).insert
    d (.bytes (calldataBytesPayload cd (4 + (calldataWord cd 228).toNat)))

theorem decodeCalldata_market_uint_address_bytes_eq (cd : ByteArray) (a b c d : Ident) :
    decodeCalldata [a, b, c, d] [marketParamsABIType, abiUInt256, abiAddress, .bytes] cd =
      if MarketWordAddressBytesBounds cd then some (marketWordAddressBytesArgs cd a b c d) else none := by
  have hhead : abiTupleHeadSize? [marketParamsABIType, abiUInt256, abiAddress, .bytes] = some 256 := by
    simp only [abiTupleHeadSize?, show isDynamicABIType marketParamsABIType = false from rfl,
      show staticABIEncodedSize? marketParamsABIType = some 160 from rfl,
      isDynamicABIType, staticABIEncodedSize?, abiUInt256, abiAddress, Bool.false_eq_true,
      ↓reduceIte, bind, Option.bind, pure]
  rw [decodeCalldata_dynamicValues cd _ _ 256 (by rfl) hhead]
  by_cases hs : 260 ≤ cd.size ∧ cd.size < 2 ^ 255
  swap
  · rw [if_neg hs, if_neg (show ¬ MarketWordAddressBytesBounds cd from fun hb ↦ hs ⟨hb.1, hb.2.1⟩)]
  rw [if_pos hs, decodeABIValues_market_cons (by omega) (by decide)]
  by_cases hc : (marketParamsFromCalldata cd).Canonical
  swap
  · simp only [hc, ↓reduceIte, Option.bind_none,
      show ¬ MarketWordAddressBytesBounds cd from fun hb ↦ hc hb.2.2.1]
  rw [if_pos hc, decodeABIValues_calldata_uint_cons_values (by omega) (by decide)]
  rw [decodeABIValues_calldata_address_bytes (by omega) (by decide)]
  by_cases hb : AddressBytesBounds cd 192
  · have hfull : MarketWordAddressBytesBounds cd := ⟨hs.1, hs.2, hc, hb⟩
    simp only [hb, ↓reduceIte, Option.map_some, Option.bind_some, hfull,
      decodeCalldata.insertValues, marketWordAddressBytesArgs]
  · have hbad : ¬ MarketWordAddressBytesBounds cd := fun h ↦ hb h.2.2.2
    simp only [hb, ↓reduceIte, Option.map_none, Option.bind_none, hbad]

end Benchmarks.Morpho.MorphoBlue
