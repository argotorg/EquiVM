import Benchmarks.Morpho.MorphoBlue.StaticABIValues

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.Morpho.MorphoBlue
set_option maxRecDepth 1000

def MarketWordTwoAddressesBounds (cd : ByteArray) : Prop :=
  260 ≤ cd.size ∧ cd.size < 2 ^ 255 + 4 ∧ (marketParamsFromCalldata cd).Canonical ∧
    (calldataWord cd 196).toNat < EVM.addressModulus ∧
    (calldataWord cd 228).toNat < EVM.addressModulus

instance (cd : ByteArray) : Decidable (MarketWordTwoAddressesBounds cd) := by
  unfold MarketWordTwoAddressesBounds
  infer_instance

def marketWordTwoAddressesArgs (cd : ByteArray) (a b c d : Ident) : Store :=
  ((((∅ : Store).insert a (marketParamsFromCalldata cd).value).insert
    b (.int (Int.ofNat (calldataWord cd 164).toNat))).insert
    c (.address (AccountAddress.ofNat (calldataWord cd 196).toNat))).insert
    d (.address (AccountAddress.ofNat (calldataWord cd 228).toNat))

theorem decodeCalldata_market_uint_two_address_eq (cd : ByteArray) (a b c d : Ident) :
    decodeCalldata [a, b, c, d] [marketParamsABIType, abiUInt256, abiAddress, abiAddress] cd =
      if MarketWordTwoAddressesBounds cd then some (marketWordTwoAddressesArgs cd a b c d) else none := by
  have hhead : abiTupleHeadSize? [marketParamsABIType, abiUInt256, abiAddress, abiAddress] = some 256 := by
    simp only [abiTupleHeadSize?, show isDynamicABIType marketParamsABIType = false from rfl,
      show staticABIEncodedSize? marketParamsABIType = some 160 from rfl,
      isDynamicABIType, staticABIEncodedSize?, abiUInt256, abiAddress, Bool.false_eq_true,
      ↓reduceIte, bind, Option.bind, pure]
  rw [decodeCalldata_staticValues cd _ _ 256 (by decide) rfl rfl hhead]
  by_cases hs : 260 ≤ cd.size ∧ cd.size < 2 ^ 255 + 4
  swap
  · rw [if_neg hs, if_neg (show ¬ MarketWordTwoAddressesBounds cd from fun hb ↦ hs ⟨hb.1, hb.2.1⟩)]
  rw [if_pos hs, decodeABIValues_market_cons (by omega) (by decide)]
  by_cases hc : (marketParamsFromCalldata cd).Canonical
  swap
  · simp only [hc, ↓reduceIte, Option.bind_none,
      show ¬ MarketWordTwoAddressesBounds cd from fun hb ↦ hc hb.2.2.1]
  rw [if_pos hc, decodeABIValues_calldata_uint_cons_values (by omega) (by decide)]
  rw [decodeABIValues_calldata_address_cons_values (by omega) (by decide)]
  by_cases ha : (calldataWord cd 196).toNat < EVM.addressModulus
  swap
  · simp only [ha, ↓reduceIte, Option.bind_none, Option.map_none,
      show ¬ MarketWordTwoAddressesBounds cd from fun hb ↦ ha hb.2.2.2.1]
  rw [if_pos ha, decodeABIValues_calldata_address_cons_values (by omega) (by decide)]
  by_cases hr : (calldataWord cd 228).toNat < EVM.addressModulus
  · have hb : MarketWordTwoAddressesBounds cd := ⟨hs.1, hs.2, hc, ha, hr⟩
    simp only [hr, ↓reduceIte, Option.map_some, Option.bind_some, hb, decodeABIValues?,
      pure, decodeCalldata.insertValues, marketWordTwoAddressesArgs]
  · simp only [hr, ↓reduceIte, Option.bind_none, Option.map_none,
      show ¬ MarketWordTwoAddressesBounds cd from fun hb ↦ hr hb.2.2.2.2]

end Benchmarks.Morpho.MorphoBlue
