import Benchmarks.Morpho.MorphoBlue.StaticABIValues

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.Morpho.MorphoBlue
set_option maxRecDepth 1000

def MarketTwoWordsTwoAddressesBounds (cd : ByteArray) : Prop :=
  292 ≤ cd.size ∧ cd.size < 2 ^ 255 + 4 ∧ (marketParamsFromCalldata cd).Canonical ∧
    (calldataWord cd 228).toNat < EVM.addressModulus ∧
    (calldataWord cd 260).toNat < EVM.addressModulus

instance (cd : ByteArray) : Decidable (MarketTwoWordsTwoAddressesBounds cd) := by
  unfold MarketTwoWordsTwoAddressesBounds
  infer_instance

def marketTwoWordsTwoAddressesArgs (cd : ByteArray) (a b c d e : Ident) : Store :=
  (((((∅ : Store).insert a (marketParamsFromCalldata cd).value).insert
    b (.int (Int.ofNat (calldataWord cd 164).toNat))).insert
    c (.int (Int.ofNat (calldataWord cd 196).toNat))).insert
    d (.address (AccountAddress.ofNat (calldataWord cd 228).toNat))).insert
    e (.address (AccountAddress.ofNat (calldataWord cd 260).toNat))

theorem decodeCalldata_market_two_uint_two_address_eq (cd : ByteArray) (a b c d e : Ident) :
    decodeCalldata [a, b, c, d, e] [marketParamsABIType, abiUInt256, abiUInt256, abiAddress, abiAddress] cd =
      if MarketTwoWordsTwoAddressesBounds cd then some (marketTwoWordsTwoAddressesArgs cd a b c d e) else none := by
  have hhead : abiTupleHeadSize? [marketParamsABIType, abiUInt256, abiUInt256, abiAddress, abiAddress] = some 288 := by
    simp only [abiTupleHeadSize?, show isDynamicABIType marketParamsABIType = false from rfl,
      show staticABIEncodedSize? marketParamsABIType = some 160 from rfl,
      isDynamicABIType, staticABIEncodedSize?, abiUInt256, abiAddress, Bool.false_eq_true,
      ↓reduceIte, bind, Option.bind, pure]
  rw [decodeCalldata_staticValues cd _ _ 288 (by decide) rfl rfl hhead]
  by_cases hs : 292 ≤ cd.size ∧ cd.size < 2 ^ 255 + 4
  swap
  · rw [if_neg hs, if_neg (show ¬ MarketTwoWordsTwoAddressesBounds cd from fun hb ↦ hs ⟨hb.1, hb.2.1⟩)]
  rw [if_pos hs, decodeABIValues_market_cons (by omega) (by decide)]
  by_cases hc : (marketParamsFromCalldata cd).Canonical
  swap
  · simp only [hc, ↓reduceIte, Option.bind_none,
      show ¬ MarketTwoWordsTwoAddressesBounds cd from fun hb ↦ hc hb.2.2.1]
  rw [if_pos hc, decodeABIValues_calldata_uint_cons_values (by omega) (by decide)]
  rw [decodeABIValues_calldata_uint_cons_values (by omega) (by decide)]
  rw [decodeABIValues_calldata_address_cons_values (by omega) (by decide)]
  by_cases ha : (calldataWord cd 228).toNat < EVM.addressModulus
  swap
  · simp only [ha, ↓reduceIte, Option.bind_none, Option.map_none,
      show ¬ MarketTwoWordsTwoAddressesBounds cd from fun hb ↦ ha hb.2.2.2.1]
  rw [if_pos ha, decodeABIValues_calldata_address_cons_values (by omega) (by decide)]
  by_cases hr : (calldataWord cd 260).toNat < EVM.addressModulus
  · have hb : MarketTwoWordsTwoAddressesBounds cd := ⟨hs.1, hs.2, hc, ha, hr⟩
    simp only [hr, ↓reduceIte, Option.map_some, Option.bind_some, hb, decodeABIValues?,
      pure, decodeCalldata.insertValues, marketTwoWordsTwoAddressesArgs]
  · simp only [hr, ↓reduceIte, Option.bind_none, Option.map_none,
      show ¬ MarketTwoWordsTwoAddressesBounds cd from fun hb ↦ hr hb.2.2.2.2]

end Benchmarks.Morpho.MorphoBlue
