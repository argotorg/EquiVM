import Benchmarks.Morpho.MorphoBlue.DynamicABIFields

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.Morpho.MorphoBlue
set_option maxRecDepth 1000

-- LIBRARY CANDIDATE: discard ABI extent metadata before binding named calldata arguments.
theorem decodeCalldata_dynamicValues (cd : ByteArray) (names : List Ident) (types : List ABIType)
    (head : Nat) (hdyn : types.any isDynamicABIType = true)
    (hhead : abiTupleHeadSize? types = some head) :
    decodeCalldata names types cd =
      if head + 4 ≤ cd.size ∧ cd.size < 2 ^ 255 then
        ((decodeABIValues? types (cd.toList.drop 4) 0 0 head head).map Prod.fst).bind
          (fun values ↦ decodeCalldata.insertValues names values ∅)
      else none := by
  rw [decodeCalldata_dynamicHead cd names types head hdyn hhead]
  simp only [Option.bind_map, Function.comp_def]

instance (p : MarketParamsWords) : Decidable p.Canonical := by
  unfold MarketParamsWords.Canonical
  infer_instance

theorem decodeABIValues_market_cons {cd : ByteArray} {types : List ABIType} {head last : Nat}
    (hb : 164 ≤ cd.size) (hl : 160 ≤ last) :
    (decodeABIValues? (marketParamsABIType :: types) (cd.toList.drop 4) 0 0 head last).map Prod.fst =
      if (marketParamsFromCalldata cd).Canonical then
        ((decodeABIValues? types (cd.toList.drop 4) 0 160 head last).map Prod.fst).map
          (List.cons (marketParamsFromCalldata cd).value)
      else none := by
  rw [decodeABIValues_static_cons rfl rfl]
  by_cases hc : (marketParamsFromCalldata cd).Canonical
  · rw [decodeABIValue_marketParams_ok hb hc]
    simp only [Option.bind_some, Nat.zero_add, ↓reduceIte, max_eq_left hl, hc,
      Option.map_map, Function.comp_def]
  · have hn : decodeABIValue? marketParamsABIType (cd.toList.drop 4) 0 = none := by
      rw [marketParamsABIType, decodeABIValue_scalarTuple_eq (by decide),
        decodeScalarWords_marketParams_noncanonical hb hc]
      rfl
    rw [hn]
    simp only [hc, ↓reduceIte, Option.bind_none, Option.map_none]

-- LIBRARY CANDIDATE: scalar word decoding with irrelevant extent metadata discarded.
theorem decodeABIValues_calldata_uint_cons_values {cd : ByteArray} {types : List ABIType}
    {cursor head last : Nat} (hb : 4 + cursor + 32 ≤ cd.size) (hh : cursor + 36 < 2 ^ 64) :
    (decodeABIValues? (abiUInt256 :: types) (cd.toList.drop 4) 0 cursor head last).map Prod.fst =
      ((decodeABIValues? types (cd.toList.drop 4) 0 (cursor + 32) head
        (max last (cursor + 32))).map Prod.fst).map
        (List.cons (.int (Int.ofNat (calldataWord cd (4 + cursor)).toNat))) := by
  rw [decodeABIValues_calldata_uint_cons hb hh]
  simp only [Option.map_map, Function.comp_def]

end Benchmarks.Morpho.MorphoBlue
