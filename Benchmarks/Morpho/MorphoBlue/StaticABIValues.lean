import Benchmarks.Morpho.MorphoBlue.MarketDynamicABI

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.Morpho.MorphoBlue
set_option maxRecDepth 1000

-- LIBRARY CANDIDATE: separate a nonempty static calldata head's size checks from value decoding.
theorem decodeCalldata_staticValues (cd : ByteArray) (names : List Ident) (types : List ABIType)
    (head : Nat) (hne : types ≠ []) (hdyn : types.any isDynamicABIType = false)
    (htotal : solcTotalSizeDynamicGuard types = false) (hhead : abiTupleHeadSize? types = some head) :
    decodeCalldata names types cd =
      if head + 4 ≤ cd.size ∧ cd.size < 2 ^ 255 + 4 then
        ((decodeABIValues? types (cd.toList.drop 4) 0 0 head head).map Prod.fst).bind
          (fun values ↦ decodeCalldata.insertValues names values ∅)
      else none := by
  have htlen : cd.toList.length = cd.size := by
    rw [byteArray_toList_eq, Array.length_toList]; rfl
  unfold decodeCalldata
  simp only [htlen, hdyn, htotal, Bool.false_eq_true, false_and, List.length_drop, ↓reduceIte]
  by_cases h4 : cd.size < 4
  · simp only [h4, ↓reduceIte, show ¬ (head + 4 ≤ cd.size ∧ cd.size < 2 ^ 255 + 4) by omega]
  · simp only [h4, ↓reduceIte]
    cases types with
    | nil => contradiction
    | cons ty rest =>
      simp only [List.isEmpty_cons, Bool.false_eq_true, and_self, true_and]
      by_cases hh : cd.size < 2 ^ 255 + 4
      swap
      · simp only [show 2 ^ 255 ≤ cd.size - 4 by omega, ↓reduceIte,
          show ¬ (head + 4 ≤ cd.size ∧ cd.size < 2 ^ 255 + 4) by omega]
      simp only [show ¬ 2 ^ 255 ≤ cd.size - 4 by omega, and_false, ↓reduceIte,
        decodeCalldata.decodeArgs, hhead, bind, Option.bind, List.length_drop, htlen]
      by_cases hshort : cd.size - 4 < head
      · simp only [hshort, ↓reduceIte, show ¬ (head + 4 ≤ cd.size ∧ cd.size < 2 ^ 255 + 4) by omega]
      · simp only [hshort, ↓reduceIte, show head + 4 ≤ cd.size ∧ cd.size < 2 ^ 255 + 4 by omega]
        cases decodeABIValues? (ty :: rest) (cd.toList.drop 4) 0 0 head head with
        | none => rfl
        | some pair =>
          simp only [Option.bind_some, Option.map_some]
          cases decodeCalldata.insertValues names pair.1 ∅ <;> rfl

-- LIBRARY CANDIDATE: a canonical address followed by an arbitrary ABI tail.
theorem decodeABIValues_calldata_address_cons_values {cd : ByteArray} {types : List ABIType}
    {cursor head last : Nat} (hb : 4 + cursor + 32 ≤ cd.size) (hh : cursor + 36 < 2 ^ 64) :
    (decodeABIValues? (abiAddress :: types) (cd.toList.drop 4) 0 cursor head last).map Prod.fst =
      if (calldataWord cd (4 + cursor)).toNat < EVM.addressModulus then
        ((decodeABIValues? types (cd.toList.drop 4) 0 (cursor + 32) head
          (max last (cursor + 32))).map Prod.fst).map
            (List.cons (.address (AccountAddress.ofNat (calldataWord cd (4 + cursor)).toNat)))
      else none := by
  rw [decodeABIValues_static_cons rfl rfl, decodeABIValue_scalarWord_eq (by decide)]
  by_cases ha : (calldataWord cd (4 + cursor)).toNat < EVM.addressModulus
  · rw [decodeScalarWord_calldata_address (by omega) (by omega) (by simpa only [Nat.add_comm] using ha)]
    simp only [Nat.zero_add, Option.bind_some, if_pos ha, ↓reduceIte, Option.map_map, Function.comp_def]
    rw [Nat.add_comm cursor 4]
  · rw [decodeScalarWord_calldata_address_noncanonical (by omega) (by omega) (by simpa only [Nat.add_comm] using ha)]
    simp only [if_neg ha, Option.bind_none, Option.map_none]

end Benchmarks.Morpho.MorphoBlue
