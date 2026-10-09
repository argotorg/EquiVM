import Benchmarks.Morpho.MorphoBlue.CalldataBytesABI
import Benchmarks.Morpho.MorphoBlue.MarketParamsABI

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.Morpho.MorphoBlue
set_option maxRecDepth 1000

-- LIBRARY CANDIDATE: separate modern dynamic calldata's size guard from value decoding.
theorem decodeCalldata_dynamicHead (cd : ByteArray) (names : List Ident) (types : List ABIType)
    (head : Nat) (hdyn : types.any isDynamicABIType = true)
    (hhead : abiTupleHeadSize? types = some head) :
    decodeCalldata names types cd =
      if head + 4 ≤ cd.size ∧ cd.size < 2 ^ 255 then
        (decodeABIValues? types (cd.toList.drop 4) 0 0 head head).bind
          (fun values => decodeCalldata.insertValues names values.1 ∅)
      else none := by
  have htlen : cd.toList.length = cd.size := by
    rw [byteArray_toList_eq, Array.length_toList]; rfl
  have hne : types ≠ [] := by intro hz; rw [hz] at hdyn; contradiction
  unfold decodeCalldata
  simp only [htlen, hdyn, true_and, List.length_drop]
  by_cases h4 : cd.size < 4
  · simp only [h4, ↓reduceIte, show ¬ (head + 4 ≤ cd.size ∧ cd.size < 2 ^ 255) by omega]
  · simp only [h4, ↓reduceIte]
    by_cases hh : cd.size < 2 ^ 255
    swap
    · simp only [show 2 ^ 255 ≤ cd.size by omega, ↓reduceIte,
        show ¬ (head + 4 ≤ cd.size ∧ cd.size < 2 ^ 255) by omega]
    simp only [show ¬ 2 ^ 255 ≤ cd.size by omega, show ¬ 2 ^ 255 ≤ cd.size - 4 by omega,
      and_false, ↓reduceIte]
    cases types with
    | nil => contradiction
    | cons ty rest =>
      simp only [decodeCalldata.decodeArgs, hhead, bind, Option.bind, List.length_drop, htlen]
      by_cases hs : head ≤ cd.size - 4
      · simp only [show ¬ cd.size - 4 < head by omega, ↓reduceIte, and_self,
          show head + 4 ≤ cd.size ∧ cd.size < 2 ^ 255 by omega]
        cases decodeABIValues? (ty :: rest) (cd.toList.drop 4) 0 0 head head with
        | none => rfl
        | some pair =>
          simp only [Option.bind_some]
          cases decodeCalldata.insertValues names pair.1 ∅ <;> rfl
      · simp only [show cd.size - 4 < head by omega, ↓reduceIte,
          show ¬ (head + 4 ≤ cd.size ∧ cd.size < 2 ^ 255) by omega]

end Benchmarks.Morpho.MorphoBlue
