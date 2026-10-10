import Benchmarks.EAS.Attester.ArrayABI

/-! Source decoding of a single dynamic calldata argument. -/

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory

namespace Benchmarks.Morpho.MetaMorphoV1_1

-- LIBRARY CANDIDATE: isolate the common head checks from a dynamic argument's decoder.
def decodeSingleDynamic? (ty : ABIType) (cd : ByteArray) : Option Value := do
  if cd.size < 36 ∨ 2 ^ 255 ≤ cd.size then none else do
  let off := (calldataWord cd 4).toNat
  if solcMaxU64 < off then none else do
  let value ← decodeABIValue? ty (cd.toList.drop 4) off
  some value.1

theorem decodeCalldata_single_dynamic (ty : ABIType) (name : Ident) (cd : ByteArray)
    (hdyn : isDynamicABIType ty = true) :
    decodeCalldata [name] [ty] cd =
      (decodeSingleDynamic? ty cd).map (fun value ↦ (∅ : Store).insert name value) := by
  have hl : cd.toList.length = cd.size := by
    rw [byteArray_toList_eq, Array.length_toList]; rfl
  by_cases hs : cd.size < 36
  · rw [decodeCalldata_head_none_short (types := []) (ty := ty) (headSize := 32)
      (by simp [abiTupleHeadSize?, hdyn]) hs]
    simp only [decodeSingleDynamic?, hs, true_or, if_true, Option.map_none]
  by_cases hh : 2 ^ 255 ≤ cd.size
  · simp only [decodeCalldata, hl, show ¬ cd.size < 4 by omega, if_false,
      List.any_cons, hdyn, Bool.true_or, true_and, hh, if_true,
      decodeSingleDynamic?, or_true, Option.map_none]
  have hr := readNat_drop4_zero_eq_calldataWord (cd := cd) (by omega)
  simp only [decodeCalldata, hl, show ¬ cd.size < 4 by omega, if_false,
    List.any_cons, hdyn, Bool.true_or, hh, List.isEmpty_cons,
    List.length_drop, show ¬ 2 ^ 255 ≤ cd.size - 4 by omega, and_false,
    solcTotalSizeDynamicGuard, decodeCalldata.decodeArgs, abiTupleHeadSize?,
    bind, Option.bind, show ¬ cd.size - 4 < 32 by omega, decodeABIValues?, Nat.zero_add,
    Nat.reduceAdd, hr, solcMaxLen_modern, if_true, decodeSingleDynamic?, hs, false_or]
  by_cases hoff : solcMaxU64 < (calldataWord cd 4).toNat
  · simp only [hoff, if_true, Option.map_none]
  · simp only [hoff, if_false]
    cases hv : decodeABIValue? ty (cd.toList.drop 4) (calldataWord cd 4).toNat <;>
      simp only [Option.map_none, Option.map_some, decodeCalldata.insertValues]

theorem decodeSingleDynamic_facts {ty : ABIType} {cd : ByteArray} {value : Value}
    (hd : decodeSingleDynamic? ty cd = some value) :
    ∃ ending, 36 ≤ cd.size ∧ cd.size < 2 ^ 255 ∧
      (calldataWord cd 4).toNat ≤ solcMaxU64 ∧
      decodeABIValue? ty (cd.toList.drop 4) (calldataWord cd 4).toNat =
        some (value, ending) := by
  unfold decodeSingleDynamic? at hd
  by_cases hs : cd.size < 36 ∨ 2 ^ 255 ≤ cd.size
  · simp only [hs, if_true] at hd; cases hd
  by_cases hoff : solcMaxU64 < (calldataWord cd 4).toNat
  · simp only [hs, hoff, if_false, if_true] at hd; cases hd
  simp only [hs, hoff, if_false] at hd
  cases hv : decodeABIValue? ty (cd.toList.drop 4) (calldataWord cd 4).toNat with
  | none => simp only [hv, bind, Option.bind_none] at hd; cases hd
  | some pair =>
      simp only [hv, bind, Option.bind_some, Option.some.injEq] at hd
      exact ⟨pair.2, by omega, by omega, by omega, hd ▸ rfl⟩

end Benchmarks.Morpho.MetaMorphoV1_1
