import Benchmarks.Morpho.MetaMorphoV1_1.MarketParamsCalldata

/-! Calldata decoding of MarketParams followed by a uint256 cap. -/

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Morpho.MetaMorphoV1_1.SourceMemory

set_option maxRecDepth 2000

theorem submitCapCalldataHeadSize :
    abiTupleHeadSize? [.tuple marketParamsFieldTypes, abiUInt256] = some 192 := by
  simp only [abiTupleHeadSize?,
    show isDynamicABIType (.tuple marketParamsFieldTypes) = false from rfl,
    show isDynamicABIType abiUInt256 = false from rfl,
    show staticABIEncodedSize? (.tuple marketParamsFieldTypes) = some 160 from rfl,
    show staticABIEncodedSize? abiUInt256 = some 32 from rfl,
    Bool.false_eq_true, if_false, bind, Option.bind, Nat.add_zero]

def SubmitCapCalldataChecks (cd : ByteArray) : Prop :=
  196 ≤ cd.size ∧ MarketParamsCalldataChecks cd

instance (cd : ByteArray) : Decidable (SubmitCapCalldataChecks cd) :=
  inferInstanceAs (Decidable (_ ∧ _))

def submitCapCalldataLocals (cd : ByteArray) : Store :=
  (marketParamsCalldataLocals "marketParams" cd).insert "newSupplyCap"
    (uint256Value (calldataWord cd 164))

theorem submitCapCalldataDecode_long {cd : ByteArray}
    (hlo : 196 ≤ cd.size) (hhi : cd.size < 2 ^ 255 + 4) :
    decodeCalldata ["marketParams", "newSupplyCap"]
      [.tuple marketParamsFieldTypes, abiUInt256] cd =
      if MarketParamsChecks (marketParamsArgs cd) then
        some (submitCapCalldataLocals cd) else none := by
  have hlist : cd.toList.length = cd.size := by
    rw [byteArray_toList_eq, Array.length_toList]; rfl
  have hs : 160 ≤ (marketParamsArgs cd).size := by rw [marketParamsArgs_size]; omega
  have hdyn : isDynamicABIType (.tuple marketParamsFieldTypes) = false := rfl
  have hsize : staticABIEncodedSize? (.tuple marketParamsFieldTypes) = some 160 := rfl
  have hhead : abiTupleHeadSize? [.tuple marketParamsFieldTypes, abiUInt256] =
      some 192 := submitCapCalldataHeadSize
  have hvalue : decodeABIValue? (.tuple marketParamsFieldTypes)
      (marketParamsArgs cd).toList 0 =
      (decodeScalarWords? marketParamsFieldTypes (marketParamsArgs cd).toList 0).map
        (fun vs ↦ (.tuple vs, 160)) := scalarTupleValueDecode (by decide)
  have hu : decodeABIValue? abiUInt256 (marketParamsArgs cd).toList 160 =
      some (uint256Value (calldataWord cd 164), 192) := by
    have hl : (((marketParamsArgs cd).toList.drop 160).take 32).length = 32 := by
      simp only [List.length_take, List.length_drop, byteArray_toList_eq, Array.length_toList]
      change min 32 ((marketParamsArgs cd).size - 160) = 32
      rw [marketParamsArgs_size]
      omega
    simpa only [decode_word_at_eq_any (marketParamsArgs cd) 160
      (by rw [marketParamsArgs_size]; omega),
      marketParamsArgs_word (cd := cd) (off := 160) (by omega)] using
      decodeABIValue_uint256_ok hl
  simp only [decodeCalldata, hlist, Nat.not_lt.mpr (by omega : 4 ≤ cd.size), if_false,
    List.any_cons, List.any_nil, hdyn, show isDynamicABIType abiUInt256 = false from rfl,
    Bool.or_self, Bool.false_eq_true, false_and, List.isEmpty_cons, true_and,
    List.length_drop, Nat.not_le.mpr (by omega : cd.size - 4 < 2 ^ 255),
    solcTotalSizeDynamicGuard, decodeCalldata.decodeArgs, hhead, bind, Option.bind,
    Nat.not_lt.mpr (by omega : 192 ≤ cd.size - 4)]
  rw [← marketParamsArgs_list, decodeABIValues?]
  simp only [hdyn, Bool.false_eq_true, if_false, hsize, bind, Option.bind, Nat.zero_add,
    hvalue, marketParamsScalarDecode_long hs]
  by_cases hc : MarketParamsChecks (marketParamsArgs cd) <;>
    simp [hc, decodeABIValues?, hu, show isDynamicABIType abiUInt256 = false from rfl,
      show staticABIEncodedSize? abiUInt256 = some 32 from rfl,
      decodeCalldata.insertValues, submitCapCalldataLocals, marketParamsCalldataLocals]

theorem submitCapCalldataDecode_short {cd : ByteArray} (hlo : cd.size < 196) :
    decodeCalldata ["marketParams", "newSupplyCap"]
      [.tuple marketParamsFieldTypes, abiUInt256] cd = none := by
  have hlist : cd.toList.length = cd.size := by
    rw [byteArray_toList_eq, Array.length_toList]; rfl
  have hdyn : isDynamicABIType (.tuple marketParamsFieldTypes) = false := rfl
  have hhead : abiTupleHeadSize? [.tuple marketParamsFieldTypes, abiUInt256] =
      some 192 := submitCapCalldataHeadSize
  by_cases h4 : cd.size < 4
  · simp [decodeCalldata, hlist, h4]
  · simp [decodeCalldata, hlist, h4, hdyn,
      show isDynamicABIType abiUInt256 = false from rfl, solcTotalSizeDynamicGuard,
      show ¬ 2 ^ 255 ≤ cd.size - 4 by omega, decodeCalldata.decodeArgs, hhead,
      show cd.size - 4 < 192 by omega]

theorem submitCapCalldataDecode_huge {cd : ByteArray} (hhi : 2 ^ 255 + 4 ≤ cd.size) :
    decodeCalldata ["marketParams", "newSupplyCap"]
      [.tuple marketParamsFieldTypes, abiUInt256] cd = none := by
  have hlist : cd.toList.length = cd.size := by
    rw [byteArray_toList_eq, Array.length_toList]; rfl
  have hdyn : isDynamicABIType (.tuple marketParamsFieldTypes) = false := rfl
  simp [decodeCalldata, hlist, show ¬ cd.size < 4 by omega, hdyn,
    show isDynamicABIType abiUInt256 = false from rfl]
  intro h
  omega

theorem submitCapCalldataDecode (cd : ByteArray) :
    decodeCalldata ["marketParams", "newSupplyCap"]
      [.tuple marketParamsFieldTypes, abiUInt256] cd =
      if SubmitCapCalldataChecks cd then some (submitCapCalldataLocals cd) else none := by
  by_cases hlo : 196 ≤ cd.size
  · by_cases hhi : cd.size < 2 ^ 255 + 4
    · simpa only [SubmitCapCalldataChecks, MarketParamsCalldataChecks, hlo, hhi, true_and]
        using submitCapCalldataDecode_long hlo hhi
    · rw [submitCapCalldataDecode_huge (by omega)]
      simp only [SubmitCapCalldataChecks, MarketParamsCalldataChecks, hhi, false_and,
        and_false, if_false]
  · rw [submitCapCalldataDecode_short (by omega)]
    simp only [SubmitCapCalldataChecks, hlo, false_and, if_false]

end Benchmarks.Morpho.MetaMorphoV1_1.SourceMemory
