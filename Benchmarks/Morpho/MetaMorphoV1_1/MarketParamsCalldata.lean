import Benchmarks.Morpho.MetaMorphoV1_1.MarketParamsHashSource

/-! Decoding a single MarketParams tuple from external calldata. -/

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Morpho.MetaMorphoV1_1.SourceMemory

def marketParamsArgs (cd : ByteArray) : ByteArray := cd.extract 4 cd.size

theorem marketParamsArgs_list (cd : ByteArray) :
    (marketParamsArgs cd).toList = cd.toList.drop 4 := by
  rw [marketParamsArgs, extract_toList]
  exact List.take_of_length_le (by
    simp only [List.length_drop, byteArray_toList_eq, Array.length_toList]
    rfl)

theorem marketParamsArgs_size (cd : ByteArray) :
    (marketParamsArgs cd).size = cd.size - 4 := by
  simp [marketParamsArgs, ByteArray.size_extract]

theorem marketParamsArgs_word {cd : ByteArray} {off : Nat} (hin : 4 + off + 32 ≤ cd.size) :
    calldataWord (marketParamsArgs cd) off = calldataWord cd (4 + off) := by
  have hw : bytesToWord (((marketParamsArgs cd).toList.drop off).take 32) =
      calldataWord (marketParamsArgs cd) off :=
    decode_word_at_eq_any (marketParamsArgs cd) off (by rw [marketParamsArgs_size]; omega)
  rw [← hw, marketParamsArgs_list, List.drop_drop]
  exact decode_word_at_eq_any cd (4 + off) hin

def MarketParamsCalldataChecks (cd : ByteArray) : Prop :=
  cd.size < 2 ^ 255 + 4 ∧ MarketParamsChecks (marketParamsArgs cd)

instance (cd : ByteArray) : Decidable (MarketParamsCalldataChecks cd) :=
  inferInstanceAs (Decidable (_ ∧ _))

def marketParamsCalldataLocals (name : Ident) (cd : ByteArray) : Store :=
  (∅ : Store).insert name (.tuple (marketParamsFields (marketParamsArgs cd)))

theorem marketParamsCalldataDecode_long {cd : ByteArray} (name : Ident)
    (hlo : 164 ≤ cd.size) (hhi : cd.size < 2 ^ 255 + 4) :
    decodeCalldata [name] [.tuple marketParamsFieldTypes] cd =
      if MarketParamsChecks (marketParamsArgs cd) then
        some (marketParamsCalldataLocals name cd) else none := by
  have hlist : cd.toList.length = cd.size := by
    rw [byteArray_toList_eq, Array.length_toList]; rfl
  have hs : 160 ≤ (marketParamsArgs cd).size := by rw [marketParamsArgs_size]; omega
  have hh : (marketParamsArgs cd).size < 2 ^ 255 := by rw [marketParamsArgs_size]; omega
  have hdyn : isDynamicABIType (.tuple marketParamsFieldTypes) = false := rfl
  have hsize : staticABIEncodedSize? (.tuple marketParamsFieldTypes) = some 160 := rfl
  have hhead : abiTupleHeadSize? [.tuple marketParamsFieldTypes] = some 160 := by
    simp only [abiTupleHeadSize?, hdyn, hsize, Bool.false_eq_true, if_false, bind,
      Option.bind, Nat.add_zero]
  have hvalue : decodeABIValue? (.tuple marketParamsFieldTypes)
      (marketParamsArgs cd).toList 0 =
        (decodeScalarWords? marketParamsFieldTypes (marketParamsArgs cd).toList 0).map
          (fun vs ↦ (.tuple vs, 160)) := scalarTupleValueDecode (by decide)
  simp only [decodeCalldata, hlist, Nat.not_lt.mpr (by omega : 4 ≤ cd.size), if_false,
    List.any_cons, List.any_nil, hdyn, Bool.or_self, Bool.false_eq_true, false_and,
    List.isEmpty_cons, true_and, List.length_drop,
    Nat.not_le.mpr (by omega : cd.size - 4 < 2 ^ 255), solcTotalSizeDynamicGuard,
    decodeCalldata.decodeArgs, hhead, bind, Option.bind,
    Nat.not_lt.mpr (by omega : 160 ≤ cd.size - 4)]
  rw [← marketParamsArgs_list]
  rw [decodeABIValues?]
  simp only [hdyn, Bool.false_eq_true, if_false, hsize, bind, Option.bind, Nat.zero_add,
    hvalue, marketParamsScalarDecode_long hs]
  by_cases hc : MarketParamsChecks (marketParamsArgs cd) <;>
    simp [hc, decodeABIValues?, decodeCalldata.insertValues, marketParamsCalldataLocals]

theorem marketParamsCalldataDecode_short {cd : ByteArray} (name : Ident)
    (hlo : cd.size < 164) :
    decodeCalldata [name] [.tuple marketParamsFieldTypes] cd = none := by
  have hlist : cd.toList.length = cd.size := by
    rw [byteArray_toList_eq, Array.length_toList]; rfl
  have hdyn : isDynamicABIType (.tuple marketParamsFieldTypes) = false := rfl
  have hsize : staticABIEncodedSize? (.tuple marketParamsFieldTypes) = some 160 := rfl
  have hhead : abiTupleHeadSize? [.tuple marketParamsFieldTypes] = some 160 := by
    simp only [abiTupleHeadSize?, hdyn, hsize, Bool.false_eq_true, if_false, bind,
      Option.bind, Nat.add_zero]
  by_cases h4 : cd.size < 4
  · simp [decodeCalldata, hlist, h4]
  · simp [decodeCalldata, hlist, h4, hdyn, solcTotalSizeDynamicGuard,
      show ¬ 2 ^ 255 ≤ cd.size - 4 by omega, decodeCalldata.decodeArgs, hhead,
      show cd.size - 4 < 160 by omega]

theorem marketParamsCalldataDecode_huge {cd : ByteArray} (name : Ident)
    (hhi : 2 ^ 255 + 4 ≤ cd.size) :
    decodeCalldata [name] [.tuple marketParamsFieldTypes] cd = none := by
  have hlist : cd.toList.length = cd.size := by
    rw [byteArray_toList_eq, Array.length_toList]; rfl
  have hdyn : isDynamicABIType (.tuple marketParamsFieldTypes) = false := rfl
  simp [decodeCalldata, hlist, show ¬ cd.size < 4 by omega, hdyn]
  intro h
  omega

theorem marketParamsCalldataDecode (cd : ByteArray) (name : Ident) :
    decodeCalldata [name] [.tuple marketParamsFieldTypes] cd =
      if MarketParamsCalldataChecks cd then some (marketParamsCalldataLocals name cd)
      else none := by
  by_cases hlo : 164 ≤ cd.size
  · by_cases hhi : cd.size < 2 ^ 255 + 4
    · simpa only [MarketParamsCalldataChecks, hhi, true_and] using
        marketParamsCalldataDecode_long name hlo hhi
    · rw [marketParamsCalldataDecode_huge name (by omega)]
      simp only [MarketParamsCalldataChecks, hhi, false_and, if_false]
  · rw [marketParamsCalldataDecode_short name (by omega)]
    have hc : ¬ MarketParamsChecks (marketParamsArgs cd) := by
      intro h
      have hs := h.1
      rw [marketParamsArgs_size] at hs
      omega
    simp [MarketParamsCalldataChecks, hc]

end Benchmarks.Morpho.MetaMorphoV1_1.SourceMemory
