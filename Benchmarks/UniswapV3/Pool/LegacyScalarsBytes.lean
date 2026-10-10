import Benchmarks.UniswapV3.Pool.ScalarPrefixDecode

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.UniswapV3.Pool

-- LIBRARY CANDIDATE: a legacy scalar tuple followed by one dynamic-bytes argument.
theorem decodeCalldata_legacyScalarsBytes_head (cd : ByteArray)
    (types : List ABIType) (names : List Ident)
    (hscalar : types.all isABIScalarWordType = true) :
    decodeCalldataWithMode .legacySolc05 names (types ++ [abiBytes]) cd =
      if cd.size < 4 + 32 * (types.length + 1) then none else
      (do
        let values ← decodeScalarWordsWithMode? .legacySolc05 types (cd.toList.drop 4) 0
        if 2 ^ 32 < (calldataWord cd (4 + 32 * types.length)).toNat then none else
        let (value, _) ← decodeABIValue? abiBytes (cd.toList.drop 4)
          (calldataWord cd (4 + 32 * types.length)).toNat .legacySolc05
        decodeCalldata.insertValues names (values ++ [value]) ∅) := by
  have htlen : cd.toList.length = cd.size := by rw [byteArray_toList_eq, Array.length_toList]; rfl
  have hhead := abiTupleHeadSize_scalarsBytes hscalar
  have hnonempty : types ++ [abiBytes] ≠ [] := by simp
  simp only [decodeCalldataWithMode, decodeCalldata, ite_self, htlen]
  by_cases h4 : cd.size < 4
  · simp only [if_pos h4, if_pos (by omega : cd.size < 4 + 32 * (types.length + 1))]
  rw [if_neg h4]
  have hargs : decodeCalldata.decodeArgs .legacySolc05 names (types ++ [abiBytes])
      (cd.toList.drop 4) (∅ : Store) =
      (do
        if cd.size - 4 < 32 * (types.length + 1) then none else
        let (values, stop) ← decodeABIValues? (types ++ [abiBytes]) (cd.toList.drop 4) 0 0
          (32 * (types.length + 1)) (32 * (types.length + 1)) .legacySolc05
        let store ← decodeCalldata.insertValues names values ∅
        some (store, stop)) := by
    rw [decodeCalldata.decodeArgs]
    · simp only [hhead, bind, Option.bind, List.length_drop, htlen]
      split
      · rfl
      · cases decodeABIValues? (types ++ [abiBytes]) (cd.toList.drop 4) 0 0
          (32 * (types.length + 1)) (32 * (types.length + 1)) .legacySolc05 <;> rfl
    · exact hnonempty
  rw [hargs]
  by_cases hshort : cd.size < 4 + 32 * (types.length + 1)
  · simp [hshort, show cd.size - 4 < 32 * (types.length + 1) by omega]
  rw [if_neg hshort]
  simp only [if_neg (by omega : ¬ cd.size - 4 < 32 * (types.length + 1))]
  rw [decodeABIValues_scalarPrefix_eq hscalar (by omega)]
  cases hv : decodeScalarWordsWithMode? .legacySolc05 types (cd.toList.drop 4) 0 with
  | none => rfl
  | some values =>
      simp only [bind, Option.bind, decodeABIValues?, isDynamicABIType, if_true, Nat.zero_add]
      rw [readNat_drop4_at_eq_calldataWord (cd := cd) (32 * types.length) (by omega)]
      simp only [solcMaxLen, solcMaxLenV1,
        show (4294967296 : Nat) = 2 ^ 32 from rfl]
      by_cases hoff : 2 ^ 32 < (calldataWord cd (4 + 32 * types.length)).toNat
      · simp only [if_pos hoff]
      simp only [if_neg hoff]
      cases hd : decodeABIValue? abiBytes (cd.toList.drop 4)
          (calldataWord cd (4 + 32 * types.length)).toNat .legacySolc05 with
      | none => rfl
      | some result =>
          rcases result with ⟨value, stop⟩
          dsimp only
          cases decodeCalldata.insertValues names (values ++ [value]) ∅ <;> rfl

end Benchmarks.UniswapV3.Pool
