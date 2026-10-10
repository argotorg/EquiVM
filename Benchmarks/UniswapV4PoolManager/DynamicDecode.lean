import Benchmarks.UniswapV4PoolManager.Values

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.UniswapV4PoolManager

-- LIBRARY CANDIDATE: the single dynamic ABI head, independent of its value type.
theorem decodeCalldata_singleDynamic_eq (cd : ByteArray) (ty : ABIType) (name : Ident)
    (hdyn : isDynamicABIType ty = true) :
    decodeCalldata [name] [ty] cd =
      if cd.size < 36 ∨ 2 ^ 255 ≤ cd.size then none
      else if solcMaxU64 < (calldataWord cd 4).toNat then none
      else (decodeABIValue? ty (cd.toList.drop 4)
        (calldataWord cd 4).toNat).map (fun p ↦ (∅ : Store).insert name p.1) := by
  have htlen : cd.toList.length = cd.size := by
    rw [byteArray_toList_eq, Array.length_toList]; rfl
  have hhead : abiTupleHeadSize? [ty] = some 32 := by
    simp [abiTupleHeadSize?, hdyn]
  unfold decodeCalldata
  simp only [htlen, List.length_drop, List.any_cons, List.any_nil,
    hdyn, Bool.true_or, true_and,
    List.isEmpty_cons]
  by_cases h4 : cd.size < 4
  · simp only [h4, if_true, show cd.size < 36 ∨ 2 ^ 255 ≤ cd.size by omega]
  · simp only [h4, if_false]
    by_cases hbig : 2 ^ 255 ≤ cd.size
    · simp only [hbig, if_true, or_true]
    · simp only [hbig, and_false, if_false, show ¬ 2 ^ 255 ≤ cd.size - 4 by omega,
        decodeCalldata.decodeArgs, hhead, bind, Option.bind, List.length_drop, htlen, or_false]
      by_cases hshort : cd.size - 4 < 32
      · simp only [hshort, if_true, show cd.size < 36 by omega]
      · have hr := readNat_drop4_zero_eq_calldataWord (cd := cd) (by omega)
        simp only [hshort, if_false, show ¬ cd.size < 36 by omega,
          decodeABIValues?, hdyn,
          if_true, Nat.add_zero, Nat.zero_add, hr, bind, Option.bind, solcMaxLen]
        by_cases ho : solcMaxU64 < (calldataWord cd 4).toNat
        · simp only [ho, if_true]
        · simp only [ho, if_false]
          cases hv : decodeABIValue? ty (cd.toList.drop 4)
              (calldataWord cd 4).toNat with
          | none => rfl
          | some p => simp only [decodeABIValues?, Option.bind_some,
              decodeCalldata.insertValues, Option.map_some]

end Benchmarks.UniswapV4PoolManager
