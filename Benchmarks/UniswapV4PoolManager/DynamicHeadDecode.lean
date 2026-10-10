import Benchmarks.UniswapV4PoolManager.DynamicDecode

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.UniswapV4PoolManager

-- LIBRARY CANDIDATE: expose the modern calldata guard and arbitrary dynamic head.
theorem decodeCalldata_dynamicHead (names : List Ident) (types : List ABIType) (cd : ByteArray) (head : Nat)
    (hdyn : types.any isDynamicABIType = true) (hhead : abiTupleHeadSize? types = some head) :
    decodeCalldata names types cd =
      if cd.size < 4+head ∨ 2^255 ≤ cd.size then none
      else (decodeABIValues? types (cd.toList.drop 4) 0 0 head head).bind
        (fun values => decodeCalldata.insertValues names values.1 ∅) := by
  have ht : cd.toList.length = cd.size := by rw [byteArray_toList_eq, Array.length_toList]; rfl
  cases types with
  | nil => simp only [List.any_nil, Bool.false_eq_true] at hdyn
  | cons ty types =>
    unfold decodeCalldata
    simp only [ht, hdyn, true_and, List.isEmpty_cons, List.length_drop]
    by_cases h4 : cd.size < 4
    · rw [if_pos h4, if_pos (by omega)]
    · rw [if_neg h4]
      by_cases hhuge : 2^255 ≤ cd.size
      · rw [if_pos hhuge, if_pos (Or.inr hhuge)]
      · rw [if_neg hhuge, if_neg (by omega : ¬2^255 ≤ cd.size-4),
          if_neg (by simp only [hhuge, and_false, not_false_eq_true])]
        simp only [decodeCalldata.decodeArgs, hhead, bind, Option.bind]
        by_cases hshort : cd.size < 4+head
        · rw [if_pos (by rw [List.length_drop, ht]; omega), if_pos (Or.inl hshort)]
        · rw [if_neg (by rw [List.length_drop, ht]; omega), if_neg (by omega)]
          cases hv : decodeABIValues? (ty :: types) (cd.toList.drop 4) 0 0 head head with
          | none => rfl
          | some value =>
            rcases value with ⟨values, endOffset⟩
            dsimp only []
            cases decodeCalldata.insertValues names values (∅ : Store) <;> rfl

end Benchmarks.UniswapV4PoolManager
