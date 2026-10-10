import Benchmarks.UniswapV3.Pool.Calldata

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.UniswapV3.Pool

-- GENERALIZES Reasoning.ABI.decodeABIValues_scalarWordsWithMode_eq to a remaining tuple tail.
theorem decodeABIValues_scalarPrefix_eq {mode : DecodeMode} {types tail : List ABIType}
    {bytes : List UInt8} {cursor headSize maxEnd : Nat}
    (hscalar : types.all isABIScalarWordType = true)
    (hbound : cursor + 32 * types.length ≤ maxEnd) :
    decodeABIValues? (types ++ tail) bytes 0 cursor headSize maxEnd mode =
      (do
        let values ← decodeScalarWordsWithMode? mode types bytes cursor
        let (rest, stop) ← decodeABIValues? tail bytes 0
          (cursor + 32 * types.length) headSize maxEnd mode
        some (values ++ rest, stop)) := by
  induction types generalizing cursor with
  | nil => simp [decodeScalarWordsWithMode?]
  | cons ty tys ih =>
      simp only [List.all_cons, Bool.and_eq_true] at hscalar
      rcases hscalar with ⟨hty, htys⟩
      rw [List.cons_append, decodeABIValues?, isABIScalarWordType_dynamic hty]
      simp only [Bool.false_eq_true, if_false]
      rw [isABIScalarWordType_size hty,
        decodeABIValue_scalarWordWithMode_eq (mode := mode) (bytes := bytes)
          (start := 0 + cursor) hty]
      simp only [Nat.zero_add, decodeScalarWordsWithMode?, decodeScalarWordWithMode?]
      cases hr : readWord? bytes cursor with
      | none => simp
      | some word =>
          simp
          cases hw : decodeABIWord? ty word mode with
          | none => simp
          | some value =>
              simp
              have hle : cursor + 32 ≤ maxEnd := by
                simp only [List.length_cons] at hbound; omega
              rw [max_eq_left hle, ih htys (by
                simp only [List.length_cons] at hbound; omega)]
              have heq : cursor + 32 + 32 * tys.length = cursor + 32 * (ty :: tys).length := by
                simp only [List.length_cons]; omega
              rw [heq]
              cases decodeScalarWordsWithMode? mode tys bytes (cursor + 32) <;> simp
              cases decodeABIValues? tail bytes 0 (cursor + 32 * (tys.length + 1))
                headSize maxEnd mode <;> rfl

-- GENERALIZES the scalar tuple head-size rule to a trailing dynamic-bytes value.
theorem abiTupleHeadSize_scalarsBytes {types : List ABIType}
    (hscalar : types.all isABIScalarWordType = true) :
    abiTupleHeadSize? (types ++ [abiBytes]) = some (32 * (types.length + 1)) := by
  induction types with
  | nil => simp [abiTupleHeadSize?, isDynamicABIType, abiBytes]
  | cons ty tys ih =>
      simp only [List.all_cons, Bool.and_eq_true] at hscalar
      rw [List.cons_append, abiTupleHeadSize?, ih hscalar.2]
      simp only [bind, Option.bind, isABIScalarWordType_dynamic hscalar.1,
        Bool.false_eq_true, if_false, isABIScalarWordType_size hscalar.1]
      congr 1
      simp only [List.length_cons]
      omega

end Benchmarks.UniswapV3.Pool
