import Reasoning.ABI

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory
namespace Benchmarks.UniswapV4PoolManager

-- LIBRARY CANDIDATE: decode a static scalar tuple at any enclosing ABI base offset.
theorem decodeScalarTupleAt {types : List ABIType} {bytes : List UInt8}
    {base cursor headSize finish : Nat}
    (hs : types.all isABIScalarWordType = true)
    (he : base+cursor+32*types.length = finish) :
    decodeABIValues? types bytes base cursor headSize finish =
      match decodeScalarWords? types bytes (base+cursor) with
      | some values => some (values, finish)
      | none => none := by
  induction types generalizing cursor with
  | nil => simp only [decodeABIValues?, decodeScalarWords?]
  | cons ty tys ih =>
    simp only [List.all_cons, Bool.and_eq_true] at hs
    obtain ⟨ht, hts⟩ := hs
    rw [decodeABIValues?, isABIScalarWordType_dynamic ht]
    simp only [Bool.false_eq_true, if_false]
    rw [isABIScalarWordType_size ht, decodeABIValue_scalarWord_eq ht]
    simp only [decodeScalarWords?, decodeScalarWord?]
    cases readWord? bytes (base+cursor) with
    | none => simp only [bind, Option.bind]
    | some word =>
      simp only [bind, Option.bind]
      cases decodeABIWord? ty word with
      | none => simp only [bind, Option.bind]
      | some value =>
        simp only [bind, Option.bind]
        have hb : base+cursor+32 ≤ finish := by simp only [List.length_cons] at he; omega
        rw [max_eq_left hb, ih hts (by simp only [List.length_cons] at he; omega)]
        simp only [Nat.add_assoc]
        cases decodeScalarWords? tys bytes (base+(cursor+32)) <;> rfl

end Benchmarks.UniswapV4PoolManager
