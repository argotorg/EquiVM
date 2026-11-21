import Benchmarks.Midnight.Common

/-! Bounds for ABI tuple heads made of scalar words and dynamic offsets. -/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Midnight

-- LIBRARY CANDIDATE: every nonempty tuple of word-sized heads fits in its input buffer.
theorem decodeABIWordHeads_bound {types : List ABIType} {bytes : List UInt8}
    {base cursor headSize maxEnd stop : Nat} {values : List Value}
    (hheads : ∀ ty ∈ types, isDynamicABIType ty = true ∨ isABIScalarWordType ty = true)
    (h : decodeABIValues? types bytes base cursor headSize maxEnd = some (values, stop)) :
    types = [] ∨ base + cursor + 32 * types.length ≤ bytes.length := by
  induction types generalizing cursor maxEnd values stop with
  | nil => exact Or.inl rfl
  | cons ty rest ih =>
    right
    have finish {values' : List Value} {end' max' : Nat}
        (hhead : base + cursor + 32 ≤ bytes.length)
        (hrest : decodeABIValues? rest bytes base (cursor + 32) headSize max' =
          some (values', end')) : base + cursor + 32 * (ty :: rest).length ≤ bytes.length := by
      rcases ih (fun t ht ↦ hheads t (List.mem_cons_of_mem _ ht)) hrest with hn | hb
      · subst rest; simpa using hhead
      · simp only [List.length_cons]; omega
    rw [decodeABIValues?] at h
    rcases hheads ty List.mem_cons_self with hdyn | hscalar
    · rw [hdyn] at h
      simp only [if_true] at h
      rcases Option.bind_eq_some_iff.mp h with ⟨off, hoff, h⟩
      split at h
      · cases h
      · rcases Option.bind_eq_some_iff.mp h with ⟨⟨value, valueEnd⟩, _, h⟩
        rcases Option.bind_eq_some_iff.mp h with ⟨⟨tail, tailEnd⟩, htail, _⟩
        exact finish (readNat?_some_length hoff) htail
    · rw [isABIScalarWordType_dynamic hscalar] at h
      simp only [Bool.false_eq_true, if_false, isABIScalarWordType_size hscalar,
        bind, Option.bind] at h
      rw [decodeABIValue_scalarWord_eq hscalar] at h
      cases hv : decodeScalarWord? ty bytes (base + cursor) with
      | none => simp only [hv] at h; cases h
      | some pair =>
        rcases pair with ⟨value, valueEnd⟩
        simp only [hv] at h
        split at h
        · rcases Option.bind_eq_some_iff.mp h with ⟨⟨tail, tailEnd⟩, htail, _⟩
          exact finish (decodeScalarWord?_some_length hv) htail
        · cases h

end Benchmarks.Midnight
