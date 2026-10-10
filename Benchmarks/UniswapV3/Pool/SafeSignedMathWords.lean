import Benchmarks.UniswapV3.Pool.SafeSignedMathSource
import Benchmarks.UniswapV3.Pool.SignedComparison

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.UniswapV3.Pool
set_option maxRecDepth 1000
attribute [local instance] Classical.propDecidable

-- LIBRARY CANDIDATE: a negated signed comparison is an integer non-strict comparison.
theorem isZero_slt_wordOfInt (i j : Int)
    (hilo : -(2 ^ 255 : Int) ≤ i) (hihi : i < 2 ^ 255)
    (hjlo : -(2 ^ 255 : Int) ≤ j) (hjhi : j < 2 ^ 255) :
    UInt256.isZero (UInt256.slt (EVM.wordOfInt i) (EVM.wordOfInt j)) =
      if j ≤ i then ⟨1⟩ else ⟨0⟩ := by
  rw [slt_wordOfInt i j hilo hihi hjlo hjhi]
  by_cases h : i < j
  · rw [if_pos h, if_neg (by omega)]
    rfl
  · rw [if_neg h, if_pos (by omega)]
    rfl

-- LIBRARY CANDIDATE: equality of Boolean EVM words represents logical equivalence.
theorem eq_prop_words (p q : Prop) [Decidable p] [Decidable q] :
    UInt256.eq (if q then ⟨1⟩ else ⟨0⟩) (if p then ⟨1⟩ else ⟨0⟩) =
      if p ↔ q then ⟨1⟩ else ⟨0⟩ := by
  by_cases hp : p <;> by_cases hq : q
  all_goals simp only [hp, hq, ↓reduceIte, iff_self, true_iff, false_iff,
    not_true_eq_false, not_false_eq_true]
  all_goals rfl

theorem safeSignedMathWordGuard (subtract : Bool) (x y : Int)
    (hxlo : -(2 ^ 255 : Int) ≤ x) (hxhi : x < 2 ^ 255)
    (hylo : -(2 ^ 255 : Int) ≤ y) (hyhi : y < 2 ^ 255) :
    UInt256.eq (UInt256.isZero (UInt256.slt (EVM.wordOfInt y) (UInt256.ofNat 0)))
      (if subtract then UInt256.isZero
        (UInt256.sgt (EVM.wordOfInt (safeSignedMathResult subtract x y)) (EVM.wordOfInt x))
       else UInt256.isZero
        (UInt256.slt (EVM.wordOfInt (safeSignedMathResult subtract x y)) (EVM.wordOfInt x))) =
      if safeSignedMathValid subtract x y then ⟨1⟩ else ⟨0⟩ := by
  classical
  have hz : -(2 ^ 255 : Int) ≤ safeSignedMathResult subtract x y ∧
      safeSignedMathResult subtract x y < 2 ^ 255 :=
    normalizeSint_bounds ⟨256, by decide⟩ _
  have hy0 : UInt256.isZero (UInt256.slt (EVM.wordOfInt y) (UInt256.ofNat 0)) =
      if 0 ≤ y then ⟨1⟩ else ⟨0⟩ :=
    isZero_slt_wordOfInt y 0 hylo hyhi (by decide) (by decide)
  rw [hy0]
  cases subtract
  · simp only [Bool.false_eq_true, ↓reduceIte, safeSignedMathValid]
    rw [isZero_slt_wordOfInt _ _ hz.1 hz.2 hxlo hxhi, eq_prop_words]
  · simp only [↓reduceIte, safeSignedMathValid]
    rw [sgt_eq_slt_swap, isZero_slt_wordOfInt _ _ hxlo hxhi hz.1 hz.2, eq_prop_words]

theorem safeSignedMathResult_word (subtract : Bool) (x y : Int) :
    EVM.wordOfInt (safeSignedMathResult subtract x y) =
      if subtract then UInt256.sub (EVM.wordOfInt x) (EVM.wordOfInt y)
      else EVM.wordOfInt y + EVM.wordOfInt x := by
  cases subtract <;> simp only [safeSignedMathResult, Bool.false_eq_true, ↓reduceIte,
    wordOfInt_normalize256, wordOfInt_sub, wordOfInt_add]
  exact u256_add_comm _ _

end Benchmarks.UniswapV3.Pool
