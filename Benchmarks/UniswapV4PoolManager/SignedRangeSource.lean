import Benchmarks.UniswapV4PoolManager.Values

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.UniswapV4PoolManager

-- GENERALIZES the checked signed-addition rule to every width and expression.
def signedFits (bits : BitWidth) (n : Int) : Prop :=
  -(2 : Int)^(bits.val-1) ≤ n ∧ n < (2 : Int)^(bits.val-1)
instance (bits : BitWidth) (n : Int) : Decidable (signedFits bits n) :=
  inferInstanceAs (Decidable (_ ∧ _))

-- LIBRARY CANDIDATE: a signed cast preserves an integer already within its target range.
theorem normalizeSigned_of_fits {bits : BitWidth} {n : Int} (hn : signedFits bits n) :
    normalizeInt (.sint bits) n = n := by
  have hbits : bits.val = bits.val-1+1 := by have := bits.property.1; omega
  have hp : (2 : Int)^bits.val = (2 : Int)^(bits.val-1) + (2 : Int)^(bits.val-1) := by
    conv_lhs => rw [hbits, pow_succ]
    ring
  have hpos : (0 : Int) < 2^(bits.val-1) := pow_pos (by decide) _
  rcases hn with ⟨hlo, hhi⟩
  simp only [normalizeInt, EVM.twoPow, Int.ofNat_eq_natCast, Int.natCast_pow, Int.cast_ofNat_Int]
  by_cases hz : 0 ≤ n
  · rw [Int.emod_eq_of_lt hz (by omega), if_pos hhi]
  · have hr : n % (2 : Int)^bits.val = n+(2 : Int)^bits.val := by
      have he := Int.emod_eq_of_lt (a := n+(2 : Int)^bits.val) (b := (2 : Int)^bits.val)
        (by omega) (by omega)
      simpa only [Int.add_emod, Int.emod_self, add_zero, Int.emod_emod] using he
    rw [hr, if_neg (by omega)]
    omega

theorem evalSignedRange {cfg : Config} {f : Frame} {evm : EVM.State} {e : Expr} {n : Int}
    (bits : BitWidth) (he : evalExpr? cfg f evm e = .ok (.int n)) :
    evalExpr? cfg f evm (.inRange (.sint bits) e) =
      if signedFits bits n then .ok (.int n) else .revert := by
  simp only [evalExpr?, he, bind, EvalResult.bind]
  by_cases h : signedFits bits n
  · rw [if_pos h]
    have hl : ¬n < -(2 : Int)^(bits.val-1) := by have := h.1; omega
    have hh : ¬n ≥ (2 : Int)^(bits.val-1) := by have := h.2; omega
    simp only [hl, hh, decide_false, Bool.false_or, Bool.false_eq_true, if_false, pure]
  · rw [if_neg h, if_pos]
    simp only [Bool.or_eq_true, decide_eq_true_eq]
    unfold signedFits at h
    omega

end Benchmarks.UniswapV4PoolManager
