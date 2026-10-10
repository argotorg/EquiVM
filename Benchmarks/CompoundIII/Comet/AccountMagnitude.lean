import Benchmarks.CompoundIII.Comet.AccountRewardModel

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.CompoundIII.Comet

set_option maxRecDepth 10000

-- LIBRARY CANDIDATE: a cast preserves a natural number already within its target width.
theorem castUintSourceOk {cfg frame evm expr} {n : Nat} (width : BitWidth)
    (he : evalExpr? cfg frame evm expr = .ok (.int (Int.ofNat n))) (hn : n < 2^width.val) :
    evalExpr? cfg frame evm (.cast expr (.elem (.int (.uint width)))) =
      .ok (.int (Int.ofNat n)) := by
  have he' := evalExpr_cast_int (intType := .uint width) he
  have hnorm : normalizeInt (.uint width) (Int.ofNat n) = Int.ofNat n :=
    normalizeInt_uint_eq_self _ _ (Int.natCast_nonneg _) (by
      change (n : Int) < (2^width.val : Nat)
      exact_mod_cast hn)
  rw [hnorm] at he'
  exact he'

theorem accountMagnitude_lt {principal : UInt256} (borrow : Bool)
    (hmin : -(2^103 : Int) < signed104 principal) :
    (accountMagnitude principal borrow).toNat < 2^104 := by
  cases borrow
  · exact lt_trans (positivePrincipal_lt principal) (by decide)
  · exact lt_trans (negativePrincipal_lt hmin) (by decide)

theorem accountMagnitude_source {cfg frame evm principal} (borrow : Bool)
    (he : evalExpr? cfg frame evm (.var "principal") = .ok (.int (signed104 principal)))
    (hsign : if borrow then signed104 principal < 0 else 0 ≤ signed104 principal) :
    evalExpr? cfg frame evm (accountMagnitudeExpr borrow) =
      if -(2^103 : Int) < signed104 principal then
        .ok (.int (accountMagnitude principal borrow).toNat) else .revert := by
  by_cases hmin : -(2^103 : Int) < signed104 principal
  · rw [if_pos hmin]
    cases borrow
    · have hpos := positivePrincipal_int hsign
      rw [← hpos] at he
      exact castUintSourceOk ⟨104, by decide⟩ he (accountMagnitude_lt false hmin)
    · exact castUintSourceOk ⟨104, by decide⟩ (checkedPrincipalNegSource he hsign hmin)
        (accountMagnitude_lt true hmin)
  · rw [if_neg hmin]
    cases borrow
    · simp only [Bool.false_eq_true, if_false] at hsign
      omega
    · have hb := signed104_bounds principal
      have hn := checkedPrincipalNegSource_revert he (by omega)
      simp only [accountMagnitudeExpr, if_true, evalExpr?, hn, bind, EvalResult.bind]

end Benchmarks.CompoundIII.Comet
