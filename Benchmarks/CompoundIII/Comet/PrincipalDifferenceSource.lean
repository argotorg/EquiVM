import Benchmarks.CompoundIII.Comet.WithdrawAmountsModel
import Benchmarks.CompoundIII.Comet.AccountMagnitude

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.CompoundIII.Comet

set_option maxRecDepth 2000
attribute [local irreducible] signed104

-- GENERALIZES withdrawAmountsDiff_source to arbitrary operand expressions.
theorem principalDifference_source {cfg frame evm left right old next}
    (ho : evalExpr? cfg frame evm left = .ok (.int (signed104 old)))
    (hn : evalExpr? cfg frame evm right = .ok (.int (signed104 next)))
    (hle : signed104 next ≤ signed104 old) :
    let expr := Expr.cast (.inRange (.sint ⟨104, by decide⟩) (.binary .sub left right))
      (.elem (.int (.uint ⟨104, by decide⟩)))
    if signed104 old - signed104 next < (2^103 : Int) then
      evalExpr? cfg frame evm expr = .ok (.int (principalDecrease old next).toNat)
    else evalExpr? cfg frame evm expr = .revert := by
  have he : evalExpr? cfg frame evm (.binary .sub left right) =
      .ok (.int (signed104 old - signed104 next)) := by
    simp only [evalExpr?, ho, hn, bind, EvalResult.bind, evalBinaryOp?]
  dsimp only
  by_cases hf : signed104 old - signed104 next < (2^103 : Int)
  · rw [if_pos hf]
    have hr := signedNarrowRangeSourceOk ⟨104, by decide⟩ he
      (by change -(2^103 : Int) ≤ _; omega) hf
    rw [← principalDecrease_int hle] at hr
    exact castUintSourceOk ⟨104, by decide⟩ hr (principalDecrease_lt old next)
  · rw [if_neg hf]
    have hr := signedNarrowRangeSourceOverflow ⟨104, by decide⟩ he
      (by change (2^103 : Int) ≤ _; omega)
    simp only [evalExpr?, hr, bind, EvalResult.bind]

end Benchmarks.CompoundIII.Comet
