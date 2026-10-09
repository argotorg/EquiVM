import Benchmarks.CompoundIII.Comet.WithdrawBaseTailModel
import Benchmarks.CompoundIII.Comet.AccountMagnitude

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Benchmarks.CompoundIII.Comet.Immutables

namespace Benchmarks.CompoundIII.Comet

set_option maxRecDepth 2000

theorem withdrawBaseBorrowMin_eval {v frame evm balance}
    (hi : frame.immutables = immStore v)
    (he : evalExpr? config frame evm (.var "srcBalance") = .ok (.int (signedWord balance)))
    (hn : signedWord balance < 0) (hb : -(2^255 : Int) < signedWord balance) :
    evalExpr? config frame evm withdrawBaseBorrowMinExpr =
      .ok (.bool (decide (WithdrawBaseBorrowMin v balance))) := by
  have hsub : evalExpr? config frame evm (.binary .sub (.intLit 0) (.var "srcBalance")) =
      .ok (.int (-signedWord balance)) := by
    simp only [evalExpr?, he, pure, bind, EvalResult.bind, evalBinaryOp?, Int.zero_sub]
  have hr := signedNarrowRangeSourceOk ⟨256, by decide⟩ hsub
    (by change -(2^255 : Int) ≤ _; omega) (by change _ < (2^255 : Int); omega)
  have hm := signedWord_negativeMagnitude (le_of_lt hn)
  rw [← hm] at hr
  have hc := castUintSourceOk ⟨256, by decide⟩ hr (UInt256.sub (UInt256.ofNat 0) balance).val.isLt
  rw [hm] at hc
  simp only [withdrawBaseBorrowMinExpr, evalExpr?, hc, hi, immStore_get_baseBorrowMin,
    bind, EvalResult.bind, EvalResult.ofOption, evalBinaryOp?, WithdrawBaseBorrowMin]
  rfl

end Benchmarks.CompoundIII.Comet
