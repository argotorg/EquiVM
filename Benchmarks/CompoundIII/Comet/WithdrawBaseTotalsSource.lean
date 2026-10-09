import Benchmarks.CompoundIII.Comet.WithdrawBaseTotalsModel
import Benchmarks.CompoundIII.Comet.NarrowArithmetic

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.CompoundIII.Comet

set_option maxRecDepth 2000

theorem withdrawBaseTotals_source (frame : Frame) (evm : EVM.State) (supplied borrowed : UInt256)
    (hc : frame.contract = contract)
    (hS : frame.locals.get? "withdrawAmount" = some (.int supplied.toNat))
    (hB : frame.locals.get? "borrowAmount" = some (.int borrowed.toNat))
    (hST : frame.locals.get? "totalSupplyBase" = none)
    (hBT : frame.locals.get? "totalBorrowBase" = none) :
    ExecBlock config frame evm withdrawBaseTotalsBlock
      (withdrawBaseTotalsResult frame evm supplied borrowed) := by
  have heS : evalExpr? config frame evm (.var "withdrawAmount") =
      .ok (.int supplied.toNat) := by simp only [evalExpr?, hS, EvalResult.ofOption]
  have htS : evalExpr? config frame evm (.storage ⟨"totalSupplyBase", []⟩) =
      .ok (.int (withdrawBaseTotal evm false).toNat) := by
    simpa only [← hc] using evalTotalsPrincipal evm frame.locals frame.immutables false hST
  by_cases hs : supplied.toNat ≤ (withdrawBaseTotal evm false).toNat
  · have hsub := checkedNarrowSubSourceOk ⟨104, by decide⟩ htS heS
      (totalsPrincipalWord_lt _ false) hs
    have hwS : assignStorageRef? config frame evm .storage ⟨"totalSupplyBase", []⟩
        (.int (UInt256.sub (withdrawBaseTotal evm false) supplied).toNat) =
        .ok (frame, withdrawBaseSupplyState evm supplied) := by
      simpa only [← hc] using assignTotalsPrincipal evm frame.locals frame.immutables false
        (UInt256.sub (withdrawBaseTotal evm false) supplied) hST
    cases hp : evm.executionEnv.perm
    · simp only [withdrawBaseTotalsResult, withdrawBaseTotalsOutcome, if_pos hs, hp,
        Bool.false_eq_true, if_false]
      exact ExecBlock.consStatic (ExecStmt.assignStatic hsub hwS hp)
    · let evm' := withdrawBaseSupplyState evm supplied
      have heB : evalExpr? config frame evm' (.var "borrowAmount") =
          .ok (.int borrowed.toNat) := by simp only [evalExpr?, hB, EvalResult.ofOption]
      have htB : evalExpr? config frame evm' (.storage ⟨"totalBorrowBase", []⟩) =
          .ok (.int (withdrawBaseTotal evm' true).toNat) := by
        simpa only [← hc] using evalTotalsPrincipal evm' frame.locals frame.immutables true hBT
      by_cases hb : (withdrawBaseTotal (withdrawBaseSupplyState evm supplied) true).toNat +
          borrowed.toNat < 2^104
      · simp only [withdrawBaseTotalsResult, withdrawBaseTotalsOutcome, if_pos hs, hp,
          if_true, if_pos hb]
        have hadd := checkedNarrowAddSourceOk ⟨104, by decide⟩ (by decide) htB heB hb
        have hwB : assignStorageRef? config frame evm' .storage ⟨"totalBorrowBase", []⟩
            (.int (withdrawBaseTotal evm' true + borrowed).toNat) =
            .ok (frame, withdrawBaseTotalsState evm supplied borrowed) := by
          simpa only [← hc] using assignTotalsPrincipal evm' frame.locals frame.immutables true
            (withdrawBaseTotal evm' true + borrowed) hBT
        exact ExecBlock.consNormal (ExecStmt.assign hsub hwS)
          (ExecBlock.consNormal (ExecStmt.assign hadd hwB) ExecBlock.nil)
      · simp only [withdrawBaseTotalsResult, withdrawBaseTotalsOutcome, if_pos hs, hp,
          if_true, if_neg hb]
        have hadd := uintRangeSourceOverflow ⟨104, by decide⟩
          (naturalAddSource htB heB) (by
            change 2^104 ≤ (withdrawBaseTotal (withdrawBaseSupplyState evm supplied) true).toNat +
              borrowed.toNat
            omega)
        exact ExecBlock.consNormal (ExecStmt.assign hsub hwS)
          (ExecBlock.consRevert (ExecStmt.assignExprRevert hadd))
  · simp only [withdrawBaseTotalsResult, withdrawBaseTotalsOutcome, if_neg hs]
    have hsub := checkedNarrowSubSourceUnderflow ⟨104, by decide⟩ htS heS (by omega)
    exact ExecBlock.consRevert (ExecStmt.assignExprRevert hsub)

end Benchmarks.CompoundIII.Comet
