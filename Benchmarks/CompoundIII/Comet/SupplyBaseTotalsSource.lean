import Benchmarks.CompoundIII.Comet.SupplyBaseTotalsModel
import Benchmarks.CompoundIII.Comet.NarrowArithmetic

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.CompoundIII.Comet

set_option maxRecDepth 2000

theorem supplyBaseTotals_source (frame : Frame) (evm : EVM.State) (supplied repaid : UInt256)
    (hc : frame.contract = contract)
    (hS : frame.locals.get? "supplyAmount" = some (.int supplied.toNat))
    (hB : frame.locals.get? "repayAmount" = some (.int repaid.toNat))
    (hST : frame.locals.get? "totalSupplyBase" = none)
    (hBT : frame.locals.get? "totalBorrowBase" = none) :
    ExecBlock config frame evm supplyBaseTotalsBlock
      (supplyBaseTotalsResult frame evm supplied repaid) := by
  have heS : evalExpr? config frame evm (.var "supplyAmount") =
      .ok (.int supplied.toNat) := by simp only [evalExpr?, hS, EvalResult.ofOption]
  have htS : evalExpr? config frame evm (.storage ⟨"totalSupplyBase", []⟩) =
      .ok (.int (withdrawBaseTotal evm false).toNat) := by
    simpa only [← hc] using evalTotalsPrincipal evm frame.locals frame.immutables false hST
  by_cases hs : (withdrawBaseTotal evm false).toNat + supplied.toNat < 2^104
  · have hadd := checkedNarrowAddSourceOk ⟨104, by decide⟩ (by decide) htS heS hs
    have hwS : assignStorageRef? config frame evm .storage ⟨"totalSupplyBase", []⟩
        (.int (withdrawBaseTotal evm false + supplied).toNat) =
        .ok (frame, supplyBaseSupplyState evm supplied) := by
      simpa only [← hc] using assignTotalsPrincipal evm frame.locals frame.immutables false
        (withdrawBaseTotal evm false + supplied) hST
    cases hp : evm.executionEnv.perm
    · simp only [supplyBaseTotalsResult, supplyBaseTotalsOutcome, if_pos hs, hp,
        Bool.false_eq_true, if_false]
      exact ExecBlock.consStatic (ExecStmt.assignStatic hadd hwS hp)
    · let evm' := supplyBaseSupplyState evm supplied
      have heB : evalExpr? config frame evm' (.var "repayAmount") =
          .ok (.int repaid.toNat) := by simp only [evalExpr?, hB, EvalResult.ofOption]
      have htB : evalExpr? config frame evm' (.storage ⟨"totalBorrowBase", []⟩) =
          .ok (.int (withdrawBaseTotal evm' true).toNat) := by
        simpa only [← hc] using evalTotalsPrincipal evm' frame.locals frame.immutables true hBT
      by_cases hb : repaid.toNat ≤
          (withdrawBaseTotal (supplyBaseSupplyState evm supplied) true).toNat
      · simp only [supplyBaseTotalsResult, supplyBaseTotalsOutcome, if_pos hs, hp,
          if_true, if_pos hb]
        have hsub := checkedNarrowSubSourceOk ⟨104, by decide⟩ htB heB
          (totalsPrincipalWord_lt _ true) hb
        have hwB : assignStorageRef? config frame evm' .storage ⟨"totalBorrowBase", []⟩
            (.int (UInt256.sub (withdrawBaseTotal evm' true) repaid).toNat) =
            .ok (frame, supplyBaseTotalsState evm supplied repaid) := by
          simpa only [← hc] using assignTotalsPrincipal evm' frame.locals frame.immutables true
            (UInt256.sub (withdrawBaseTotal evm' true) repaid) hBT
        exact ExecBlock.consNormal (ExecStmt.assign hadd hwS)
          (ExecBlock.consNormal (ExecStmt.assign hsub hwB) ExecBlock.nil)
      · simp only [supplyBaseTotalsResult, supplyBaseTotalsOutcome, if_pos hs, hp,
          if_true, if_neg hb]
        have hsub := checkedNarrowSubSourceUnderflow ⟨104, by decide⟩ htB heB
          (Nat.lt_of_not_ge hb)
        exact ExecBlock.consNormal (ExecStmt.assign hadd hwS)
          (ExecBlock.consRevert (ExecStmt.assignExprRevert hsub))
  · simp only [supplyBaseTotalsResult, supplyBaseTotalsOutcome, if_neg hs]
    have hadd := uintRangeSourceOverflow ⟨104, by decide⟩ (naturalAddSource htS heS)
      (by change 2^104 ≤ (withdrawBaseTotal evm false).toNat + supplied.toNat; omega)
    exact ExecBlock.consRevert (ExecStmt.assignExprRevert hadd)

end Benchmarks.CompoundIII.Comet
