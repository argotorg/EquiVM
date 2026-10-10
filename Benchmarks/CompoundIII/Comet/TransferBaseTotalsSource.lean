import Benchmarks.CompoundIII.Comet.TransferBaseTotalsModel
import Benchmarks.CompoundIII.Comet.CheckedAddSubSource

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.CompoundIII.Comet

set_option maxRecDepth 2000

theorem totalsChange_source (frame : Frame) (evm : EVM.State) (borrow : Bool)
    (increase decrease : UInt256) (increaseName decreaseName : Ident)
    (hc : frame.contract = contract)
    (hi : frame.locals.get? increaseName = some (.int increase.toNat))
    (hd : frame.locals.get? decreaseName = some (.int decrease.toNat))
    (ht : frame.locals.get? (totalsPrincipalName borrow) = none) :
    ExecStmt config frame evm (totalsChangeStmt borrow increaseName decreaseName)
      (totalsChangeResult frame evm borrow increase decrease) := by
  have hei : evalExpr? config frame evm (.var increaseName) = .ok (.int increase.toNat) := by
    simp only [evalExpr?, hi, EvalResult.ofOption]
  have hed : evalExpr? config frame evm (.var decreaseName) = .ok (.int decrease.toNat) := by
    simp only [evalExpr?, hd, EvalResult.ofOption]
  have het : evalExpr? config frame evm (.storage ⟨totalsPrincipalName borrow, []⟩) =
      .ok (.int (withdrawBaseTotal evm borrow).toNat) := by
    simpa only [← hc] using evalTotalsPrincipal evm frame.locals frame.immutables borrow ht
  have he := checkedNarrowAddSubSource ⟨104, by decide⟩ (by decide) het hei hed
  change evalExpr? _ _ _ _ = if TotalsChangeFits evm borrow increase decrease then _ else _ at he
  by_cases hf : TotalsChangeFits evm borrow increase decrease
  · rw [if_pos hf] at he
    have hw : assignStorageRef? config frame evm .storage ⟨totalsPrincipalName borrow, []⟩
        (.int (UInt256.sub (withdrawBaseTotal evm borrow + increase) decrease).toNat) =
        .ok (frame, totalsChangeState evm borrow increase decrease) := by
      simpa only [← hc] using assignTotalsPrincipal evm frame.locals frame.immutables borrow
        (UInt256.sub (withdrawBaseTotal evm borrow + increase) decrease) ht
    cases hp : evm.executionEnv.perm
    · simp only [totalsChangeResult, totalsChangeOutcome, if_pos hf, hp, Bool.false_eq_true, if_false]
      exact ExecStmt.assignStatic he hw hp
    · simp only [totalsChangeResult, totalsChangeOutcome, if_pos hf, hp, if_true]
      exact ExecStmt.assign he hw
  · rw [if_neg hf] at he
    simp only [totalsChangeResult, totalsChangeOutcome, if_neg hf]
    exact ExecStmt.assignExprRevert he

theorem transferBaseTotals_source (frame : Frame) (evm : EVM.State)
    (supplied withdrawn borrowed repaid : UInt256) (hc : frame.contract = contract)
    (hS : frame.locals.get? "supplyAmount" = some (.int supplied.toNat))
    (hW : frame.locals.get? "withdrawAmount" = some (.int withdrawn.toNat))
    (hB : frame.locals.get? "borrowAmount" = some (.int borrowed.toNat))
    (hR : frame.locals.get? "repayAmount" = some (.int repaid.toNat))
    (hST : frame.locals.get? "totalSupplyBase" = none)
    (hBT : frame.locals.get? "totalBorrowBase" = none) :
    ExecBlock config frame evm transferBaseTotalsBlock
      (transferBaseTotalsResult frame evm supplied withdrawn borrowed repaid) := by
  have hsrc := totalsChange_source frame evm false supplied withdrawn
    "supplyAmount" "withdrawAmount" hc hS hW hST
  cases hs : totalsChangeOutcome evm false supplied withdrawn with
  | reverted =>
      simp only [totalsChangeResult, hs] at hsrc
      simp only [transferBaseTotalsResult, transferBaseTotalsOutcome, hs]
      exact ExecBlock.consRevert hsrc
  | staticViolation =>
      simp only [totalsChangeResult, hs] at hsrc
      simp only [transferBaseTotalsResult, transferBaseTotalsOutcome, hs]
      exact ExecBlock.consStatic hsrc
  | ok evm' =>
      simp only [totalsChangeResult, hs] at hsrc
      have hdst := totalsChange_source frame evm' true borrowed repaid
        "borrowAmount" "repayAmount" hc hB hR hBT
      cases hd : totalsChangeOutcome evm' true borrowed repaid with
      | reverted =>
          simp only [totalsChangeResult, hd] at hdst
          simp only [transferBaseTotalsResult, transferBaseTotalsOutcome, hs, hd]
          exact ExecBlock.consNormal hsrc (ExecBlock.consRevert hdst)
      | staticViolation =>
          simp only [totalsChangeResult, hd] at hdst
          simp only [transferBaseTotalsResult, transferBaseTotalsOutcome, hs, hd]
          exact ExecBlock.consNormal hsrc (ExecBlock.consStatic hdst)
      | ok evm'' =>
          simp only [totalsChangeResult, hd] at hdst
          simp only [transferBaseTotalsResult, transferBaseTotalsOutcome, hs, hd]
          exact ExecBlock.consNormal hsrc (ExecBlock.consNormal hdst ExecBlock.nil)

end Benchmarks.CompoundIII.Comet
