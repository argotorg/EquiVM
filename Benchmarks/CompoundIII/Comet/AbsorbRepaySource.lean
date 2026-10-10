import Benchmarks.CompoundIII.Comet.AbsorbRepayModel
import Benchmarks.CompoundIII.Comet.RepayAmountsSource
import Benchmarks.CompoundIII.Comet.SupplyBaseTotalsSource
import Benchmarks.CompoundIII.Comet.TupleLocalSource

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.CompoundIII.Comet

set_option maxRecDepth 10000
attribute [local irreducible] signed104 supplyBaseTotalsOutcome absorbRepayOutcome

theorem absorbRepay_source (frame : Frame) (evm : State) (old next : UInt256)
    (hc : frame.contract = contract)
    (ho : frame.locals.get? "oldPrincipal" = some (.int (signed104 old)))
    (hn : frame.locals.get? "newPrincipal" = some (.int (signed104 next)))
    (hST : frame.locals.get? "totalSupplyBase" = none)
    (hBT : frame.locals.get? "totalBorrowBase" = none) :
    ExecBlock config frame evm absorbRepayBlock (absorbRepayResult frame evm old next) := by
  have heo : evalExpr? config frame evm (.var "oldPrincipal") = .ok (.int (signed104 old)) := by
    simp only [evalExpr?, ho, EvalResult.ofOption]
  have hen : evalExpr? config frame evm (.var "newPrincipal") = .ok (.int (signed104 next)) := by
    simp only [evalExpr?, hn, EvalResult.ofOption]
  have hr := repayAmounts_call frame evm old next _ _ "__c12" hc heo hen
  by_cases hf : RepayAmountsFits old next
  · rw [if_pos hf] at hr
    let f : Frame := { frame with
      locals := frame.locals.insert "__c12"
        (.tuple [.int (repayAmount old next).toNat, .int (supplyAmount old next).toNat]) }
    have ht : f.locals.get? "__c12" = some
        (.tuple [.int (repayAmount old next).toNat, .int (supplyAmount old next).toNat]) := by
      simp only [f, Std.HashMap.get?_eq_getElem?, Std.HashMap.getElem?_insert]; rfl
    have hl := tuplePairLets_source config f evm "__c12" "repayAmount" "supplyAmount"
      (some (.elem (.int (.uint ⟨104, by decide⟩))))
      (some (.elem (.int (.uint ⟨104, by decide⟩)))) _ _ (by decide) ht
    have hS : (absorbRepayFrame frame old next).locals.get? "supplyAmount" =
        some (.int (supplyAmount old next).toNat) := by
      simp only [absorbRepayFrame, Std.HashMap.get?_eq_getElem?, Std.HashMap.getElem?_insert]; rfl
    have hB : (absorbRepayFrame frame old next).locals.get? "repayAmount" =
        some (.int (repayAmount old next).toNat) := by
      simp only [absorbRepayFrame, Std.HashMap.get?_eq_getElem?, Std.HashMap.getElem?_insert]; rfl
    have hST' : (absorbRepayFrame frame old next).locals.get? "totalSupplyBase" = none := by
      simpa only [absorbRepayFrame, Std.HashMap.get?_eq_getElem?,
        Std.HashMap.getElem?_insert] using hST
    have hBT' : (absorbRepayFrame frame old next).locals.get? "totalBorrowBase" = none := by
      simpa only [absorbRepayFrame, Std.HashMap.get?_eq_getElem?,
        Std.HashMap.getElem?_insert] using hBT
    have hb := supplyBaseTotals_source (absorbRepayFrame frame old next) evm
      (supplyAmount old next) (repayAmount old next) hc hS hB hST' hBT'
    rw [absorbRepayResult, if_pos hf]
    exact ExecBlock.consNormal hr (execBlock_append hl hb)
  · rw [if_neg hf] at hr
    rw [absorbRepayResult, if_neg hf]
    exact ExecBlock.consRevert hr

end Benchmarks.CompoundIII.Comet
