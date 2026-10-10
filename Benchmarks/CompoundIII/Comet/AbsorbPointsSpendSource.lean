import Benchmarks.CompoundIII.Comet.AbsorbPointsModel
import Benchmarks.CompoundIII.Comet.SafeUintSource
import Benchmarks.CompoundIII.Comet.NarrowArithmetic

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.CompoundIII.Comet

set_option maxRecDepth 2000

def absorbPointsSpendExpr : Expr :=
  .inRange (.uint ⟨256, by decide⟩) (.binary .mul (.var "gasUsed") (.env .basefee))

def absorbPointsSpendBlock : List Stmt :=
  [.internalCall "safe128" [absorbPointsSpendExpr] "__c4",
    .assign .localVar ⟨"points", [.field "approxSpend"]⟩
      (.inRange (.uint ⟨128, by decide⟩)
        (.binary .add (.field (.var "points") "approxSpend") (.var "__c4")))]

def absorbPointsSpendFrame (frame : Frame) (p : LiquidatorPointsData) (gasUsed fee : UInt256) :
    Frame :=
  { frame with
    locals := (frame.locals.insert "__c4" (.int (absorbPointsCost gasUsed fee).toNat)).insert
      "points" (liquidatorPointsValue (absorbPointsSpend p gasUsed fee)) }

theorem absorbPointsSpend_source (frame : Frame) (evm : State) (p : LiquidatorPointsData)
    (gasUsed : UInt256) (hc : frame.contract = contract)
    (hp : frame.locals.get? "points" = some (liquidatorPointsValue p))
    (hg : frame.locals.get? "gasUsed" = some (.int gasUsed.toNat)) :
    ExecBlock config frame evm absorbPointsSpendBlock
      (if AbsorbPointsSpendValid p gasUsed (UInt256.ofNat evm.executionEnv.header.baseFeePerGas) then
        .ok (absorbPointsSpendFrame frame p gasUsed
          (UInt256.ofNat evm.executionEnv.header.baseFeePerGas)) evm else .reverted) := by
  let fee := UInt256.ofNat evm.executionEnv.header.baseFeePerGas
  let cost := absorbPointsCost gasUsed fee
  have hegas : evalExpr? config frame evm (.var "gasUsed") = .ok (.int gasUsed.toNat) := by
    simp only [evalExpr?, hg, EvalResult.ofOption]
  have hefee : evalExpr? config frame evm (.env .basefee) = .ok (.int fee.toNat) := by
    simp only [evalExpr?, envValue, pure]
    rfl
  by_cases hmul : gasUsed.toNat * fee.toNat < UInt256.size
  · have hecost : evalExpr? config frame evm absorbPointsSpendExpr = .ok (.int cost.toNat) :=
      checkedMulSourceOk hegas hefee hmul
    have hcall := safeUint_call ⟨128, by decide⟩ "safe128" safe128Callable_lookup
      frame evm cost absorbPointsSpendExpr "__c4" hc hecost
    by_cases hcost : cost.toNat < 2^128
    · rw [if_pos hcost] at hcall
      let f1 : Frame := { frame with locals := frame.locals.insert "__c4" (.int cost.toNat) }
      have hp1 : f1.locals.get? "points" = some (liquidatorPointsValue p) := by
        simpa only [f1, Std.HashMap.get?_eq_getElem?, Std.HashMap.getElem?_insert] using hp
      have hep : evalExpr? config f1 evm (.var "points") = .ok (liquidatorPointsValue p) := by
        simp only [evalExpr?, hp1, EvalResult.ofOption]
      have hec : evalExpr? config f1 evm (.var "__c4") = .ok (.int cost.toNat) := by
        simp only [evalExpr?, f1, Std.HashMap.get?_eq_getElem?, Std.HashMap.getElem?_insert,
          EvalResult.ofOption]
        rfl
      by_cases hsum : p.spend.toNat + cost.toNat < 2^128
      · rw [if_pos (show AbsorbPointsSpendValid p gasUsed fee from ⟨hmul, hcost, hsum⟩)]
        have hadd := checkedNarrowAddSourceOk ⟨128, by decide⟩ (by decide)
          (evalLiquidatorPointsLocalField 2 hep) hec hsum
        exact ExecBlock.consNormal hcall (ExecBlock.consNormal
          (ExecStmt.assign hadd (assignLiquidatorPointsLocalField 2 (p.spend + cost) hp1))
          ExecBlock.nil)
      · rw [if_neg (show ¬ AbsorbPointsSpendValid p gasUsed fee from fun hv ↦ hsum hv.2.2)]
        exact ExecBlock.consNormal hcall (ExecBlock.consRevert (ExecStmt.assignExprRevert
          (uintRangeSourceOverflow ⟨128, by decide⟩
            (naturalAddSource (evalLiquidatorPointsLocalField 2 hep) hec) (le_of_not_gt hsum))))
    · rw [if_neg hcost] at hcall
      rw [if_neg (show ¬ AbsorbPointsSpendValid p gasUsed fee from fun hv ↦ hcost hv.2.1)]
      exact ExecBlock.consRevert hcall
  · rw [if_neg (show ¬ AbsorbPointsSpendValid p gasUsed fee from fun hv ↦ hmul hv.1)]
    have hm := checkedMulSourceOverflow hegas hefee (le_of_not_gt hmul)
    exact ExecBlock.consRevert (ExecStmt.internalCallArgsRevert (by
      simp only [evalExprs?, absorbPointsSpendExpr, hm, bind, EvalResult.bind]))

end Benchmarks.CompoundIII.Comet
