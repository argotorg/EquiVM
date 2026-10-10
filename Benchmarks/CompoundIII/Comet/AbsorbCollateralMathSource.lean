import Benchmarks.CompoundIII.Comet.AbsorbCollateralMathModel
import Benchmarks.CompoundIII.Comet.IndexAccrual

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.CompoundIII.Comet

theorem absorbCollateralMath_source (frame : Frame) (evm : State)
    (delta seized price : UInt256) (out : ByteArray) (hc : frame.contract = contract)
    (ha : frame.locals.get? "assetInfo" = some (assetValue out))
    (hn : frame.locals.get? "seizeAmount" = some (.int seized.toNat))
    (hp : frame.locals.get? "__c5" = some (.int price.toNat))
    (hd : frame.locals.get? "deltaValue" = some (.int delta.toNat)) :
    ExecBlock config frame evm absorbCollateralMathBlock
      (if AbsorbCollateralMathValid delta seized price out then
        .ok (absorbCollateralMathFrame frame delta seized price out) evm else .reverted) := by
  have hs : evalExpr? config frame evm (.field (.var "assetInfo") "scale") =
      .ok (.int (calldataWord out 96).toNat) := by
    simp only [evalExpr?, ha, EvalResult.ofOption, bind, EvalResult.bind]; rfl
  have hprice := mulPrice_call frame evm seized price (calldataWord out 96)
    (.var "seizeAmount") (.var "__c5") (.field (.var "assetInfo") "scale") "value" hc
    (by simp only [evalExpr?, hn, EvalResult.ofOption])
    (by simp only [evalExpr?, hp, EvalResult.ofOption]) hs
  by_cases hv1 : MulPriceValid seized price (calldataWord out 96)
  · rw [if_pos hv1] at hprice
    let f1 := absorbCollateralValueFrame frame seized price out
    have hv : evalExpr? config f1 evm (.var "value") =
        .ok (.int (absorbCollateralValue seized price out).toNat) := by
      simp only [evalExpr?, f1, absorbCollateralValueFrame, Std.HashMap.get?_eq_getElem?,
        Std.HashMap.getElem?_insert, EvalResult.ofOption]; rfl
    have ha1 : f1.locals.get? "assetInfo" = some (assetValue out) := by
      simpa only [f1, absorbCollateralValueFrame, Std.HashMap.get?_eq_getElem?,
        Std.HashMap.getElem?_insert] using ha
    have hf : evalExpr? config f1 evm (.field (.var "assetInfo") "liquidationFactor") =
        .ok (.int (calldataWord out 192).toNat) := by
      simp only [evalExpr?, ha1, EvalResult.ofOption, bind, EvalResult.bind]; rfl
    by_cases hv2 : (absorbCollateralValue seized price out).toNat *
        (calldataWord out 192).toNat < UInt256.size
    · have hfactor := mulFactor_call_ok f1 evm (absorbCollateralValue seized price out)
        (calldataWord out 192) (.var "value")
        (.field (.var "assetInfo") "liquidationFactor") "__c7" hc hv hf hv2
      let f2 := absorbCollateralFactorFrame frame seized price out
      have hc7 : evalExpr? config f2 evm (.var "__c7") =
          .ok (.int (absorbCollateralContribution seized price out).toNat) := by
        simp only [evalExpr?, f2, absorbCollateralFactorFrame, Std.HashMap.get?_eq_getElem?,
          Std.HashMap.getElem?_insert, EvalResult.ofOption]; rfl
      have hd2 : f2.locals.get? "deltaValue" = some (.int delta.toNat) := by
        simpa only [f2, absorbCollateralFactorFrame, absorbCollateralValueFrame,
          Std.HashMap.get?_eq_getElem?, Std.HashMap.getElem?_insert] using hd
      have hed : evalExpr? config f2 evm (.var "deltaValue") = .ok (.int delta.toNat) := by
        simp only [evalExpr?, hd2, EvalResult.ofOption]
      by_cases hv3 : delta.toNat + (absorbCollateralContribution seized price out).toNat < UInt256.size
      · rw [if_pos (show AbsorbCollateralMathValid delta seized price out from ⟨hv1, hv2, hv3⟩)]
        exact ExecBlock.consNormal hprice (ExecBlock.consNormal hfactor
          (ExecBlock.consNormal (ExecStmt.assign (checkedAddSourceOk hed hc7 hv3)
            (assignLocalFrame hd2)) .nil))
      · rw [if_neg (fun h : AbsorbCollateralMathValid delta seized price out ↦ hv3 h.2.2)]
        exact ExecBlock.consNormal hprice (ExecBlock.consNormal hfactor
          (ExecBlock.consRevert (ExecStmt.assignExprRevert
            (checkedAddSourceOverflow hed hc7 (Nat.le_of_not_lt hv3)))))
    · rw [if_neg (fun h : AbsorbCollateralMathValid delta seized price out ↦ hv2 h.2.1)]
      exact ExecBlock.consNormal hprice (ExecBlock.consRevert
        (mulFactor_call_revert f1 evm (absorbCollateralValue seized price out)
          (calldataWord out 192) (.var "value")
          (.field (.var "assetInfo") "liquidationFactor") "__c7" hc hv hf hv2))
  · rw [if_neg hv1] at hprice
    rw [if_neg (fun h : AbsorbCollateralMathValid delta seized price out ↦ hv1 h.1)]
    exact ExecBlock.consRevert hprice

end Benchmarks.CompoundIII.Comet
