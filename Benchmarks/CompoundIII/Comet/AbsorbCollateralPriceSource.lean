import Benchmarks.CompoundIII.Comet.AbsorbCollateralPriceModel
import Benchmarks.CompoundIII.Comet.AbsorbCollateralMathSource

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.CompoundIII.Comet

set_option maxRecDepth 2000

theorem absorbCollateralPrice_source {assetOut : ByteArray} {delta seized : UInt256}
    {evm : State} {result : Option (State × UInt256)}
    (ht : AbsorbCollateralPriceTrace assetOut delta seized evm result)
    (frame : Frame) (absorber account asset : AccountAddress) (hc : frame.contract = contract)
    (hi : frame.locals.get? "assetInfo" = some (assetValue assetOut))
    (hd : frame.locals.get? "deltaValue" = some (.int delta.toNat))
    (hn : frame.locals.get? "seizeAmount" = some (.int seized.toNat))
    (ha : frame.locals.get? "absorber" = some (.address absorber))
    (hb : frame.locals.get? "account" = some (.address account))
    (he : frame.locals.get? "asset" = some (.address asset)) :
    ExecBlock config frame evm absorbCollateralPriceBlock
      (absorbCollateralPriceResult frame delta seized assetOut result) := by
  have hfeed : evalExpr? config frame evm (.field (.var "assetInfo") "priceFeed") =
      .ok (.address (AccountAddress.ofNat (calldataWord assetOut 64).toNat)) := by
    simp only [evalExpr?, hi, EvalResult.ofOption, bind, EvalResult.bind]; rfl
  cases ht with
  | @priceFailed evm' z priceOut hcall hh hv =>
      exact ExecBlock.consRevert (price_call_revert frame evm evm' _ _ "__c5"
        priceOut z hc hfeed hcall hh hv)
  | @result evm' priceOut hcall hh hv =>
      have hp := price_call_ok frame evm evm' _ _ "__c5" priceOut hc hfeed hcall hh hv
      let price := calldataWord priceOut 32
      let f1 := absorbCollateralPriceFrame frame price
      have hget1 (key : String) (hk : "__c5" ≠ key) :
          f1.locals.get? key = frame.locals.get? key := by
        simp only [f1, absorbCollateralPriceFrame, Std.HashMap.get?_eq_getElem?,
          Std.HashMap.getElem?_insert, beq_iff_eq, if_neg hk]
      have hm := absorbCollateralMath_source f1 evm' delta seized price assetOut hc
        ((hget1 _ (by decide)).trans hi) ((hget1 _ (by decide)).trans hn)
        (by simp only [f1, absorbCollateralPriceFrame, Std.HashMap.get?_eq_getElem?,
          Std.HashMap.getElem?_insert]; rfl) ((hget1 _ (by decide)).trans hd)
      by_cases hvalid : AbsorbCollateralMathValid delta seized price assetOut
      · rw [if_pos hvalid] at hm ⊢
        let f2 := absorbCollateralMathFrame f1 delta seized price assetOut
        have hget2 (key : String) (hk1 : "__c5" ≠ key) (hk2 : "value" ≠ key)
            (hk3 : "__c7" ≠ key) (hk4 : "deltaValue" ≠ key) :
            f2.locals.get? key = frame.locals.get? key := by
          simp only [f2, f1, absorbCollateralMathFrame, absorbCollateralFactorFrame,
            absorbCollateralValueFrame, absorbCollateralPriceFrame, Std.HashMap.get?_eq_getElem?,
            Std.HashMap.getElem?_insert, beq_iff_eq, if_neg hk1, if_neg hk2, if_neg hk3, if_neg hk4]
        have hev := absorbCollateralEvent_source f2 evm' absorber account asset seized
          (absorbCollateralValue seized price assetOut)
          ((hget2 _ (by decide) (by decide) (by decide) (by decide)).trans ha)
          ((hget2 _ (by decide) (by decide) (by decide) (by decide)).trans hb)
          ((hget2 _ (by decide) (by decide) (by decide) (by decide)).trans he)
          ((hget2 _ (by decide) (by decide) (by decide) (by decide)).trans hn)
          (by simp only [f2, absorbCollateralMathFrame, absorbCollateralFactorFrame,
            absorbCollateralValueFrame, Std.HashMap.get?_eq_getElem?, Std.HashMap.getElem?_insert]; rfl)
        exact ExecBlock.consNormal hp (execBlock_append hm (execBlock_singleton hev))
      · rw [if_neg hvalid] at hm ⊢
        exact ExecBlock.consNormal hp (execBlock_reverted_append hm)

end Benchmarks.CompoundIII.Comet
