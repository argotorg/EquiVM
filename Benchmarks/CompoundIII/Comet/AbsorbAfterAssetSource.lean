import Benchmarks.CompoundIII.Comet.AbsorbAfterAssetModel
import Benchmarks.CompoundIII.Comet.AbsorbSeizeSource
import Benchmarks.CompoundIII.Comet.AbsorbCollateralPriceSource

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.CompoundIII.Comet

set_option maxRecDepth 2000

theorem absorbAfterAsset_source {account : AccountAddress} {out : ByteArray} {delta : UInt256}
    {evm : State} {result : InternalValueOutcome UInt256}
    (ht : AbsorbAfterAssetTrace account out delta evm result)
    (frame : Frame) (absorber : AccountAddress) (hc : frame.contract = contract)
    (hi : frame.locals.get? "assetInfo" = some (assetValue out))
    (hd : frame.locals.get? "deltaValue" = some (.int delta.toNat))
    (ha : frame.locals.get? "absorber" = some (.address absorber))
    (hb : frame.locals.get? "account" = some (.address account))
    (hU : frame.locals.get? "userCollateral" = none)
    (hT : frame.locals.get? "totalsCollateral" = none) :
    ExecBlock config frame evm absorbAfterAssetBlock
      (internalValueFrameResult (absorbAfterAssetFrame frame out delta
        (withdrawCollateralBalance evm account (absorbAssetAddress out))) result) := by
  let asset := absorbAssetAddress out
  let named := absorbAssetNameFrame frame out
  let ready := absorbAssetSeizedFrame frame out (withdrawCollateralBalance evm account asset)
  have he : evalExpr? config frame evm (.field (.var "assetInfo") "asset") =
      .ok (.address asset) := by
    simp only [evalExpr?, hi, EvalResult.ofOption, bind, EvalResult.bind]; rfl
  have hname (key : String) (hk : "asset" ≠ key) :
      named.locals.get? key = frame.locals.get? key := by
    simp only [named, absorbAssetNameFrame, Std.HashMap.get?_eq_getElem?,
      Std.HashMap.getElem?_insert, beq_iff_eq, if_neg hk]
  have hasset : named.locals.get? "asset" = some (.address asset) := by
    simp only [named, absorbAssetNameFrame, Std.HashMap.get?_eq_getElem?,
      Std.HashMap.getElem?_insert]; rfl
  have hseize := absorbSeize_source named evm account asset hc
    ((hname _ (by decide)).trans hb) hasset ((hname _ (by decide)).trans hU)
    ((hname _ (by decide)).trans hT)
  apply ExecBlock.consNormal (ExecStmt.letDecl he)
  cases ht with
  | seizeReverted hs =>
      rw [hs] at hseize
      exact execBlock_reverted_append hseize
  | seizeStatic hs =>
      rw [hs] at hseize
      exact execBlock_append_term hseize (by intro _ _ hh; cases hh)
  | @priced seizedState result hs hprice =>
      rw [hs] at hseize
      have hget (key : String) (hk1 : "asset" ≠ key) (hk2 : "seizeAmount" ≠ key) :
          ready.locals.get? key = frame.locals.get? key := by
        simp only [ready, absorbAssetSeizedFrame, absorbAssetNameFrame,
          Std.HashMap.get?_eq_getElem?, Std.HashMap.getElem?_insert, beq_iff_eq,
          if_neg hk1, if_neg hk2]
      have hp := absorbCollateralPrice_source hprice ready absorber account asset hc
        ((hget _ (by decide) (by decide)).trans hi)
        ((hget _ (by decide) (by decide)).trans hd)
        (by simp only [ready, absorbAssetSeizedFrame, Std.HashMap.get?_eq_getElem?,
          Std.HashMap.getElem?_insert]; rfl)
        ((hget _ (by decide) (by decide)).trans ha)
        ((hget _ (by decide) (by decide)).trans hb)
        (by simp only [ready, absorbAssetSeizedFrame, absorbAssetNameFrame,
          Std.HashMap.get?_eq_getElem?, Std.HashMap.getElem?_insert]; rfl)
      cases result with
      | none => exact execBlock_append hseize hp
      | some r =>
          obtain ⟨evm', price⟩ := r
          exact execBlock_append hseize hp

end Benchmarks.CompoundIII.Comet
