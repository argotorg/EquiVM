import Benchmarks.CompoundIII.Comet.AbsorbBalanceModel
import Benchmarks.CompoundIII.Comet.Signed256
import Benchmarks.CompoundIII.Comet.IndexAccrual

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Benchmarks.CompoundIII.Comet.Immutables

namespace Benchmarks.CompoundIII.Comet

theorem absorbBalance_source (frame : Frame) (evm : EVM.State)
    (v : CometWithExtendedAssetListImmutables) (old delta price : UInt256)
    (hc : frame.contract = contract) (hi : frame.immutables = immStore v)
    (ho : frame.locals.get? "oldBalance" = some (.int (signedWord old)))
    (hd : frame.locals.get? "deltaValue" = some (.int delta.toNat))
    (hp : frame.locals.get? "basePrice" = some (.int price.toNat)) :
    ExecBlock config frame evm absorbBalanceBlock
      (if AbsorbBalanceValid v old delta price then
        .ok (absorbBalanceFrame frame v old delta price) evm else .reverted) := by
  have hdiv := divPrice_call frame evm delta price (collateralBaseScale v)
    (.var "deltaValue") (.var "basePrice")
    (.cast (.immutable "baseScale") (.elem (.int (.uint ⟨64, by decide⟩)))) "deltaBalance" hc
    (by simp only [evalExpr?, hd, EvalResult.ofOption])
    (by simp only [evalExpr?, hp, EvalResult.ofOption]) (by
      apply uintCastWord_source
      simp only [evalExpr?, hi, immStore_get_baseScale, EvalResult.ofOption])
  by_cases hv : DivPriceValid delta price (collateralBaseScale v)
  · rw [if_pos hv] at hdiv
    let f1 := absorbBalanceDivFrame frame v delta price
    have hd1 : evalExpr? config f1 evm (.var "deltaBalance") =
        .ok (.int (absorbDeltaBalance v delta price).toNat) := by
      simp only [evalExpr?, f1, absorbBalanceDivFrame, Std.HashMap.get?_eq_getElem?,
        Std.HashMap.getElem?_insert, EvalResult.ofOption]; rfl
    by_cases hn : (absorbDeltaBalance v delta price).toNat < 2^255
    · have hsigned := signed256_call_ok f1 evm (absorbDeltaBalance v delta price)
        (.var "deltaBalance") "__c9" hc hd1 hn
      let f2 := absorbBalanceSignedFrame frame v delta price
      have ho2 : f2.locals.get? "oldBalance" = some (.int (signedWord old)) := by
        simpa only [f2, absorbBalanceSignedFrame, absorbBalanceDivFrame,
          Std.HashMap.get?_eq_getElem?, Std.HashMap.getElem?_insert] using ho
      have hd2 : f2.locals.get? "__c9" = some (.int (absorbDeltaBalance v delta price).toNat) := by
        simp only [f2, absorbBalanceSignedFrame, Std.HashMap.get?_eq_getElem?,
          Std.HashMap.getElem?_insert]; rfl
      have he : evalExpr? config f2 evm (.binary .add (.var "oldBalance") (.var "__c9")) =
          .ok (.int (signedWord old + Int.ofNat (absorbDeltaBalance v delta price).toNat)) := by
        simp only [evalExpr?, ho2, hd2, EvalResult.ofOption, bind, EvalResult.bind, evalBinaryOp?]
        rfl
      by_cases hsum : signedWord old + Int.ofNat (absorbDeltaBalance v delta price).toNat <
          (2^255 : Int)
      · have hvalid : AbsorbBalanceValid v old delta price := ⟨hv, hn, hsum⟩
        rw [if_pos hvalid]
        have hlo : -(2^255 : Int) ≤
            signedWord old + Int.ofNat (absorbDeltaBalance v delta price).toNat := by
          have ho := (signedWord_bounds old).1
          change -(2^255 : Int) ≤ signedWord old at ho
          simp only [Int.ofNat_eq_natCast]
          omega
        have he' := signedRangeSourceOk he hlo hsum
        rw [← absorbBalanceSum_signed hvalid] at he'
        let summed : Frame := { f2 with
          locals := f2.locals.insert "newBalance" (.int (signedWord (absorbBalanceSum v old delta price))) }
        have hget : summed.locals.get? "newBalance" =
            some (.int (signedWord (absorbBalanceSum v old delta price))) := by
          simp only [summed, Std.HashMap.get?_eq_getElem?, Std.HashMap.getElem?_insert]; rfl
        have hcond : evalExpr? config summed evm (.binary .lt (.var "newBalance") (.intLit 0)) =
            .ok (.bool (decide (signedWord (absorbBalanceSum v old delta price) < 0))) := by
          simp only [evalExpr?, hget, EvalResult.ofOption, pure, bind, EvalResult.bind, evalBinaryOp?]
        by_cases hz : (absorbBalanceSum v old delta price).toNat < 2^255
        · have hpos := (signedWord_nonneg_iff _).2 hz
          simp only [absorbBalanceFrame, if_pos hz]
          exact ExecBlock.consNormal hdiv (ExecBlock.consNormal hsigned
            (ExecBlock.consNormal (ExecStmt.letDecl he') (ExecBlock.consNormal
              (ExecStmt.iteFalse (hcond.trans (by rw [decide_eq_false (by omega)])) .nil) .nil)))
        · have hneg : signedWord (absorbBalanceSum v old delta price) < 0 := by
            have hh := signedWord_nonneg_iff (absorbBalanceSum v old delta price)
            omega
          simp only [absorbBalanceFrame, if_neg hz]
          exact ExecBlock.consNormal hdiv (ExecBlock.consNormal hsigned
            (ExecBlock.consNormal (ExecStmt.letDecl he') (ExecBlock.consNormal
              (ExecStmt.iteTrue (hcond.trans (by rw [decide_eq_true hneg]))
                (execBlock_singleton (ExecStmt.assign (by simp only [evalExpr?, pure])
                  (assignLocalFrame hget)))) .nil)))
      · rw [if_neg (fun hh ↦ hsum hh.2.2)]
        exact ExecBlock.consNormal hdiv (ExecBlock.consNormal hsigned
          (ExecBlock.consRevert (ExecStmt.letDeclRevert
            (signedRangeSourceOverflow he (le_of_not_gt hsum)))))
    · rw [if_neg (fun hh ↦ hn hh.2.1)]
      exact ExecBlock.consNormal hdiv (ExecBlock.consRevert
        (signed256_call_revert f1 evm (absorbDeltaBalance v delta price)
          (.var "deltaBalance") "__c9" hc hd1 hn))
  · rw [if_neg hv] at hdiv
    rw [if_neg (fun hh ↦ hv hh.1)]
    exact ExecBlock.consRevert hdiv

end Benchmarks.CompoundIII.Comet
