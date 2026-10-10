import Benchmarks.CompoundIII.Comet.QuoteModel

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Benchmarks.CompoundIII.Comet.Immutables

namespace Benchmarks.CompoundIII.Comet

set_option maxRecDepth 10000

theorem quoteDiscount_result (v : CometWithExtendedAssetListImmutables)
    (asset : AccountAddress) (amount price : UInt256) (out : ByteArray) (evm : EVM.State) :
    ExecBlock config (quotePriceFrame v asset amount out price) evm quoteDiscountBlock
      (if QuoteDiscountValid v out price then
        .ok (quoteDiscountFrame v asset amount out price) evm else .reverted) := by
  let f0 := quotePriceFrame v asset amount out price
  let f1 : Frame := { f0 with
    locals := f0.locals.insert "discountFactor" (.int (quoteDiscountFactor v out).toNat) }
  have hs : evalExpr? config f0 evm (.immutable "storeFrontPriceFactor") =
      .ok (.int v.storeFrontPriceFactor.toNat) := by
    simp only [evalExpr?, f0, quotePriceFrame, quoteAssetFrame, quoteEntry,
      immStore_get_storeFrontPriceFactor, EvalResult.ofOption]
    rfl
  have hl : evalExpr? config f0 evm (.field (.var "assetInfo") "liquidationFactor") =
      .ok (.int (calldataWord out 192).toNat) := by
    simp only [evalExpr?, f0, quotePriceFrame, quoteAssetFrame, Std.HashMap.get?_eq_getElem?,
      Std.HashMap.getElem?_insert, EvalResult.ofOption, bind, EvalResult.bind]
    rfl
  have hk (f : Frame) : evalExpr? config f evm (.intLit 1000000000000000000) =
      .ok (.int quoteFactorScale.toNat) := by
    norm_num [evalExpr?, pure, quoteFactorScale, UInt256.toNat, UInt256.size]
  by_cases hsub : (calldataWord out 192).toNat ≤ quoteFactorScale.toNat
  · have hd := checkedNarrowSubSourceOk ⟨64, by decide⟩ (hk f0) hl (by decide) hsub
    by_cases hmul : v.storeFrontPriceFactor.toNat *
        (UInt256.sub quoteFactorScale (calldataWord out 192)).toNat < UInt256.size
    · apply ExecBlock.consNormal (mulFactor_call_ok f0 evm v.storeFrontPriceFactor
        (UInt256.sub quoteFactorScale (calldataWord out 192)) _ _ "discountFactor" rfl hs hd hmul)
      have hf : evalExpr? config f1 evm (.var "discountFactor") =
          .ok (.int (quoteDiscountFactor v out).toNat) := by
        simp only [evalExpr?, f1, Std.HashMap.get?_eq_getElem?, Std.HashMap.getElem?_insert,
          EvalResult.ofOption]
        rfl
      have hp : evalExpr? config f1 evm (.var "assetPrice") = .ok (.int price.toNat) := by
        simp only [evalExpr?, f1, f0, quotePriceFrame, Std.HashMap.get?_eq_getElem?,
          Std.HashMap.getElem?_insert, EvalResult.ofOption]
        rfl
      by_cases hsub2 : (quoteDiscountFactor v out).toNat ≤ quoteFactorScale.toNat
      · have hd2 := checkedNarrowSubSourceOk ⟨256, by decide⟩ (hk f1) hf (by decide) hsub2
        by_cases hmul2 : price.toNat *
            (UInt256.sub quoteFactorScale (quoteDiscountFactor v out)).toNat < UInt256.size
        · rw [if_pos (show QuoteDiscountValid v out price from ⟨hsub, hmul, hsub2, hmul2⟩)]
          exact ExecBlock.consNormal (mulFactor_call_ok f1 evm price
            (UInt256.sub quoteFactorScale (quoteDiscountFactor v out)) _ _
            "assetPriceDiscounted" rfl hp hd2 hmul2) ExecBlock.nil
        · rw [if_neg (show ¬ QuoteDiscountValid v out price from fun h ↦ hmul2 h.2.2.2)]
          exact ExecBlock.consRevert (mulFactor_call_revert f1 evm price
            (UInt256.sub quoteFactorScale (quoteDiscountFactor v out)) _ _
            "assetPriceDiscounted" rfl hp hd2 hmul2)
      · rw [if_neg (show ¬ QuoteDiscountValid v out price from fun h ↦ hsub2 h.2.2.1)]
        apply ExecBlock.consRevert
        apply ExecStmt.internalCallArgsRevert
        have hd2 := checkedNarrowSubSourceUnderflow ⟨256, by decide⟩
          (hk f1) hf (Nat.lt_of_not_ge hsub2)
        change evalExprs? config f1 evm _ = _
        simp only [evalExprs?, hp, hd2, bind, EvalResult.bind]
    · rw [if_neg (show ¬ QuoteDiscountValid v out price from fun h ↦ hmul h.2.1)]
      exact ExecBlock.consRevert (mulFactor_call_revert f0 evm v.storeFrontPriceFactor
        (UInt256.sub quoteFactorScale (calldataWord out 192)) _ _ "discountFactor" rfl hs hd hmul)
  · rw [if_neg (show ¬ QuoteDiscountValid v out price from fun h ↦ hsub h.1)]
    apply ExecBlock.consRevert
    apply ExecStmt.internalCallArgsRevert
    have hd := checkedNarrowSubSourceUnderflow ⟨64, by decide⟩ (hk f0) hl (Nat.lt_of_not_ge hsub)
    change evalExprs? config f0 evm _ = _
    simp only [evalExprs?, hs, hd, bind, EvalResult.bind]

end Benchmarks.CompoundIII.Comet
