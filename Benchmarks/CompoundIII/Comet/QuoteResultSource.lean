import Benchmarks.CompoundIII.Comet.QuoteModel

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Benchmarks.CompoundIII.Comet.Immutables

namespace Benchmarks.CompoundIII.Comet

set_option maxRecDepth 10000

theorem quoteResult_eval (v : CometWithExtendedAssetListImmutables)
    (asset : AccountAddress) (amount assetPrice basePrice : UInt256) (out : ByteArray)
    (evm : EVM.State) :
    evalExpr? config (quoteFinalFrame v asset amount out assetPrice basePrice) evm quoteResultExpr =
      if QuoteResultValid v out amount basePrice (quoteDiscountedPrice v out assetPrice) then
        .ok (.int (quoteResultWord v out amount basePrice
          (quoteDiscountedPrice v out assetPrice)).toNat) else .revert := by
  let f := quoteFinalFrame v asset amount out assetPrice basePrice
  have hp : evalExpr? config f evm (.var "basePrice") = .ok (.int basePrice.toNat) := by
    simp only [evalExpr?, f, quoteFinalFrame, Std.HashMap.get?_eq_getElem?,
      Std.HashMap.getElem?_insert, EvalResult.ofOption]
    rfl
  have ha : evalExpr? config f evm (.var "baseAmount") = .ok (.int amount.toNat) := by
    simp only [evalExpr?, f, quoteFinalFrame, quoteDiscountFrame, quotePriceFrame, quoteAssetFrame,
      quoteEntry, Std.HashMap.get?_eq_getElem?, Std.HashMap.getElem?_insert, EvalResult.ofOption]
    rfl
  have hs : evalExpr? config f evm (.field (.var "assetInfo") "scale") =
      .ok (.int (calldataWord out 96).toNat) := by
    simp only [evalExpr?, f, quoteFinalFrame, quoteDiscountFrame, quotePriceFrame, quoteAssetFrame,
      Std.HashMap.get?_eq_getElem?, Std.HashMap.getElem?_insert, EvalResult.ofOption,
      bind, EvalResult.bind]
    rfl
  have hd : evalExpr? config f evm (.var "assetPriceDiscounted") =
      .ok (.int (quoteDiscountedPrice v out assetPrice).toNat) := by
    simp only [evalExpr?, f, quoteFinalFrame, quoteDiscountFrame, Std.HashMap.get?_eq_getElem?,
      Std.HashMap.getElem?_insert, EvalResult.ofOption]
    rfl
  have hb : evalExpr? config f evm (.immutable "baseScale") = .ok (.int v.baseScale.toNat) := by
    simp only [evalExpr?, f, quoteFinalFrame, quoteDiscountFrame, quotePriceFrame, quoteAssetFrame,
      quoteEntry, immStore_get_baseScale, EvalResult.ofOption]
    rfl
  by_cases hm1 : basePrice.toNat * amount.toNat < UInt256.size
  · have h1 := checkedMulSourceOk hp ha hm1
    by_cases hm2 : (UInt256.mul basePrice amount).toNat * (calldataWord out 96).toNat < UInt256.size
    · have h2 := checkedMulSourceOk h1 hs hm2
      by_cases hn1 : quoteDiscountedPrice v out assetPrice ≠ ⟨0⟩
      · have h3 := divSourceOk h2 hd hn1
        by_cases hn2 : v.baseScale ≠ ⟨0⟩
        · rw [if_pos (show QuoteResultValid v out amount basePrice
            (quoteDiscountedPrice v out assetPrice) from ⟨hm1, hm2, hn1, hn2⟩)]
          exact divSourceOk h3 hb hn2
        · rw [if_neg (show ¬ QuoteResultValid v out amount basePrice
            (quoteDiscountedPrice v out assetPrice) from fun h ↦ hn2 h.2.2.2)]
          have hz : v.baseScale = ⟨0⟩ := not_ne_iff.mp hn2
          rw [hz] at hb
          exact divSourceZero h3 hb
      · rw [if_neg (show ¬ QuoteResultValid v out amount basePrice
          (quoteDiscountedPrice v out assetPrice) from fun h ↦ hn1 h.2.2.1)]
        have hz : quoteDiscountedPrice v out assetPrice = ⟨0⟩ := not_ne_iff.mp hn1
        rw [hz] at hd
        have hr := divSourceZero h2 hd
        change evalExpr? config f evm _ = _
        simp only [quoteResultExpr, evalExpr?, hr, bind, EvalResult.bind]
    · rw [if_neg (show ¬ QuoteResultValid v out amount basePrice
        (quoteDiscountedPrice v out assetPrice) from fun h ↦ hm2 h.2.1)]
      have hr := checkedMulSourceOverflow h1 hs (le_of_not_gt hm2)
      change evalExpr? config f evm _ = _
      simp only [quoteResultExpr, evalExpr?, hr, bind, EvalResult.bind]
  · rw [if_neg (show ¬ QuoteResultValid v out amount basePrice
      (quoteDiscountedPrice v out assetPrice) from fun h ↦ hm1 h.1)]
    have hr := checkedMulSourceOverflow hp ha (le_of_not_gt hm1)
    change evalExpr? config f evm _ = _
    simp only [quoteResultExpr, evalExpr?, hr, bind, EvalResult.bind]

end Benchmarks.CompoundIII.Comet
