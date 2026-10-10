import Benchmarks.CompoundIII.Comet.QuoteTrace
import Benchmarks.CompoundIII.Comet.QuoteDiscountSource
import Benchmarks.CompoundIII.Comet.QuoteResultSource

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Benchmarks.CompoundIII.Comet.Immutables

namespace Benchmarks.CompoundIII.Comet

set_option maxRecDepth 2000

theorem quoteBaseFeed_eval (v : CometWithExtendedAssetListImmutables) (asset : AccountAddress)
    (amount price : UInt256) (out : ByteArray) (evm : EVM.State) :
    evalExpr? config (quoteDiscountFrame v asset amount out price) evm
      (.immutable "baseTokenPriceFeed") = .ok (.address v.baseTokenPriceFeed) := by
  simp only [evalExpr?, quoteDiscountFrame, quotePriceFrame, quoteAssetFrame, quoteEntry,
    immStore_get_baseTokenPriceFeed, EvalResult.ofOption]

theorem quoteAssetFeed_eval (v : CometWithExtendedAssetListImmutables) (asset : AccountAddress)
    (amount : UInt256) (out : ByteArray) (evm : EVM.State) :
    evalExpr? config (quoteAssetFrame v asset amount out) evm
      (.field (.var "assetInfo") "priceFeed") =
      .ok (.address (AccountAddress.ofNat (calldataWord out 64).toNat)) := by
  simp only [evalExpr?, quoteAssetFrame, Std.HashMap.get?_eq_getElem?,
    Std.HashMap.getElem?_insert, EvalResult.ofOption, bind, EvalResult.bind]
  rfl

theorem quoteFinish_source {v : CometWithExtendedAssetListImmutables} {assetOut : ByteArray}
    {amount price : UInt256} {evm : EVM.State} {result : Option (EVM.State × UInt256)}
    (ht : QuoteFinish v assetOut amount price evm result) (asset : AccountAddress) :
    QuoteSourceResult (quotePriceFrame v asset amount assetOut price) evm
      quoteTailBlock result := by
  cases ht with
  | discountFailed hd =>
      have hb := quoteDiscount_result v asset amount price assetOut evm
      rw [if_neg hd] at hb
      exact execBlockAppendReverted hb
  | @priceFailed evm' z out hd hc hh hv =>
      have hb := quoteDiscount_result v asset amount price assetOut evm
      rw [if_pos hd] at hb
      exact execBlockAppendOk hb (ExecBlock.consRevert (price_call_revert
        (quoteDiscountFrame v asset amount assetOut price) evm evm' v.baseTokenPriceFeed
        _ "basePrice" out z rfl (quoteBaseFeed_eval v asset amount price assetOut evm) hc hh hv))
  | @result evm' out hd hc hh hv =>
      have hb := quoteDiscount_result v asset amount price assetOut evm
      rw [if_pos hd] at hb
      have hp := price_call_ok (quoteDiscountFrame v asset amount assetOut price) evm evm'
        v.baseTokenPriceFeed _ "basePrice" out rfl
        (quoteBaseFeed_eval v asset amount price assetOut evm) hc hh hv
      have he := quoteResult_eval v asset amount price (calldataWord out 32) assetOut evm'
      apply Classical.byCases (p := QuoteResultValid v assetOut amount (calldataWord out 32)
        (quoteDiscountedPrice v assetOut price))
      · intro hm
        rw [if_pos hm]
        rw [if_pos hm] at he
        refine ⟨quoteFinalFrame v asset amount assetOut price (calldataWord out 32), ?_⟩
        exact execBlockAppendOk hb (ExecBlock.consNormal hp (ABlock.start.returns he))
      · intro hm
        rw [if_neg hm]
        rw [if_neg hm] at he
        exact execBlockAppendOk hb (ExecBlock.consNormal hp (ExecBlock.consRevert
          (ExecStmt.returnRevert (by
            change evalExprs? config (quoteFinalFrame v asset amount assetOut price
              (calldataWord out 32)) evm' _ = _
            simp only [evalExprs?, he, bind, EvalResult.bind]))))

theorem quoteAfterAsset_source {v : CometWithExtendedAssetListImmutables} {assetOut : ByteArray}
    {amount : UInt256} {evm : EVM.State} {result : Option (EVM.State × UInt256)}
    (ht : QuoteAfterAsset v assetOut amount evm result) (asset : AccountAddress) :
    QuoteSourceResult (quoteAssetFrame v asset amount assetOut) evm
      quoteAfterAssetBlock result := by
  cases ht with
  | @priceFailed evm' z out hc hh hv =>
      exact ExecBlock.consRevert (price_call_revert (quoteAssetFrame v asset amount assetOut)
        evm evm' _ _ "assetPrice" out z rfl
        (quoteAssetFeed_eval v asset amount assetOut evm) hc hh hv)
  | @priceOk evm' out result hc hh hv ht =>
      have hp := price_call_ok (quoteAssetFrame v asset amount assetOut) evm evm'
        _ _ "assetPrice" out rfl (quoteAssetFeed_eval v asset amount assetOut evm) hc hh hv
      have hb := quoteFinish_source ht asset
      cases result with
      | none => exact ExecBlock.consNormal hp hb
      | some r =>
          obtain ⟨evm'', value⟩ := r
          obtain ⟨final, hb⟩ := hb
          exact ⟨final, ExecBlock.consNormal hp hb⟩

theorem quoteTrace_source {v : CometWithExtendedAssetListImmutables} {asset : AccountAddress}
    {amount : UInt256} {evm : EVM.State} {result : Option (EVM.State × UInt256)}
    (ht : QuoteTrace v asset amount evm result) :
    QuoteSourceResult (quoteEntry v asset amount) evm quoteCallable.body result := by
  have he : evalExpr? config (quoteEntry v asset amount) evm (.var "asset") =
      .ok (.address asset) := by
    simp only [evalExpr?, quoteEntry, Std.HashMap.get?_eq_getElem?,
      Std.HashMap.getElem?_insert, EvalResult.ofOption]
    rfl
  cases ht with
  | assetFailed hs =>
      exact ExecBlock.consRevert (assetSearch_call hs (quoteEntry v asset amount)
        _ "assetInfo" rfl rfl he)
  | @assetOk evm' out result hs ht =>
      have hp := assetSearch_call hs (quoteEntry v asset amount) _ "assetInfo" rfl rfl he
      have hb := quoteAfterAsset_source ht asset
      cases result with
      | none => exact ExecBlock.consNormal hp hb
      | some r =>
          obtain ⟨evm'', value⟩ := r
          obtain ⟨final, hb⟩ := hb
          exact ⟨final, ExecBlock.consNormal hp hb⟩

theorem quote_call {v : CometWithExtendedAssetListImmutables} {asset : AccountAddress}
    {amount : UInt256} {evm : EVM.State} {result : Option (EVM.State × UInt256)}
    (ht : QuoteTrace v asset amount evm result) (frame : Frame) (assetExpr amountExpr : Expr)
    (ret : Ident) (hc : frame.contract = contract) (hi : frame.immutables = immStore v)
    (ha : evalExpr? config frame evm assetExpr = .ok (.address asset))
    (hb : evalExpr? config frame evm amountExpr = .ok (.int amount.toNat)) :
    match result with
    | none => ExecStmt config frame evm
        (.internalCall "quoteCollateral_body" [assetExpr, amountExpr] ret) .reverted
    | some (evm', value) => ExecStmt config frame evm
        (.internalCall "quoteCollateral_body" [assetExpr, amountExpr] ret)
        (.ok { frame with locals := frame.locals.insert ret (.int value.toNat) } evm') := by
  have he : evalExprs? config frame evm [assetExpr, amountExpr] =
      .ok [.address asset, .int amount.toNat] := by
    simp only [evalExprs?, ha, hb, bind, EvalResult.bind, pure]
  have hsource := quoteTrace_source ht
  cases result with
  | none =>
      exact ExecStmt.internalCallRevert (callee := quoteCallable)
        (locals := (quoteEntry v asset amount).locals) he
        (by rw [hc]; exact quoteCallable_lookup) rfl
        (by simpa only [hc, hi] using ExecFuncBody.execBlockRevert hsource)
  | some r =>
      obtain ⟨evm', value⟩ := r
      obtain ⟨final, hsource⟩ := hsource
      exact ExecStmt.internalCallReturn (callee := quoteCallable)
        (locals := (quoteEntry v asset amount).locals) he
        (by rw [hc]; exact quoteCallable_lookup) rfl
        (by simpa only [hc, hi] using ExecFuncBody.execBlockRet hsource)

end Benchmarks.CompoundIII.Comet
