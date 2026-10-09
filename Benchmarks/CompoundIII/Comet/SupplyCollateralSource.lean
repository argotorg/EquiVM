import Benchmarks.CompoundIII.Comet.SupplyCollateralPrepareSource
import Benchmarks.CompoundIII.Comet.TransferInSource

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Benchmarks.CompoundIII.Comet.Immutables

namespace Benchmarks.CompoundIII.Comet

set_option maxRecDepth 2000

theorem supplyCollateral_source {v sender dst asset amount evm result}
    (ht : SupplyCollateralTrace v sender dst asset amount evm result) :
    internalSourceResult config (supplyCollateralEntry (immStore v) sender dst asset amount)
      evm supplyCollateralCallable.body result := by
  let frame := supplyCollateralEntry (immStore v) sender dst asset amount
  have htransfer {r} (h : TransferInTrace asset sender amount evm r) :=
    transferIn_call h frame (.var "asset") (.var "from") (.var "amount") "__c0" rfl
      (by simp only [evalExpr?, frame, supplyCollateralEntry, Std.HashMap.get?_eq_getElem?,
            Std.HashMap.getElem?_insert, EvalResult.ofOption]; rfl)
      (by simp only [evalExpr?, frame, supplyCollateralEntry, Std.HashMap.get?_eq_getElem?,
            Std.HashMap.getElem?_insert, EvalResult.ofOption]; rfl)
      (by simp only [evalExpr?, frame, supplyCollateralEntry, Std.HashMap.get?_eq_getElem?,
            Std.HashMap.getElem?_insert, EvalResult.ofOption]; rfl)
  have hprepare := supplyCollateralPrepare_source (immStore v) sender dst asset amount
  have hsearch {evm' received r} (h : AssetSearch v asset 0 evm' r) :=
    assetSearch_call h (supplyCollateralPreparedFrame (immStore v) sender dst asset amount received)
      (.var "asset") "assetInfo" rfl rfl (by
        simp only [evalExpr?, supplyCollateralPreparedFrame, supplyCollateralTransferredFrame,
          supplyCollateralEntry, Std.HashMap.get?_eq_getElem?, Std.HashMap.getElem?_insert,
          EvalResult.ofOption]; rfl)
  apply internalBlockResult.toSource
  change internalBlockResult config frame evm
    (.internalCall "doTransferIn" [.var "asset", .var "from", .var "amount"] "__c0" ::
      (supplyCollateralPrepare ++ (.internalCall "getAssetInfoByAddress_body"
        [.var "asset"] "assetInfo" :: (supplyCollateralPrefix ++ supplyCollateralTail)))) result
  cases ht with
  | transferFailed ht => exact ExecBlock.consRevert (htransfer ht)
  | @tooLarge evm' received ht hw =>
    have hp := hprepare received evm'
    rw [if_neg hw] at hp
    exact ExecBlock.consNormal (htransfer ht)
      (execBlock_append_term hp (by intro _ _ h; cases h))
  | @assetFailed evm' received ht hw ha =>
    have hp := hprepare received evm'
    rw [if_pos hw] at hp
    exact ExecBlock.consNormal (htransfer ht)
      (execBlock_append hp (ExecBlock.consRevert (hsearch (received := received) ha)))
  | @done evm' received evm'' out ht hw ha hv =>
    have hp := hprepare received evm'
    rw [if_pos hw] at hp
    have hafter := supplyCollateralAfterAsset_source _ evm''
      (supplyCollateralPrepared_args (immStore v) sender dst asset amount received out) hv
    exact ((hafter.prepend (hsearch (received := received) ha)).prependBlock hp).prepend (htransfer ht)

theorem supplyCollateral_call {v sender dst asset amount evm result}
    (ht : SupplyCollateralTrace v sender dst asset amount evm result) (frame : Frame)
    (fromExpr dstExpr assetExpr amountExpr : Expr) (ret : Ident)
    (hc : frame.contract = contract) (hi : frame.immutables = immStore v)
    (hs : evalExpr? config frame evm fromExpr = .ok (.address sender))
    (hd : evalExpr? config frame evm dstExpr = .ok (.address dst))
    (ha : evalExpr? config frame evm assetExpr = .ok (.address asset))
    (ham : evalExpr? config frame evm amountExpr = .ok (.int amount.toNat)) :
    ExecStmt config frame evm
      (.internalCall "supplyCollateral" [fromExpr, dstExpr, assetExpr, amountExpr] ret)
      (internalStmtResult frame ret result) := by
  apply internalVoidCall (callee := supplyCollateralCallable)
    (locals := (supplyCollateralEntry (immStore v) sender dst asset amount).locals)
    (argVals := [.address sender, .address dst, .address asset, .int amount.toNat])
  · simp only [evalExprs?, hs, hd, ha, ham, pure, bind, EvalResult.bind]
  · rw [hc]; exact supplyCollateralCallable_lookup
  · rfl
  · simpa only [hc, hi] using supplyCollateral_source ht

end Benchmarks.CompoundIII.Comet
