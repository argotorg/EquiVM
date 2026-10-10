import Benchmarks.CompoundIII.Comet.AssetSource
import Benchmarks.CompoundIII.Comet.UintFunction

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Benchmarks.CompoundIII.Comet.Immutables

namespace Benchmarks.CompoundIII.Comet

def assetPublicExpr : Expr :=
  .tupleLit [
    .field (.var "info") "offset",
    .field (.var "info") "asset",
    .field (.var "info") "priceFeed",
    .field (.var "info") "scale",
    .field (.var "info") "borrowCollateralFactor",
    .field (.var "info") "liquidateCollateralFactor",
    .field (.var "info") "liquidationFactor",
    .field (.var "info") "supplyCap"]

theorem getAssetInfoTransition_body : getAssetInfoTransition.body = calldataPrologue
    [.internalCall "getAssetInfo_body" [.var "i"] "info", .return [assetPublicExpr]] := rfl

theorem assetPublicExpr_eval {frame : Frame} {evm : EVM.State} {out : ByteArray}
    (hi : frame.locals.get? "info" = some (assetValue out)) :
    evalExpr? config frame evm assetPublicExpr = .ok (assetTuple out) := by
  simp only [assetPublicExpr, evalExpr?, evalExprList?, hi, assetValue, lookupField?,
    EvalResult.ofOption, pure, bind, EvalResult.bind]
  rfl

theorem getAssetInfo_returns {σ σ₀ A I} {g : Sat256}
    (v : CometWithExtendedAssetListImmutables) (evm' : EVM.State) (out : ByteArray)
    (hv : I.weiValue = ⟨0⟩) (hhi : I.calldata.size < 2^255 + 4)
    (hc : callViaEVM (initState σ σ₀ g A I)
      v.assetList 0 (assetPayload (calldataWord I.calldata 4))
        (true, evm', out) false)
    (hsize : out.size < 2^255) (hvalid : AssetValid out) :
    ∃ frame, ExecTransitionBody config contract (initState σ σ₀ g A I)
      (uintFunctionArgs "i" I) getAssetInfoTransition.body
      (.returned frame evm' (some [assetTuple out])) (immStore v) := by
  let i := calldataWord I.calldata 4
  let frame := calldataLocalFrame
    { contract := contract, locals := uintFunctionArgs "i" I, immutables := immStore v }
    (initState σ σ₀ g A I)
  have he : evalExpr? config frame (initState σ σ₀ g A I) (.var "i") =
      .ok (.int (Int.ofNat i.toNat)) := by
    simp only [evalExpr?, frame, calldataLocalFrame, uintFunctionArgs,
      Std.HashMap.get?_eq_getElem?, Std.HashMap.getElem?_insert, EvalResult.ofOption]
    rfl
  have hs := asset_call_ok frame (initState σ σ₀ g A I) evm' i v.assetList _ "info" out
    rfl (immStore_get_assetList v) he hc hsize hvalid
  rw [getAssetInfoTransition_body]
  refine ⟨{ frame with locals := frame.locals.insert "info" (assetValue out) },
    .execBlockRet ?_⟩
  apply (calldataPrologue_ok hv hhi).run
  apply ExecBlock.consNormal hs
  exact ABlock.start.returns (assetPublicExpr_eval (by simp [Std.HashMap.getElem?_insert]))

theorem getAssetInfo_reverts {σ σ₀ A I} {g : Sat256}
    (v : CometWithExtendedAssetListImmutables) (evm' : EVM.State) (out : ByteArray) (z : Bool)
    (hv : I.weiValue = ⟨0⟩) (hhi : I.calldata.size < 2^255 + 4)
    (hc : callViaEVM (initState σ σ₀ g A I)
      v.assetList 0 (assetPayload (calldataWord I.calldata 4))
        (z, evm', out) false)
    (hsize : out.size < 2^255) (hvalid : ¬ (z = true ∧ AssetValid out)) :
    ExecTransitionBody config contract (initState σ σ₀ g A I)
      (uintFunctionArgs "i" I) getAssetInfoTransition.body .reverted (immStore v) := by
  let i := calldataWord I.calldata 4
  let frame := calldataLocalFrame
    { contract := contract, locals := uintFunctionArgs "i" I, immutables := immStore v }
    (initState σ σ₀ g A I)
  have he : evalExpr? config frame (initState σ σ₀ g A I) (.var "i") =
      .ok (.int (Int.ofNat i.toNat)) := by
    simp only [evalExpr?, frame, calldataLocalFrame, uintFunctionArgs,
      Std.HashMap.get?_eq_getElem?, Std.HashMap.getElem?_insert, EvalResult.ofOption]
    rfl
  rw [getAssetInfoTransition_body]
  apply ExecFuncBody.execBlockRevert
  apply (calldataPrologue_ok hv hhi).run
  exact ExecBlock.consRevert
    (asset_call_revert frame (initState σ σ₀ g A I) evm' i v.assetList _ "info" out z
      rfl (immStore_get_assetList v) he hc hsize hvalid)

end Benchmarks.CompoundIII.Comet
