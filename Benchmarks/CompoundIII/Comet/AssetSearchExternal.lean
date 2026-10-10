import Benchmarks.CompoundIII.Comet.AssetExternal
import Benchmarks.CompoundIII.Comet.AssetSearch
import Benchmarks.CompoundIII.Comet.AddressGetter

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Benchmarks.CompoundIII.Comet.Immutables

namespace Benchmarks.CompoundIII.Comet

theorem getAssetInfoByAddressTransition_body : getAssetInfoByAddressTransition.body =
    calldataPrologue [.internalCall "getAssetInfoByAddress_body" [.var "asset"] "info",
      .return [assetPublicExpr]] := rfl

theorem getAssetInfoByAddress_returns {σ σ₀ A I} {g : Sat256}
    (v : CometWithExtendedAssetListImmutables) (evm' : EVM.State) (out : ByteArray)
    (hv : I.weiValue = ⟨0⟩) (hhi : I.calldata.size < 2^255 + 4)
    (hsearch : AssetSearch v (AccountAddress.ofNat (calldataWord I.calldata 4).toNat)
      0 (initState σ σ₀ g A I) (some (evm', out))) :
    ∃ frame, ExecTransitionBody config contract (initState σ σ₀ g A I)
      (addressGetterArgs "asset" I) getAssetInfoByAddressTransition.body
      (.returned frame evm' (some [assetTuple out])) (immStore v) := by
  let frame := calldataLocalFrame
    { contract := contract, locals := addressGetterArgs "asset" I, immutables := immStore v }
    (initState σ σ₀ g A I)
  have hs := assetSearch_call hsearch frame (.var "asset") "info" rfl rfl (by
    simp only [evalExpr?, frame, calldataLocalFrame, addressGetterArgs,
      Std.HashMap.get?_eq_getElem?, Std.HashMap.getElem?_insert, EvalResult.ofOption]
    rfl)
  rw [getAssetInfoByAddressTransition_body]
  refine ⟨{ frame with locals := frame.locals.insert "info" (assetValue out) },
    .execBlockRet ?_⟩
  apply (calldataPrologue_ok hv hhi).run
  apply ExecBlock.consNormal hs
  exact ABlock.start.returns (assetPublicExpr_eval (by simp [Std.HashMap.getElem?_insert]))

theorem getAssetInfoByAddress_reverts {σ σ₀ A I} {g : Sat256}
    (v : CometWithExtendedAssetListImmutables)
    (hv : I.weiValue = ⟨0⟩) (hhi : I.calldata.size < 2^255 + 4)
    (hsearch : AssetSearch v (AccountAddress.ofNat (calldataWord I.calldata 4).toNat)
      0 (initState σ σ₀ g A I) none) :
    ExecTransitionBody config contract (initState σ σ₀ g A I)
      (addressGetterArgs "asset" I) getAssetInfoByAddressTransition.body
      .reverted (immStore v) := by
  let frame := calldataLocalFrame
    { contract := contract, locals := addressGetterArgs "asset" I, immutables := immStore v }
    (initState σ σ₀ g A I)
  have hs := assetSearch_call hsearch frame (.var "asset") "info" rfl rfl (by
    simp only [evalExpr?, frame, calldataLocalFrame, addressGetterArgs,
      Std.HashMap.get?_eq_getElem?, Std.HashMap.getElem?_insert, EvalResult.ofOption]
    rfl)
  rw [getAssetInfoByAddressTransition_body]
  apply ExecFuncBody.execBlockRevert
  apply (calldataPrologue_ok hv hhi).run
  exact ExecBlock.consRevert hs

end Benchmarks.CompoundIII.Comet
