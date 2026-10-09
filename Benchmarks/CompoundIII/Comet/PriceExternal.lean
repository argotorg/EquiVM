import Benchmarks.CompoundIII.Comet.PriceSource
import Benchmarks.CompoundIII.Comet.AddressGetter

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Benchmarks.CompoundIII.Comet.Immutables

namespace Benchmarks.CompoundIII.Comet

theorem getPriceTransition_body : getPriceTransition.body = calldataPrologue
    [.internalCall "getPrice_body" [.var "priceFeed"] "__r", .return [.var "__r"]] := rfl

theorem getPrice_returns {σ σ₀ A I} {g : Sat256}
    (v : CometWithExtendedAssetListImmutables) (evm' : EVM.State) (out : ByteArray)
    (hv : I.weiValue = ⟨0⟩) (hhi : I.calldata.size < 2^255 + 4)
    (hc : callViaEVM (initState σ σ₀ g A I)
      (AccountAddress.ofNat (calldataWord I.calldata 4).toNat) 0 pricePayload
        (true, evm', out) false)
    (hsize : out.size < 2^255) (hvalid : PriceValid out) :
    ∃ frame, ExecTransitionBody config contract (initState σ σ₀ g A I)
      (addressGetterArgs "priceFeed" I) getPriceTransition.body
      (.returned frame evm' (some [.int (calldataWord out 32).toNat])) (immStore v) := by
  let addr := AccountAddress.ofNat (calldataWord I.calldata 4).toNat
  let frame := calldataLocalFrame
    { contract := contract, locals := addressGetterArgs "priceFeed" I, immutables := immStore v }
    (initState σ σ₀ g A I)
  have he : evalExpr? config frame (initState σ σ₀ g A I) (.var "priceFeed") =
      .ok (.address addr) := by
    simp only [evalExpr?, frame, calldataLocalFrame, addressGetterArgs,
      Std.HashMap.get?_eq_getElem?, Std.HashMap.getElem?_insert, EvalResult.ofOption]
    rfl
  have hs := price_call_ok frame (initState σ σ₀ g A I) evm' addr _ "__r" out
    rfl he hc hsize hvalid
  rw [getPriceTransition_body]
  refine ⟨{ frame with locals := frame.locals.insert "__r" (.int (calldataWord out 32).toNat) },
    .execBlockRet ?_⟩
  apply (calldataPrologue_ok hv hhi).run
  apply ExecBlock.consNormal hs
  exact ABlock.start.returns (by
    simp only [evalExpr?, Std.HashMap.get?_eq_getElem?, Std.HashMap.getElem?_insert,
      EvalResult.ofOption]
    rfl)

theorem getPrice_reverts {σ σ₀ A I} {g : Sat256}
    (v : CometWithExtendedAssetListImmutables) (evm' : EVM.State) (out : ByteArray) (z : Bool)
    (hv : I.weiValue = ⟨0⟩) (hhi : I.calldata.size < 2^255 + 4)
    (hc : callViaEVM (initState σ σ₀ g A I)
      (AccountAddress.ofNat (calldataWord I.calldata 4).toNat) 0 pricePayload
        (z, evm', out) false)
    (hsize : out.size < 2^255) (hvalid : ¬ (z = true ∧ PriceValid out)) :
    ExecTransitionBody config contract (initState σ σ₀ g A I)
      (addressGetterArgs "priceFeed" I) getPriceTransition.body .reverted (immStore v) := by
  let addr := AccountAddress.ofNat (calldataWord I.calldata 4).toNat
  let frame := calldataLocalFrame
    { contract := contract, locals := addressGetterArgs "priceFeed" I, immutables := immStore v }
    (initState σ σ₀ g A I)
  have he : evalExpr? config frame (initState σ σ₀ g A I) (.var "priceFeed") =
      .ok (.address addr) := by
    simp only [evalExpr?, frame, calldataLocalFrame, addressGetterArgs,
      Std.HashMap.get?_eq_getElem?, Std.HashMap.getElem?_insert, EvalResult.ofOption]
    rfl
  rw [getPriceTransition_body]
  apply ExecFuncBody.execBlockRevert
  apply (calldataPrologue_ok hv hhi).run
  exact ExecBlock.consRevert
    (price_call_revert frame (initState σ σ₀ g A I) evm' addr _ "__r" out z
      rfl he hc hsize hvalid)

end Benchmarks.CompoundIII.Comet
