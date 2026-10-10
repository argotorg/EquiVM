import Benchmarks.CompoundIII.Comet.CollateralReservesSource
import Benchmarks.CompoundIII.Comet.AddressGetter

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Benchmarks.CompoundIII.Comet.Immutables

namespace Benchmarks.CompoundIII.Comet

theorem getCollateralReservesTransition_body :
    getCollateralReservesTransition.body = calldataPrologue
    [.internalCall "getCollateralReserves_body" [.var "asset"] "__r", .return [.var "__r"]] := rfl

theorem getCollateralReserves_returns {σ σ₀ A I} {g : Sat256}
    (v : CometWithExtendedAssetListImmutables) (evm' : EVM.State) (out : ByteArray)
    (hv : I.weiValue = ⟨0⟩) (hhi : I.calldata.size < 2^255 + 4)
    (hc : callViaEVM (initState σ σ₀ g A I)
      (AccountAddress.ofNat (calldataWord I.calldata 4).toNat) 0 (tokenBalancePayload I.codeOwner)
        (true, evm', out) false)
    (hsize : out.size < 2^255)
    (hvalid : CollateralReservesValid evm'
      (AccountAddress.ofNat (calldataWord I.calldata 4).toNat) true out) :
    ∃ frame, ExecTransitionBody config contract (initState σ σ₀ g A I)
      (addressGetterArgs "asset" I) getCollateralReservesTransition.body
      (.returned frame evm' (some [.int (collateralReservesValue evm'
        (AccountAddress.ofNat (calldataWord I.calldata 4).toNat) out).toNat])) (immStore v) := by
  let addr := AccountAddress.ofNat (calldataWord I.calldata 4).toNat
  let frame := calldataLocalFrame
    { contract := contract, locals := addressGetterArgs "asset" I, immutables := immStore v }
    (initState σ σ₀ g A I)
  have he : evalExpr? config frame (initState σ σ₀ g A I) (.var "asset") =
      .ok (.address addr) := by
    simp only [evalExpr?, frame, calldataLocalFrame, addressGetterArgs,
      Std.HashMap.get?_eq_getElem?, Std.HashMap.getElem?_insert, EvalResult.ofOption]
    rfl
  have hs := collateralReserves_call_ok frame (initState σ σ₀ g A I) evm' addr _ "__r" out
    rfl he hc hsize hvalid
  rw [getCollateralReservesTransition_body]
  refine ⟨{ frame with locals :=
    frame.locals.insert "__r" (.int (collateralReservesValue evm' addr out).toNat) },
    .execBlockRet ?_⟩
  apply (calldataPrologue_ok hv hhi).run
  apply ExecBlock.consNormal hs
  exact ABlock.start.returns (by
    simp only [evalExpr?, Std.HashMap.get?_eq_getElem?, Std.HashMap.getElem?_insert,
      EvalResult.ofOption]
    rfl)

theorem getCollateralReserves_reverts {σ σ₀ A I} {g : Sat256}
    (v : CometWithExtendedAssetListImmutables) (evm' : EVM.State) (out : ByteArray) (z : Bool)
    (hv : I.weiValue = ⟨0⟩) (hhi : I.calldata.size < 2^255 + 4)
    (hc : callViaEVM (initState σ σ₀ g A I)
      (AccountAddress.ofNat (calldataWord I.calldata 4).toNat) 0 (tokenBalancePayload I.codeOwner)
        (z, evm', out) false)
    (hsize : out.size < 2^255)
    (hvalid : ¬ CollateralReservesValid evm'
      (AccountAddress.ofNat (calldataWord I.calldata 4).toNat) z out) :
    ExecTransitionBody config contract (initState σ σ₀ g A I)
      (addressGetterArgs "asset" I) getCollateralReservesTransition.body
      .reverted (immStore v) := by
  let addr := AccountAddress.ofNat (calldataWord I.calldata 4).toNat
  let frame := calldataLocalFrame
    { contract := contract, locals := addressGetterArgs "asset" I, immutables := immStore v }
    (initState σ σ₀ g A I)
  have he : evalExpr? config frame (initState σ σ₀ g A I) (.var "asset") =
      .ok (.address addr) := by
    simp only [evalExpr?, frame, calldataLocalFrame, addressGetterArgs,
      Std.HashMap.get?_eq_getElem?, Std.HashMap.getElem?_insert, EvalResult.ofOption]
    rfl
  rw [getCollateralReservesTransition_body]
  apply ExecFuncBody.execBlockRevert
  apply (calldataPrologue_ok hv hhi).run
  exact ExecBlock.consRevert
    (collateralReserves_call_revert frame (initState σ σ₀ g A I) evm' addr _ "__r" out z
      rfl he hc hsize hvalid)

end Benchmarks.CompoundIII.Comet
