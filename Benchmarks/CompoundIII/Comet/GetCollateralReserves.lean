import Benchmarks.CompoundIII.Comet.Dispatch
import Benchmarks.CompoundIII.Comet.GetCollateralReservesEvm
import Benchmarks.CompoundIII.Comet.CollateralReservesExternal

/-!
# CometWithExtendedAssetList `getCollateralReserves(address)`

Per-function proof: calldata decode facts, the EVM trace from the dispatcher arm through the
body, the Solm body evaluation, and the `…Body` theorem `Correct.lean` consumes.
Dispatcher arm entry: pc 997; reach lemma `cometWithExtendedAssetListReachGetCollateralReservesBody`.
-/

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables
open Benchmarks.CompoundIII.Comet.Immutables

namespace Benchmarks.CompoundIII.Comet

set_option maxRecDepth 10000

/-- `getCollateralReserves(address)`: the theorem `Correct.lean` routes selector 44 to. -/
theorem cometWithExtendedAssetListGetCollateralReservesBody {σ σ₀ A I} {g : UInt256} (v : CometWithExtendedAssetListImmutables)
    (hcode : I.code = deployedRuntime v) (hsize : I.calldata.size < UInt256.size)
    (hsel : selIs I (cometWithExtendedAssetListSelBytes 44)) :
    runtimeRefinementFor config contract σ σ₀ g A I (immStore v) := by
  have hsz : 4 ≤ I.calldata.size := calldata_size_ge_of_selIs I (cometWithExtendedAssetListSelBytes 44) rfl hsel
  have hd : selectorDispatchMsg contract I.calldata = some getCollateralReservesTransition :=
    cometSelectorDispatch ⟨44, by decide⟩ hsel
  have hdecode : decodeCalldataWithMode config.abiDecodeMode
      (getCollateralReservesTransition.params.map Param.name)
      (transitionSignature getCollateralReservesTransition).paramTypes I.calldata =
      decodeCalldata ["asset"] [.elem .address] I.calldata := rfl
  have hX := getCollateralReservesX (σ := σ) (σ₀ := σ₀) (A := A)
    (g := Sat256.ofUInt256 g) v hcode hsz hsize hsel
  by_cases hlo : 36 ≤ I.calldata.size
  · by_cases hhi : I.calldata.size < 2^255 + 4
    · by_cases hc : (calldataWord I.calldata 4).toNat < EVM.addressModulus
      · have hdec := hdecode.trans (decodeCalldata_address_ok hlo hhi hc)
        by_cases hv : I.weiValue = ⟨0⟩
        · unfold GetCollateralReservesResult at hX
          rw [if_pos ⟨hv, hlo, hhi, hc⟩] at hX
          obtain ⟨evm', σ', z, out, hcall, haccounts, hout, hr⟩ := hX
          have hout' : out.size < 2^255 := lt_trans hout (by decide)
          by_cases hvalid : CollateralReservesValid evm'
              (AccountAddress.ofNat (calldataWord I.calldata 4).toNat) z out
          · rw [if_pos hvalid] at hr
            have hz := hvalid.1
            rw [hz] at hcall hvalid
            obtain ⟨frame, hbody⟩ :=
              getCollateralReserves_returns v evm' out hv hhi hcall hout' hvalid
            exact selectorStateReturn_refines hcode hr hd hdec hbody haccounts
              (returnEquiv_of_encode (uint256ReturnEncoding
                (collateralReservesValue evm'
                  (AccountAddress.ofNat (calldataWord I.calldata 4).toNat) out)))
          · rw [if_neg hvalid] at hr
            exact selectorRevert_refines hcode hr hd hdec
              (getCollateralReserves_reverts v evm' out z hv hhi hcall hout' hvalid)
        · simp only [GetCollateralReservesResult, hv, false_and, if_false] at hX
          apply selectorRevert_refines hcode hX hd hdec
          rw [getCollateralReservesTransition_body]
          exact calldataPrologue_nonpayable hv
      · simp only [GetCollateralReservesResult, hc, and_false, if_false] at hX
        exact selectorDecodeFailure_refines hcode hX hd
          (hdecode.trans (decodeCalldata_address_none_noncanon hlo hhi hc))
    · simp only [GetCollateralReservesResult, hhi, false_and, and_false, if_false] at hX
      exact selectorDecodeFailure_refines hcode hX hd
        (hdecode.trans (decodeCalldata_address_none_huge (by omega)))
  · simp only [GetCollateralReservesResult, hlo, false_and, and_false, if_false] at hX
    exact selectorDecodeFailure_refines hcode hX hd
      (hdecode.trans (decodeCalldata_address_none_short hsz (by omega)))

end Benchmarks.CompoundIII.Comet
