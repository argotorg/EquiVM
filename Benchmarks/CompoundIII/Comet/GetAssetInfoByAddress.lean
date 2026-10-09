import Benchmarks.CompoundIII.Comet.Dispatch
import Benchmarks.CompoundIII.Comet.GetAssetInfoByAddressEvm
import Benchmarks.CompoundIII.Comet.AssetSearchExternal

/-!
# CometWithExtendedAssetList `getAssetInfoByAddress(address)`

Per-function proof: calldata decode facts, the EVM trace from the dispatcher arm through the
body, the Solm body evaluation, and the `…Body` theorem `Correct.lean` consumes.
Dispatcher arm entry: pc 1204; reach lemma `cometWithExtendedAssetListReachGetAssetInfoByAddressBody`.
-/

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables
open Benchmarks.CompoundIII.Comet.Immutables

namespace Benchmarks.CompoundIII.Comet

set_option maxRecDepth 10000

/-- `getAssetInfoByAddress(address)`: the theorem `Correct.lean` routes selector 20 to. -/
theorem cometWithExtendedAssetListGetAssetInfoByAddressBody {σ σ₀ A I} {g : UInt256} (v : CometWithExtendedAssetListImmutables)
    (hcode : I.code = deployedRuntime v) (hsize : I.calldata.size < UInt256.size)
    (hsel : selIs I (cometWithExtendedAssetListSelBytes 20)) :
    runtimeRefinementFor config contract σ σ₀ g A I (immStore v) := by
  have hsz : 4 ≤ I.calldata.size := calldata_size_ge_of_selIs I (cometWithExtendedAssetListSelBytes 20) rfl hsel
  have hd : selectorDispatchMsg contract I.calldata = some getAssetInfoByAddressTransition :=
    cometSelectorDispatch ⟨20, by decide⟩ hsel
  have hdecode : decodeCalldataWithMode config.abiDecodeMode
      (getAssetInfoByAddressTransition.params.map Param.name)
      (transitionSignature getAssetInfoByAddressTransition).paramTypes I.calldata =
      decodeCalldata ["asset"] [.elem .address] I.calldata := rfl
  have hX := getAssetInfoByAddressX (σ := σ) (σ₀ := σ₀) (A := A)
    (g := Sat256.ofUInt256 g) v hcode hsz hsize hsel
  by_cases hlo : 36 ≤ I.calldata.size
  · by_cases hhi : I.calldata.size < 2^255 + 4
    · by_cases hc : (calldataWord I.calldata 4).toNat < EVM.addressModulus
      · have hdec := hdecode.trans (decodeCalldata_address_ok hlo hhi hc)
        by_cases hv : I.weiValue = ⟨0⟩
        · unfold GetAssetInfoByAddressResult at hX
          rw [if_pos ⟨hv, hlo, hhi, hc⟩] at hX
          obtain ⟨result, hsearch, hr⟩ := hX
          cases result with
          | none =>
              exact selectorRevert_refines hcode hr hd hdec
                (getAssetInfoByAddress_reverts v hv hhi hsearch)
          | some result =>
              obtain ⟨evm', out⟩ := result
              obtain ⟨hvalid, hr⟩ := hr
              obtain ⟨frame, hbody⟩ := getAssetInfoByAddress_returns v evm' out hv hhi hsearch
              exact selectorStateReturn_refines hcode hr hd hdec hbody rfl
                (returnEquiv_of_encode (assetReturnEncoding hvalid))
        · simp only [GetAssetInfoByAddressResult, hv, false_and, if_false] at hX
          apply selectorRevert_refines hcode hX hd hdec
          rw [getAssetInfoByAddressTransition_body]
          exact calldataPrologue_nonpayable hv
      · simp only [GetAssetInfoByAddressResult, hc, and_false, if_false] at hX
        exact selectorDecodeFailure_refines hcode hX hd
          (hdecode.trans (decodeCalldata_address_none_noncanon hlo hhi hc))
    · simp only [GetAssetInfoByAddressResult, hhi, false_and, and_false, if_false] at hX
      exact selectorDecodeFailure_refines hcode hX hd
        (hdecode.trans (decodeCalldata_address_none_huge (by omega)))
  · simp only [GetAssetInfoByAddressResult, hlo, false_and, and_false, if_false] at hX
    exact selectorDecodeFailure_refines hcode hX hd
      (hdecode.trans (decodeCalldata_address_none_short hsz (by omega)))

end Benchmarks.CompoundIII.Comet
