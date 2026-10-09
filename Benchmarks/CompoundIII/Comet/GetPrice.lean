import Benchmarks.CompoundIII.Comet.Dispatch
import Benchmarks.CompoundIII.Comet.GetPriceEvm
import Benchmarks.CompoundIII.Comet.PriceExternal

/-!
# CometWithExtendedAssetList `getPrice(address)`

Per-function proof: calldata decode facts, the EVM trace from the dispatcher arm through the
body, the Solm body evaluation, and the `…Body` theorem `Correct.lean` consumes.
Dispatcher arm entry: pc 1195; reach lemma `cometWithExtendedAssetListReachGetPriceBody`.
-/

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables
open Benchmarks.CompoundIII.Comet.Immutables

namespace Benchmarks.CompoundIII.Comet

set_option maxRecDepth 10000

/-- `getPrice(address)`: the theorem `Correct.lean` routes selector 21 to. -/
theorem cometWithExtendedAssetListGetPriceBody {σ σ₀ A I} {g : UInt256} (v : CometWithExtendedAssetListImmutables)
    (hcode : I.code = deployedRuntime v) (hsize : I.calldata.size < UInt256.size)
    (hsel : selIs I (cometWithExtendedAssetListSelBytes 21)) :
    runtimeRefinementFor config contract σ σ₀ g A I (immStore v) := by
  have hsz : 4 ≤ I.calldata.size := calldata_size_ge_of_selIs I (cometWithExtendedAssetListSelBytes 21) rfl hsel
  have hd : selectorDispatchMsg contract I.calldata = some getPriceTransition :=
    cometSelectorDispatch ⟨21, by decide⟩ hsel
  have hdecode : decodeCalldataWithMode config.abiDecodeMode
      (getPriceTransition.params.map Param.name)
      (transitionSignature getPriceTransition).paramTypes I.calldata =
      decodeCalldata ["priceFeed"] [.elem .address] I.calldata := rfl
  have hX := getPriceX (σ := σ) (σ₀ := σ₀) (A := A)
    (g := Sat256.ofUInt256 g) v hcode hsz hsize hsel
  by_cases hlo : 36 ≤ I.calldata.size
  · by_cases hhi : I.calldata.size < 2^255 + 4
    · by_cases hc : (calldataWord I.calldata 4).toNat < EVM.addressModulus
      · have hdec := hdecode.trans (decodeCalldata_address_ok hlo hhi hc)
        by_cases hv : I.weiValue = ⟨0⟩
        · unfold GetPriceResult at hX
          rw [if_pos ⟨hv, hlo, hhi, hc⟩] at hX
          obtain ⟨evm', σ', z, out, hcall, haccounts, hout, hr⟩ := hX
          have hout' : out.size < 2^255 := lt_trans hout (by decide)
          by_cases hvalid : z = true ∧ PriceValid out
          · rw [if_pos hvalid] at hr
            rw [hvalid.1] at hcall
            obtain ⟨frame, hbody⟩ := getPrice_returns v evm' out hv hhi hcall hout' hvalid.2
            exact selectorStateReturn_refines hcode hr hd hdec hbody haccounts
              (returnEquiv_of_encode (uint256ReturnEncoding (calldataWord out 32)))
          · rw [if_neg hvalid] at hr
            exact selectorRevert_refines hcode hr hd hdec
              (getPrice_reverts v evm' out z hv hhi hcall hout' hvalid)
        · simp only [GetPriceResult, hv, false_and, if_false] at hX
          apply selectorRevert_refines hcode hX hd hdec
          rw [getPriceTransition_body]
          exact calldataPrologue_nonpayable hv
      · simp only [GetPriceResult, hc, and_false, if_false] at hX
        exact selectorDecodeFailure_refines hcode hX hd
          (hdecode.trans (decodeCalldata_address_none_noncanon hlo hhi hc))
    · simp only [GetPriceResult, hhi, false_and, and_false, if_false] at hX
      exact selectorDecodeFailure_refines hcode hX hd
        (hdecode.trans (decodeCalldata_address_none_huge (by omega)))
  · simp only [GetPriceResult, hlo, false_and, and_false, if_false] at hX
    exact selectorDecodeFailure_refines hcode hX hd
      (hdecode.trans (decodeCalldata_address_none_short hsz (by omega)))

end Benchmarks.CompoundIII.Comet
