import Benchmarks.CompoundIII.Comet.Dispatch
import Benchmarks.CompoundIII.Comet.GetAssetInfoEvm
import Benchmarks.CompoundIII.Comet.AssetExternal

/-!
# CometWithExtendedAssetList `getAssetInfo(uint8)`

Per-function proof: calldata decode facts, the EVM trace from the dispatcher arm through the
body, the Solm body evaluation, and the `…Body` theorem `Correct.lean` consumes.
Dispatcher arm entry: pc 871; reach lemma `cometWithExtendedAssetListReachGetAssetInfoBody`.
-/

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables
open Benchmarks.CompoundIII.Comet.Immutables

namespace Benchmarks.CompoundIII.Comet

set_option maxRecDepth 2000000

/-- `getAssetInfo(uint8)`: the theorem `Correct.lean` routes selector 57 to. -/
theorem cometWithExtendedAssetListGetAssetInfoBody {σ σ₀ A I} {g : UInt256} (v : CometWithExtendedAssetListImmutables)
    (hcode : I.code = deployedRuntime v) (hsize : I.calldata.size < UInt256.size)
    (hsel : selIs I (cometWithExtendedAssetListSelBytes 57)) :
    runtimeRefinementFor config contract σ σ₀ g A I (immStore v) := by
  have hsz : 4 ≤ I.calldata.size := calldata_size_ge_of_selIs I (cometWithExtendedAssetListSelBytes 57) rfl hsel
  have hd : selectorDispatchMsg contract I.calldata = some getAssetInfoTransition :=
    cometSelectorDispatch ⟨57, by decide⟩ hsel
  have hdecode : decodeCalldataWithMode config.abiDecodeMode
      (getAssetInfoTransition.params.map Param.name)
      (transitionSignature getAssetInfoTransition).paramTypes I.calldata =
      decodeCalldata ["i"] [.elem (.int (.uint ⟨8, by decide⟩))] I.calldata := by
    exact solc0815_decodeCalldata_scalar_eq (by decide)
  have hX := getAssetInfoX (σ := σ) (σ₀ := σ₀) (A := A)
    (g := Sat256.ofUInt256 g) v hcode hsz hsize hsel
  by_cases hlo : 36 ≤ I.calldata.size
  · by_cases hhi : I.calldata.size < 2^255 + 4
    · by_cases hc : (calldataWord I.calldata 4).toNat < 256
      · have hdec := hdecode.trans (decodeCalldata_uint_result ⟨8, by decide⟩ hlo hhi)
        change _ = (if (calldataWord I.calldata 4).toNat < 256 then
          some (uintFunctionArgs "i" I) else none) at hdec
        rw [if_pos hc] at hdec
        by_cases hv : I.weiValue = ⟨0⟩
        · unfold GetAssetInfoResult at hX
          rw [if_pos ⟨hv, hlo, hhi, hc⟩] at hX
          obtain ⟨evm', σ', z, out, hcall, haccounts, hout, hr⟩ := hX
          have hout' : out.size < 2^255 := lt_trans hout (by decide)
          by_cases hvalid : z = true ∧ AssetValid out
          · rw [if_pos hvalid] at hr
            rw [hvalid.1] at hcall
            obtain ⟨frame, hbody⟩ := getAssetInfo_returns v evm' out hv hhi hcall hout' hvalid.2
            exact selectorStateReturn_refines hcode hr hd hdec hbody haccounts
              (returnEquiv_of_encode (assetReturnEncoding hvalid.2.2))
          · rw [if_neg hvalid] at hr
            exact selectorRevert_refines hcode hr hd hdec
              (getAssetInfo_reverts v evm' out z hv hhi hcall hout' hvalid)
        · simp only [GetAssetInfoResult, hv, false_and, if_false] at hX
          apply selectorRevert_refines hcode hX hd hdec
          rw [getAssetInfoTransition_body]
          exact calldataPrologue_nonpayable hv
      · simp only [GetAssetInfoResult, hc, and_false, if_false] at hX
        exact selectorDecodeFailure_refines hcode hX hd
          (hdecode.trans (by
            rw [decodeCalldata_uint_result ⟨8, by decide⟩ hlo hhi]
            exact if_neg hc))
    · simp only [GetAssetInfoResult, hhi, false_and, and_false, if_false] at hX
      exact selectorDecodeFailure_refines hcode hX hd
        (hdecode.trans (decodeCalldata_uint_none_huge ⟨8, by decide⟩ (by omega)))
  · simp only [GetAssetInfoResult, hlo, false_and, and_false, if_false] at hX
    exact selectorDecodeFailure_refines hcode hX hd
      (hdecode.trans (decodeCalldata_uint_none_short ⟨8, by decide⟩ (by omega)))

end Benchmarks.CompoundIII.Comet
