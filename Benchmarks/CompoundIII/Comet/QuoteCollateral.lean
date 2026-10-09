import Benchmarks.CompoundIII.Comet.Dispatch
import Benchmarks.CompoundIII.Comet.QuoteCollateralEvm
import Benchmarks.CompoundIII.Comet.QuoteExternal

/-!
# CometWithExtendedAssetList `quoteCollateral(address,uint256)`

Per-function proof: calldata decode facts, the EVM trace from the dispatcher arm through the
body, the Solm body evaluation, and the `…Body` theorem `Correct.lean` consumes.
Dispatcher arm entry: pc 1096; reach lemma `cometWithExtendedAssetListReachQuoteCollateralBody`.
-/

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables
open Benchmarks.CompoundIII.Comet.Immutables

namespace Benchmarks.CompoundIII.Comet

set_option maxRecDepth 2000

/-- `quoteCollateral(address,uint256)`: the theorem `Correct.lean` routes selector 32 to. -/
theorem cometWithExtendedAssetListQuoteCollateralBody {σ σ₀ A I} {g : UInt256} (v : CometWithExtendedAssetListImmutables)
    (hcode : I.code = deployedRuntime v) (hsize : I.calldata.size < UInt256.size)
    (hsel : selIs I (cometWithExtendedAssetListSelBytes 32)) :
    runtimeRefinementFor config contract σ σ₀ g A I (immStore v) := by
  have hsz : 4 ≤ I.calldata.size := calldata_size_ge_of_selIs I (cometWithExtendedAssetListSelBytes 32) rfl hsel
  have hd : selectorDispatchMsg contract I.calldata = some quoteCollateralTransition :=
    cometSelectorDispatch ⟨32, by decide⟩ hsel
  have hdecode : decodeCalldataWithMode config.abiDecodeMode
      (quoteCollateralTransition.params.map Param.name)
      (transitionSignature quoteCollateralTransition).paramTypes I.calldata =
      decodeCalldata ["asset", "baseAmount"] [.elem .address, abiUInt256] I.calldata := by
    exact solc0815_decodeCalldata_scalar_eq (by decide)
  have hX := quoteCollateralX (σ := σ) (σ₀ := σ₀) (A := A)
    (g := Sat256.ofUInt256 g) v hcode hsz hsize hsel
  by_cases hlo : 68 ≤ I.calldata.size
  · by_cases hhi : I.calldata.size < 2^255 + 4
    · by_cases hc : (calldataWord I.calldata 4).toNat < EVM.addressModulus
      · have hdec := hdecode.trans (decodeCalldata_addr_uint256_ok hlo hhi hc)
        by_cases hv : I.weiValue = ⟨0⟩
        · unfold QuoteCollateralResult at hX
          rw [if_pos ⟨hv, hlo, hhi, hc⟩] at hX
          obtain ⟨result, hsearch, hr⟩ := hX
          cases result with
          | none =>
              exact selectorRevert_refines hcode hr hd hdec
                (quoteCollateral_source v hv hhi hsearch)
          | some result =>
              obtain ⟨evm', value⟩ := result
              obtain ⟨frame, hbody⟩ := quoteCollateral_source v hv hhi hsearch
              exact selectorStateReturn_refines hcode hr hd hdec hbody rfl
                (returnEquiv_of_encode (uint256ReturnEncoding value))
        · simp only [QuoteCollateralResult, hv, false_and, if_false] at hX
          apply selectorRevert_refines hcode hX hd hdec
          rw [quoteCollateralTransition_body]
          exact calldataPrologue_nonpayable hv
      · simp only [QuoteCollateralResult, hc, and_false, if_false] at hX
        exact selectorDecodeFailure_refines hcode hX hd
          (hdecode.trans (decodeCalldata_addr_uint256_none_noncanon hlo hhi hc))
    · simp only [QuoteCollateralResult, hhi, false_and, and_false, if_false] at hX
      exact selectorDecodeFailure_refines hcode hX hd
        (hdecode.trans (decodeCalldata_addr_uint256_none_huge (by omega)))
  · simp only [QuoteCollateralResult, hlo, false_and, and_false, if_false] at hX
    exact selectorDecodeFailure_refines hcode hX hd
      (hdecode.trans (decodeCalldata_addr_uint256_none_short hsz (by omega)))


end Benchmarks.CompoundIII.Comet
