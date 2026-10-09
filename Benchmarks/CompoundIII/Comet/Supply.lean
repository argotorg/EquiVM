import Benchmarks.CompoundIII.Comet.Dispatch
import Benchmarks.CompoundIII.Comet.SupplyEvm
import Benchmarks.CompoundIII.Comet.SupplySource

/-!
# CometWithExtendedAssetList `supply(address,uint256)`

Per-function proof: calldata decode facts, the EVM trace from the dispatcher arm through the
body, the Solm body evaluation, and the `…Body` theorem `Correct.lean` consumes.
Dispatcher arm entry: pc 790; reach lemma `cometWithExtendedAssetListReachSupplyBody`.
-/

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables
open Benchmarks.CompoundIII.Comet.Immutables

namespace Benchmarks.CompoundIII.Comet

set_option maxRecDepth 2000

/-- `supply(address,uint256)`: the theorem `Correct.lean` routes selector 66 to. -/
theorem cometWithExtendedAssetListSupplyBody {σ σ₀ A I} {g : UInt256} (v : CometWithExtendedAssetListImmutables)
    (hcode : I.code = deployedRuntime v) (hsize : I.calldata.size < UInt256.size)
    (hsel : selIs I (cometWithExtendedAssetListSelBytes 66)) :
    runtimeRefinementFor config contract σ σ₀ g A I (immStore v) := by
  have hsz : 4 ≤ I.calldata.size := calldata_size_ge_of_selIs I (cometWithExtendedAssetListSelBytes 66) rfl hsel
  have hd : selectorDispatchMsg contract I.calldata = some supplyTransition :=
    cometSelectorDispatch ⟨66, by decide⟩ hsel
  have hdecode : decodeCalldataWithMode config.abiDecodeMode
      (supplyTransition.params.map Param.name)
      (transitionSignature supplyTransition).paramTypes I.calldata =
      decodeCalldata ["asset", "amount"] [.elem .address, abiUInt256] I.calldata := rfl
  have hX := supplyX (σ := σ) (σ₀ := σ₀) (A := A)
    (g := Sat256.ofUInt256 g) v hcode hsz hsize hsel
  by_cases hlo : 68 ≤ I.calldata.size
  · by_cases hhi : I.calldata.size < 2^255 + 4
    · by_cases hc : (calldataWord I.calldata 4).toNat < EVM.addressModulus
      · have hdec := hdecode.trans (decodeCalldata_addr_uint256_ok hlo hhi hc)
        by_cases hv : I.weiValue = ⟨0⟩
        · unfold SupplyResult at hX
          rw [if_pos ⟨hv, hlo, hhi, hc⟩] at hX
          obtain ⟨result, hsearch, hr⟩ := hX
          have hb := supply_source (evm := initState σ σ₀ (Sat256.ofUInt256 g) A I)
            hsearch hv hhi
          cases result with
          | reverted => exact selectorRevert_refines hcode hr hd hdec hb
          | staticViolation => exact selectorStatic_refines hcode hr hd hdec hb
          | ok evm' =>
              obtain ⟨frame, hb⟩ := hb
              exact selectorStateReturn_refines hcode hr hd hdec hb rfl explicitVoidReturnEquiv
        · simp only [SupplyResult, hv, false_and, if_false] at hX
          apply selectorRevert_refines hcode hX hd hdec
          rw [supplyTransition_body]
          exact calldataPrologue_nonpayable hv
      · simp only [SupplyResult, hc, and_false, if_false] at hX
        exact selectorDecodeFailure_refines hcode hX hd
          (hdecode.trans (decodeCalldata_addr_uint256_none_noncanon hlo hhi hc))
    · simp only [SupplyResult, hhi, false_and, and_false, if_false] at hX
      exact selectorDecodeFailure_refines hcode hX hd
        (hdecode.trans (decodeCalldata_addr_uint256_none_huge (by omega)))
  · simp only [SupplyResult, hlo, false_and, and_false, if_false] at hX
    exact selectorDecodeFailure_refines hcode hX hd
      (hdecode.trans (decodeCalldata_addr_uint256_none_short hsz (by omega)))

end Benchmarks.CompoundIII.Comet
