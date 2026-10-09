import Benchmarks.CompoundIII.Comet.IsLiquidatableEvm

/-!
# CometWithExtendedAssetList `isLiquidatable(address)`

Per-function proof: calldata decode facts, the EVM trace from the dispatcher arm through the
body, the Solm body evaluation, and the `…Body` theorem `Correct.lean` consumes.
Dispatcher arm entry: pc 1384; reach lemma `cometWithExtendedAssetListReachIsLiquidatableBody`.
-/

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables
open Benchmarks.CompoundIII.Comet.Immutables

namespace Benchmarks.CompoundIII.Comet

set_option maxRecDepth 2000

/-- `isLiquidatable(address)`: the theorem `Correct.lean` routes selector 0 to. -/
theorem cometWithExtendedAssetListIsLiquidatableBody {σ σ₀ A I} {g : UInt256} (v : CometWithExtendedAssetListImmutables)
    (hcode : I.code = deployedRuntime v) (hsize : I.calldata.size < UInt256.size)
    (hsel : selIs I (cometWithExtendedAssetListSelBytes 0)) :
    runtimeRefinementFor config contract σ σ₀ g A I (immStore v) := by
  have hsz : 4 ≤ I.calldata.size := calldata_size_ge_of_selIs I (cometWithExtendedAssetListSelBytes 0) rfl hsel
  have hbodyEq : isLiquidatableTransition.body = collateralCheckPublicBody false := rfl
  have hd : selectorDispatchMsg contract I.calldata = some isLiquidatableTransition :=
    cometSelectorDispatch ⟨0, by decide⟩ hsel
  have hdecode : decodeCalldataWithMode config.abiDecodeMode
      (isLiquidatableTransition.params.map Param.name)
      (transitionSignature isLiquidatableTransition).paramTypes I.calldata =
      decodeCalldata ["account"] [.elem .address] I.calldata := rfl
  have hX := isLiquidatableX (σ := σ) (σ₀ := σ₀) (A := A)
    (g := Sat256.ofUInt256 g) v hcode hsz hsize hsel
  by_cases hlo : 36 ≤ I.calldata.size
  · by_cases hhi : I.calldata.size < 2^255 + 4
    · by_cases hc : (calldataWord I.calldata 4).toNat < EVM.addressModulus
      · have hdec := hdecode.trans (decodeCalldata_address_ok hlo hhi hc)
        by_cases hv : I.weiValue = ⟨0⟩
        · unfold CollateralCheckPublicResult at hX
          rw [if_pos ⟨hv, hlo, hhi, hc⟩] at hX
          obtain ⟨result, ht, hr⟩ := hX
          cases result with
          | none =>
              exact selectorRevert_refines hcode hr hd hdec
                (by rw [hbodyEq]; exact collateralCheckPublic_reverts hv hhi ht)
          | some result =>
              obtain ⟨evm', value⟩ := result
              obtain ⟨frame, hbody⟩ := collateralCheckPublic_returns hv hhi ht
              rw [← hbodyEq] at hbody
              exact selectorStateReturn_refines hcode hr hd hdec hbody rfl
                (returnEquiv_of_encode (boolWordEncoding value))
        · simp only [CollateralCheckPublicResult, hv, false_and, if_false] at hX
          apply selectorRevert_refines hcode hX hd hdec
          rw [hbodyEq]
          exact calldataPrologue_nonpayable hv
      · simp only [CollateralCheckPublicResult, hc, and_false, if_false] at hX
        exact selectorDecodeFailure_refines hcode hX hd
          (hdecode.trans (decodeCalldata_address_none_noncanon hlo hhi hc))
    · simp only [CollateralCheckPublicResult, hhi, false_and, and_false, if_false] at hX
      exact selectorDecodeFailure_refines hcode hX hd
        (hdecode.trans (decodeCalldata_address_none_huge (by omega)))
  · simp only [CollateralCheckPublicResult, hlo, false_and, and_false, if_false] at hX
    exact selectorDecodeFailure_refines hcode hX hd
      (hdecode.trans (decodeCalldata_address_none_short hsz (by omega)))


end Benchmarks.CompoundIII.Comet
