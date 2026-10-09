import Benchmarks.CompoundIII.Comet.Dispatch
import Benchmarks.CompoundIII.Comet.BuyCollateralEvm
import Benchmarks.CompoundIII.Comet.BuyCollateralSource

/-!
# CometWithExtendedAssetList `buyCollateral(address,uint256,uint256,address)`

Per-function proof: calldata decode facts, the EVM trace from the dispatcher arm through the
body, the Solm body evaluation, and the `…Body` theorem `Correct.lean` consumes.
Dispatcher arm entry: pc 808; reach lemma `cometWithExtendedAssetListReachBuyCollateralBody`.
-/

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables
open Benchmarks.CompoundIII.Comet.Immutables

namespace Benchmarks.CompoundIII.Comet

set_option maxRecDepth 2000

/-- `buyCollateral(address,uint256,uint256,address)`: the theorem `Correct.lean` routes selector 64 to. -/
theorem cometWithExtendedAssetListBuyCollateralBody {σ σ₀ A I} {g : UInt256} (v : CometWithExtendedAssetListImmutables)
    (hcode : I.code = deployedRuntime v) (hsize : I.calldata.size < UInt256.size)
    (hsel : selIs I (cometWithExtendedAssetListSelBytes 64)) :
    runtimeRefinementFor config contract σ σ₀ g A I (immStore v) := by
  have hsz : 4 ≤ I.calldata.size := calldata_size_ge_of_selIs I (cometWithExtendedAssetListSelBytes 64) rfl hsel
  have hd : selectorDispatchMsg contract I.calldata = some buyCollateralTransition :=
    cometSelectorDispatch ⟨64, by decide⟩ hsel
  have hdecode : decodeCalldataWithMode config.abiDecodeMode
      (buyCollateralTransition.params.map Param.name)
      (transitionSignature buyCollateralTransition).paramTypes I.calldata =
      decodeCalldata ["asset", "minAmount", "baseAmount", "recipient"]
        [.elem .address, abiUInt256, abiUInt256, .elem .address] I.calldata := by
    exact solc0815_decodeCalldata_scalar_eq (by decide)
  have hdec := hdecode.trans
    (decodeCalldata_addressUintUintAddress I "asset" "minAmount" "baseAmount" "recipient" hsz)
  have hX := buyCollateralX (σ := σ) (σ₀ := σ₀) (A := A)
    (g := Sat256.ofUInt256 g) v hcode hsz hsize hsel
  by_cases hargs : BuyCollateralCalldataValid I
  · rw [if_pos hargs] at hdec
    by_cases hv : I.weiValue = ⟨0⟩
    · unfold BuyCollateralResult at hX
      rw [if_pos ⟨hv, hargs⟩] at hX
      obtain ⟨result, ht, hr⟩ := hX
      have hb := buyCollateralPublic_source ht hv hargs.2.1
      cases result with
      | reverted => exact selectorRevert_refines hcode hr hd hdec hb
      | staticViolation => exact selectorStatic_refines hcode hr hd hdec hb
      | ok evm' =>
        obtain ⟨frame, hb⟩ := hb
        exact selectorStateReturn_refines hcode hr hd hdec hb rfl voidReturnEquiv
    · simp only [BuyCollateralResult, hv, false_and, if_false] at hX
      apply selectorRevert_refines hcode hX hd hdec
      rw [buyCollateralTransition_body]
      exact calldataPrologue_nonpayable hv
  · simp only [BuyCollateralResult, hargs, and_false, if_false] at hX
    rw [if_neg hargs] at hdec
    exact selectorDecodeFailure_refines hcode hX hd hdec

end Benchmarks.CompoundIII.Comet
