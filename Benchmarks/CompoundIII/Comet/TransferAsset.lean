import Benchmarks.CompoundIII.Comet.Dispatch
import Benchmarks.CompoundIII.Comet.TransferAssetPublicEvm
import Benchmarks.CompoundIII.Comet.TransferAssetPublicSource

/-!
# CometWithExtendedAssetList `transferAsset(address,address,uint256)`

Per-function proof: calldata decode facts, the EVM trace from the dispatcher arm through the
body, the Solm body evaluation, and the `…Body` theorem `Correct.lean` consumes.
Dispatcher arm entry: pc 1177; reach lemma `cometWithExtendedAssetListReachTransferAssetBody`.
-/

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables
open Benchmarks.CompoundIII.Comet.Immutables

namespace Benchmarks.CompoundIII.Comet

set_option maxRecDepth 2000

/-- `transferAsset(address,address,uint256)`: the theorem `Correct.lean` routes selector 23 to. -/
theorem cometWithExtendedAssetListTransferAssetBody {σ σ₀ A I} {g : UInt256} (v : CometWithExtendedAssetListImmutables)
    (hcode : I.code = deployedRuntime v) (hsize : I.calldata.size < UInt256.size)
    (hsel : selIs I (cometWithExtendedAssetListSelBytes 23)) :
    runtimeRefinementFor config contract σ σ₀ g A I (immStore v) := by
  have hsz : 4 ≤ I.calldata.size := calldata_size_ge_of_selIs I (cometWithExtendedAssetListSelBytes 23) rfl hsel
  have hd : selectorDispatchMsg contract I.calldata = some transferAssetTransition :=
    cometSelectorDispatch ⟨23, by decide⟩ hsel
  have hdecode : decodeCalldataWithMode config.abiDecodeMode
      (transferAssetTransition.params.map Param.name)
      (transitionSignature transferAssetTransition).paramTypes I.calldata =
      decodeCalldata ["dst", "asset", "amount"]
        [.elem .address, .elem .address, abiUInt256] I.calldata := by
    exact solc0815_decodeCalldata_scalar_eq (by decide)
  have hX := transferAssetPublicX (σ := σ) (σ₀ := σ₀) (A := A)
    (g := Sat256.ofUInt256 g) v hcode hsz hsize hsel
  by_cases hargs : TwoAddressUintCalldataValid I
  · have hdec := hdecode.trans (decodeCalldata_address_address_uint256_ok
      hargs.1 hargs.2.1 hargs.2.2.1 hargs.2.2.2)
    by_cases hv : I.weiValue = ⟨0⟩
    · unfold TransferAssetResult at hX
      rw [if_pos ⟨hv, hargs⟩] at hX
      obtain ⟨result, ht, hr⟩ := hX
      have hb := transferAssetPublic_source (evm := initState σ σ₀ (Sat256.ofUInt256 g) A I) ht hv hargs.2.1
      cases result with
      | reverted => exact selectorRevert_refines hcode hr hd hdec hb
      | staticViolation => exact selectorStatic_refines hcode hr hd hdec hb
      | ok evm' =>
          obtain ⟨frame, hb⟩ := hb
          exact selectorStateReturn_refines hcode hr hd hdec hb rfl explicitVoidReturnEquiv
    · simp only [TransferAssetResult, hv, false_and, if_false] at hX
      apply selectorRevert_refines hcode hX hd hdec
      rw [transferAssetTransition_body]
      exact calldataPrologue_nonpayable hv
  · simp only [TransferAssetResult, hargs, and_false, if_false] at hX
    apply selectorDecodeFailure_refines hcode hX hd
    rw [hdecode]
    by_cases hlo : 100 ≤ I.calldata.size
    · by_cases hhi : I.calldata.size < 2^255 + 4
      · by_cases hc : (calldataWord I.calldata 4).toNat < EVM.addressModulus
        · exact decodeCalldata_address_address_uint256_none_noncanon1 hlo hhi hc
            (fun hd ↦ hargs ⟨hlo, hhi, hc, hd⟩)
        · exact decodeCalldata_address_address_uint256_none_noncanon0 hlo hhi hc
      · exact decodeCalldata_address_address_uint256_none_huge (by omega)
    · exact decodeCalldata_address_address_uint256_none_short hsz (by omega)

end Benchmarks.CompoundIII.Comet
