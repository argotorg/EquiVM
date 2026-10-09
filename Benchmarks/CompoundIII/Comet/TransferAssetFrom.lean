import Benchmarks.CompoundIII.Comet.Dispatch
import Benchmarks.CompoundIII.Comet.TransferAssetFromEvm
import Benchmarks.CompoundIII.Comet.TransferAssetFromSource

/-!
# CometWithExtendedAssetList `transferAssetFrom(address,address,address,uint256)`

Per-function proof: calldata decode facts, the EVM trace from the dispatcher arm through the
body, the Solm body evaluation, and the `…Body` theorem `Correct.lean` consumes.
Dispatcher arm entry: pc 916; reach lemma `cometWithExtendedAssetListReachTransferAssetFromBody`.
-/

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables
open Benchmarks.CompoundIII.Comet.Immutables

namespace Benchmarks.CompoundIII.Comet

set_option maxRecDepth 2000

/-- `transferAssetFrom(address,address,address,uint256)`: the theorem `Correct.lean` routes selector 53 to. -/
theorem cometWithExtendedAssetListTransferAssetFromBody {σ σ₀ A I} {g : UInt256} (v : CometWithExtendedAssetListImmutables)
    (hcode : I.code = deployedRuntime v) (hsize : I.calldata.size < UInt256.size)
    (hsel : selIs I (cometWithExtendedAssetListSelBytes 53)) :
    runtimeRefinementFor config contract σ σ₀ g A I (immStore v) := by
  have hsz : 4 ≤ I.calldata.size := calldata_size_ge_of_selIs I (cometWithExtendedAssetListSelBytes 53) rfl hsel
  have hd : selectorDispatchMsg contract I.calldata = some transferAssetFromTransition :=
    cometSelectorDispatch ⟨53, by decide⟩ hsel
  have hdecode : decodeCalldataWithMode config.abiDecodeMode
      (transferAssetFromTransition.params.map Param.name)
      (transitionSignature transferAssetFromTransition).paramTypes I.calldata =
      decodeCalldata ["src", "dst", "asset", "amount"]
        [.elem .address, .elem .address, .elem .address, abiUInt256] I.calldata := rfl
  have hdec := hdecode.trans (decodeCalldata_threeAddressUint I "src" "dst" "asset" "amount" hsz)
  have hX := transferAssetFromX (σ := σ) (σ₀ := σ₀) (A := A)
    (g := Sat256.ofUInt256 g) v hcode hsz hsize hsel
  by_cases hargs : ThreeAddressUintCalldataValid I
  · rw [if_pos hargs] at hdec
    by_cases hv : I.weiValue = ⟨0⟩
    · unfold TransferAssetFromResult at hX
      rw [if_pos ⟨hv, hargs⟩] at hX
      obtain ⟨result, ht, hr⟩ := hX
      have hb := transferAssetFrom_source (evm := initState σ σ₀ (Sat256.ofUInt256 g) A I) ht hv hargs.2.1
      cases result with
      | reverted => exact selectorRevert_refines hcode hr hd hdec hb
      | staticViolation => exact selectorStatic_refines hcode hr hd hdec hb
      | ok evm' =>
          obtain ⟨frame, hb⟩ := hb
          exact selectorStateReturn_refines hcode hr hd hdec hb rfl explicitVoidReturnEquiv
    · simp only [TransferAssetFromResult, hv, false_and, if_false] at hX
      apply selectorRevert_refines hcode hX hd hdec
      rw [transferAssetFromTransition_body]
      exact calldataPrologue_nonpayable hv
  · simp only [TransferAssetFromResult, hargs, and_false, if_false] at hX
    rw [if_neg hargs] at hdec
    exact selectorDecodeFailure_refines hcode hX hd hdec

end Benchmarks.CompoundIII.Comet
