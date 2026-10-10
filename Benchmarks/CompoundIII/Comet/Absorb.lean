import Benchmarks.CompoundIII.Comet.Dispatch
import Benchmarks.CompoundIII.Comet.GasBound
import Benchmarks.CompoundIII.Comet.AbsorbEvm
import Benchmarks.CompoundIII.Comet.AbsorbSource

/-!
# CometWithExtendedAssetList `absorb(address,address[])`

Per-function proof: calldata decode facts, the EVM trace from the dispatcher arm through the
body, the Solm body evaluation, and the `…Body` theorem `Correct.lean` consumes.
Dispatcher arm entry: pc 898; reach lemma `cometWithExtendedAssetListReachAbsorbBody`.
-/

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables
open Benchmarks.CompoundIII.Comet.Immutables

namespace Benchmarks.CompoundIII.Comet

set_option maxRecDepth 2000

/-- `absorb(address,address[])`: the theorem `Correct.lean` routes selector 38 to. -/
theorem cometWithExtendedAssetListAbsorbBody {σ σ₀ A I} {g : UInt256} (v : CometWithExtendedAssetListImmutables)
    (hcode : I.code = deployedRuntime v) (hsize : I.calldata.size < UInt256.size)
    (hsel : selIs I (cometWithExtendedAssetListSelBytes 38)) (hgas : cometGasBound g) :
    runtimeRefinementFor config contract σ σ₀ g A I (immStore v) := by
  have hsz : 4 ≤ I.calldata.size := calldata_size_ge_of_selIs I (cometWithExtendedAssetListSelBytes 38) rfl hsel
  have hd : selectorDispatchMsg contract I.calldata = some absorbTransition :=
    cometSelectorDispatch ⟨38, by decide⟩ hsel
  have hdecode : decodeCalldataWithMode config.abiDecodeMode
      (absorbTransition.params.map Param.name) (transitionSignature absorbTransition).paramTypes
      I.calldata = decodeCalldataWithMode .solc0815 ["absorber", "accounts"]
        [.elem .address, .dynamicArray (.elem .address)] I.calldata := rfl
  have hX := absorbX (σ := σ) (σ₀ := σ₀) (A := A) (g := Sat256.ofUInt256 g)
    v hcode hsz hsize hsel hgas
  by_cases hargs : AbsorbCalldataValid I.calldata
  · obtain ⟨accounts, endOffset, hread, hlen, hdec⟩ := absorbCalldata_decode_valid hargs
    have hdec := hdecode.trans hdec
    by_cases hv : I.weiValue = ⟨0⟩
    · unfold AbsorbResult at hX
      rw [if_pos ⟨hv, hargs⟩] at hX
      obtain hoog | ⟨result, ht, hr⟩ := hX
      · exact reEquiv_outOfGas (Xi_error_of_X (g := g) (by rw [← hcode] at hoog; exact hoog))
      have hn : absorbArrayLength I.calldata < 2^64 := by
        have hh := hargs.2.2.2.2.2.1
        change absorbArrayLength I.calldata ≤ 2^64 - 1 at hh
        omega
      have hb := absorbPublic_source ht hread hlen hn hv (by
        change I.calldata.size < 2^255 + 4
        have hh := hargs.2.1
        omega)
      cases result with
      | reverted => exact selectorRevert_refines hcode hr hd hdec hb
      | staticViolation => exact selectorStatic_refines hcode hr hd hdec hb
      | ok evm' =>
        obtain ⟨frame, hb⟩ := hb
        exact selectorStateReturn_refines hcode hr hd hdec hb rfl voidReturnEquiv
    · simp only [AbsorbResult, hv, false_and, if_false] at hX
      apply selectorRevert_refines hcode hX hd hdec
      rw [absorbTransition_body]
      exact calldataPrologue_nonpayable hv
  · simp only [AbsorbResult, hargs, and_false, if_false] at hX
    have hdec := hdecode.trans (absorbCalldata_decode_invalid hargs)
    exact selectorDecodeFailure_refines hcode hX hd hdec

end Benchmarks.CompoundIII.Comet
