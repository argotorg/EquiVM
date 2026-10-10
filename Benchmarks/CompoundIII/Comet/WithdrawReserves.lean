import Benchmarks.CompoundIII.Comet.Dispatch
import Benchmarks.CompoundIII.Comet.WithdrawReservesEvm
import Benchmarks.CompoundIII.Comet.WithdrawReservesSource

/-!
# CometWithExtendedAssetList `withdrawReserves(address,uint256)`

Per-function proof: calldata decode facts, the EVM trace from the dispatcher arm through the
body, the Solm body evaluation, and the `…Body` theorem `Correct.lean` consumes.
Dispatcher arm entry: pc 817; reach lemma `cometWithExtendedAssetListReachWithdrawReservesBody`.
-/

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables
open Benchmarks.CompoundIII.Comet.Immutables

namespace Benchmarks.CompoundIII.Comet

set_option maxRecDepth 2000

/-- `withdrawReserves(address,uint256)`: the theorem `Correct.lean` routes selector 63 to. -/
theorem cometWithExtendedAssetListWithdrawReservesBody {σ σ₀ A I} {g : UInt256} (v : CometWithExtendedAssetListImmutables)
    (hcode : I.code = deployedRuntime v) (hsize : I.calldata.size < UInt256.size)
    (hsel : selIs I (cometWithExtendedAssetListSelBytes 63)) :
    runtimeRefinementFor config contract σ σ₀ g A I (immStore v) := by
  have hsz : 4 ≤ I.calldata.size := calldata_size_ge_of_selIs I (cometWithExtendedAssetListSelBytes 63) rfl hsel
  have hd : selectorDispatchMsg contract I.calldata = some withdrawReservesTransition :=
    cometSelectorDispatch ⟨63, by decide⟩ hsel
  have hdecode : decodeCalldataWithMode config.abiDecodeMode
      (withdrawReservesTransition.params.map Param.name)
      (transitionSignature withdrawReservesTransition).paramTypes I.calldata =
      decodeCalldata ["to", "amount"] [.elem .address, abiUInt256] I.calldata := by
    exact solc0815_decodeCalldata_scalar_eq (by decide)
  have hX := withdrawReservesX (σ := σ) (σ₀ := σ₀) (A := A)
    (g := Sat256.ofUInt256 g) v hcode hsz hsize hsel
  by_cases hlo : 68 ≤ I.calldata.size
  · by_cases hhi : I.calldata.size < 2^255 + 4
    · by_cases hc : (calldataWord I.calldata 4).toNat < EVM.addressModulus
      · have hdec := hdecode.trans (decodeCalldata_addr_uint256_ok hlo hhi hc)
        by_cases hv : I.weiValue = ⟨0⟩
        · unfold WithdrawReservesResult at hX
          rw [if_pos ⟨hv, hlo, hhi, hc⟩] at hX
          obtain ⟨result, hsearch, hr⟩ := hX
          have hb := withdrawReserves_source hsearch hv hhi
          cases result with
          | none => exact selectorRevert_refines hcode hr hd hdec hb
          | some evm' =>
              simp only [WithdrawReservesSourceResult] at hb
              simp only [WithdrawReservesRun] at hr
              by_cases hp : evm'.executionEnv.perm = true
              · rw [if_pos hp] at hb hr
                obtain ⟨frame, hbody⟩ := hb
                exact selectorStateReturn_refines hcode hr hd hdec hbody rfl voidReturnEquiv
              · rw [if_neg hp] at hb hr
                exact selectorStatic_refines hcode hr hd hdec hb
        · simp only [WithdrawReservesResult, hv, false_and, if_false] at hX
          apply selectorRevert_refines hcode hX hd hdec
          rw [withdrawReservesTransition_body]
          exact calldataPrologue_nonpayable hv
      · simp only [WithdrawReservesResult, hc, and_false, if_false] at hX
        exact selectorDecodeFailure_refines hcode hX hd
          (hdecode.trans (decodeCalldata_addr_uint256_none_noncanon hlo hhi hc))
    · simp only [WithdrawReservesResult, hhi, false_and, and_false, if_false] at hX
      exact selectorDecodeFailure_refines hcode hX hd
        (hdecode.trans (decodeCalldata_addr_uint256_none_huge (by omega)))
  · simp only [WithdrawReservesResult, hlo, false_and, and_false, if_false] at hX
    exact selectorDecodeFailure_refines hcode hX hd
      (hdecode.trans (decodeCalldata_addr_uint256_none_short hsz (by omega)))

end Benchmarks.CompoundIII.Comet
