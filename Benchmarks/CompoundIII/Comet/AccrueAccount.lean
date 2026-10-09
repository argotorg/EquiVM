import Benchmarks.CompoundIII.Comet.Dispatch
import Benchmarks.CompoundIII.Comet.AccrueAccountEvm
import Benchmarks.CompoundIII.Comet.AccrueAccountSource

/-!
# CometWithExtendedAssetList `accrueAccount(address)`

Per-function proof: calldata decode facts, the EVM trace from the dispatcher arm through the
body, the Solm body evaluation, and the `…Body` theorem `Correct.lean` consumes.
Dispatcher arm entry: pc 925; reach lemma `cometWithExtendedAssetListReachAccrueAccountBody`.
-/

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables
open Benchmarks.CompoundIII.Comet.Immutables

namespace Benchmarks.CompoundIII.Comet

set_option maxRecDepth 2000

/-- `accrueAccount(address)`: the theorem `Correct.lean` routes selector 52 to. -/
theorem cometWithExtendedAssetListAccrueAccountBody {σ σ₀ A I} {g : UInt256} (v : CometWithExtendedAssetListImmutables)
    (hcode : I.code = deployedRuntime v) (hsize : I.calldata.size < UInt256.size)
    (hsel : selIs I (cometWithExtendedAssetListSelBytes 52)) :
    runtimeRefinementFor config contract σ σ₀ g A I (immStore v) := by
  have hsz : 4 ≤ I.calldata.size := calldata_size_ge_of_selIs I (cometWithExtendedAssetListSelBytes 52) rfl hsel
  have hd : selectorDispatchMsg contract I.calldata = some accrueAccountTransition :=
    cometSelectorDispatch ⟨52, by decide⟩ hsel
  have hdecode : decodeCalldataWithMode config.abiDecodeMode
      (accrueAccountTransition.params.map Param.name)
      (transitionSignature accrueAccountTransition).paramTypes I.calldata =
      decodeCalldata ["account"] [.elem .address] I.calldata := rfl
  have hX := accrueAccountX (σ := σ) (σ₀ := σ₀) (A := A)
    (g := Sat256.ofUInt256 g) v hcode hsz hsize hsel
  by_cases hlo : 36 ≤ I.calldata.size
  · by_cases hhi : I.calldata.size < 2^255 + 4
    · by_cases hc : (calldataWord I.calldata 4).toNat < EVM.addressModulus
      · have hdec := hdecode.trans (decodeCalldata_address_ok hlo hhi hc)
        by_cases hv : I.weiValue = ⟨0⟩
        · unfold AccrueAccountResult at hX
          rw [if_pos ⟨hv, hlo, hhi, hc⟩] at hX
          have hb := accrueAccount_source v (initState σ σ₀ (Sat256.ofUInt256 g) A I)
            (AccountAddress.ofNat (calldataWord I.calldata 4).toNat) hv hhi
          cases hr : accrueAccountOutcome v (initState σ σ₀ (Sat256.ofUInt256 g) A I)
              (AccountAddress.ofNat (calldataWord I.calldata 4).toNat) with
          | ok evm' =>
              rw [hr] at hX hb
              obtain ⟨frame, hb⟩ := hb
              exact selectorStateReturn_refines hcode hX hd hdec hb rfl voidReturnEquiv
          | reverted =>
              rw [hr] at hX hb
              exact selectorRevert_refines hcode hX hd hdec hb
          | staticViolation =>
              rw [hr] at hX hb
              exact selectorStatic_refines hcode hX hd hdec hb
        · simp only [AccrueAccountResult, hv, false_and, if_false] at hX
          apply selectorRevert_refines hcode hX hd hdec
          rw [accrueAccountTransition_body]
          exact calldataPrologue_nonpayable hv
      · simp only [AccrueAccountResult, hc, and_false, if_false] at hX
        exact selectorDecodeFailure_refines hcode hX hd
          (hdecode.trans (decodeCalldata_address_none_noncanon hlo hhi hc))
    · simp only [AccrueAccountResult, hhi, false_and, and_false, if_false] at hX
      exact selectorDecodeFailure_refines hcode hX hd
        (hdecode.trans (decodeCalldata_address_none_huge (by omega)))
  · simp only [AccrueAccountResult, hlo, false_and, and_false, if_false] at hX
    exact selectorDecodeFailure_refines hcode hX hd
      (hdecode.trans (decodeCalldata_address_none_short hsz (by omega)))

end Benchmarks.CompoundIII.Comet
