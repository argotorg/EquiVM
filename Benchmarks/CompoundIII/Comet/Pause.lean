import Benchmarks.CompoundIII.Comet.Dispatch
import Benchmarks.CompoundIII.Comet.PauseEvm

/-!
# CometWithExtendedAssetList `pause(bool,bool,bool,bool,bool)`

Per-function proof: calldata decode facts, the EVM trace from the dispatcher arm through the
body, the Solm body evaluation, and the `…Body` theorem `Correct.lean` consumes.
Dispatcher arm entry: pc 1159; reach lemma `cometWithExtendedAssetListReachPauseBody`.
-/

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables
open Benchmarks.CompoundIII.Comet.Immutables

namespace Benchmarks.CompoundIII.Comet

set_option maxRecDepth 10000

/-- `pause(bool,bool,bool,bool,bool)`: the theorem `Correct.lean` routes selector 25 to. -/
theorem cometWithExtendedAssetListPauseBody {σ σ₀ A I} {g : UInt256} (v : CometWithExtendedAssetListImmutables)
    (hcode : I.code = deployedRuntime v) (hsize : I.calldata.size < UInt256.size)
    (hsel : selIs I (cometWithExtendedAssetListSelBytes 25)) :
    runtimeRefinementFor config contract σ σ₀ g A I (immStore v) := by
  have hsz : 4 ≤ I.calldata.size := calldata_size_ge_of_selIs I (cometWithExtendedAssetListSelBytes 25) rfl hsel
  have hd : selectorDispatchMsg contract I.calldata = some pauseTransition :=
    cometSelectorDispatch ⟨25, by decide⟩ hsel
  have hX := pauseX (σ := σ) (σ₀ := σ₀) (A := A)
    (g := Sat256.ofUInt256 g) v hcode hsz hsize hsel
  by_cases hlo : 164 ≤ I.calldata.size
  · by_cases hhi : I.calldata.size < 2^255 + 4
    · have hdec := pauseDecode_result hlo hhi
      by_cases hc : PauseCanonical I.calldata
      · rw [if_pos hc] at hdec
        by_cases hv : I.weiValue = ⟨0⟩
        · by_cases ha : PauseAuthorized v I
          · unfold PauseResult at hX
            rw [if_pos ⟨hv, hlo, hhi, hc, ha⟩] at hX
            by_cases hp : I.perm = true
            · rw [if_pos hp] at hX
              exact selectorStateReturn_refines hcode hX hd hdec
                (pause_returns _ v (pauseInputs I.calldata) hv hhi ha)
                (pauseSourceState_accountMap _).symm voidReturnEquiv
            · rw [if_neg hp] at hX
              exact selectorStatic_refines hcode hX hd hdec
                (pause_static _ v (pauseInputs I.calldata) hv hhi ha (Bool.eq_false_iff.mpr hp))
          · simp only [PauseResult, ha, and_false, if_false] at hX
            exact selectorRevert_refines hcode hX hd hdec
              (pause_reverts _ v (pauseInputs I.calldata) hv hhi ha)
        · simp only [PauseResult, hv, false_and, if_false] at hX
          apply selectorRevert_refines hcode hX hd hdec
          rw [pause_body]
          exact calldataPrologue_nonpayable hv
      · simp only [PauseResult, hc, false_and, and_false, if_false] at hX
        rw [if_neg hc] at hdec
        exact selectorDecodeFailure_refines hcode hX hd hdec
    · simp only [PauseResult, hhi, false_and, and_false, if_false] at hX
      exact selectorDecodeFailure_refines hcode hX hd (pauseDecode_huge (by omega))
  · simp only [PauseResult, hlo, false_and, and_false, if_false] at hX
    exact selectorDecodeFailure_refines hcode hX hd (pauseDecode_short (by omega))

end Benchmarks.CompoundIII.Comet
