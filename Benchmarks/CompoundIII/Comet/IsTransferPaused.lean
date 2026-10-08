import Benchmarks.CompoundIII.Comet.Dispatch
import Benchmarks.CompoundIII.Comet.PauseCommon
import Benchmarks.CompoundIII.Comet.RuntimeBlocks_009
import Benchmarks.CompoundIII.Comet.RuntimeBlocks_026

/-!
# CometWithExtendedAssetList `isTransferPaused()`

Per-function proof: calldata decode facts, the EVM trace from the dispatcher arm through the
body, the Solm body evaluation, and the `…Body` theorem `Correct.lean` consumes.
Dispatcher arm entry: pc 979; reach lemma `cometWithExtendedAssetListReachIsTransferPausedBody`.
-/

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables
open Benchmarks.CompoundIII.Comet.Immutables
open cometWithExtendedAssetListBlocks

namespace Benchmarks.CompoundIII.Comet

set_option maxRecDepth 2000000

theorem isTransferPausedX {σ σ₀ A I} {g : Sat256} (v : CometWithExtendedAssetListImmutables)
    (hcode : I.code = deployedRuntime v) (hsz : 4 ≤ I.calldata.size)
    (hsize : I.calldata.size < UInt256.size)
    (hsel : selIs I (cometWithExtendedAssetListSelBytes 46)) :
    GetterResult (deployedRuntime v) I g (initState σ σ₀ g A I) σ
      (pauseReturnWord σ I ⟨1, by decide⟩).toByteArray := by
  obtain ⟨k, C, rd⟩ := cometWithExtendedAssetListReachIsTransferPausedBody
    (σ := σ) (σ₀ := σ₀) (A := A) (g := g) v hcode hsz hsize hsel
  have rd1 := cometWithExtendedAssetList_block_979 (immWords := wordsOf (immStore v))
    (by decide) (by rw [cometWithExtendedAssetListPatchedValidJumpsRuntime v]; jump_dest) rd
  by_cases hvalue : I.weiValue = ⟨0⟩
  · have rd2 := cometWithExtendedAssetList_block_4799_fallthrough
      (immWords := wordsOf (immStore v)) (by decide) hvalue rd1
    by_cases hhi : I.calldata.size < 2 ^ 255 + 4
    · simp only [GetterResult, hvalue, hhi, and_self, if_true]
      have rd3 := cometWithExtendedAssetList_block_4806_fallthrough
        (immWords := wordsOf (immStore v)) (by decide) (getterLength_ok hsz hhi hsize) rd2
      have rd4 := cometWithExtendedAssetList_block_4818
        (immWords := wordsOf (immStore v)) (by decide) rd3
      exact (getterReturnData (pauseReturnWord σ I ⟨1, by decide⟩)) ▸ rd4
    · simp only [GetterResult, hvalue, hhi, and_false, if_false]
      have rd3 := cometWithExtendedAssetList_block_4806_taken
        (immWords := wordsOf (immStore v)) (by decide) (getterLength_huge (by omega) hsize)
        (by rw [cometWithExtendedAssetListPatchedValidJumpsRuntime v]; jump_dest) rd2
      exact cometRevert1410 (by decide) rd3
  · simp only [GetterResult, hvalue, false_and, if_false]
    have rd2 := cometWithExtendedAssetList_block_4799_taken
      (immWords := wordsOf (immStore v)) (by decide) hvalue
      (by rw [cometWithExtendedAssetListPatchedValidJumpsRuntime v]; jump_dest) rd1
    exact cometRevert1410 (by decide) rd2

/-- `isTransferPaused()`: the theorem `Correct.lean` routes selector 46 to. -/
theorem cometWithExtendedAssetListIsTransferPausedBody {σ σ₀ A I} {g : UInt256} (v : CometWithExtendedAssetListImmutables)
    (hcode : I.code = deployedRuntime v) (hsize : I.calldata.size < UInt256.size)
    (hsel : selIs I (cometWithExtendedAssetListSelBytes 46)) :
    runtimeRefinementFor config contract σ σ₀ g A I (immStore v) := by
  have hsz : 4 ≤ I.calldata.size := calldata_size_ge_of_selIs I (cometWithExtendedAssetListSelBytes 46) rfl hsel
  exact pauseGetter_refines (t := isTransferPausedTransition) ⟨1, by decide⟩ hcode hsz
    (cometSelectorDispatch ⟨46, by decide⟩ hsel) rfl rfl rfl
    (isTransferPausedX v hcode hsz hsize hsel)

end Benchmarks.CompoundIII.Comet
