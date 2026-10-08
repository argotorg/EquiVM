import Benchmarks.CompoundIII.Comet.Dispatch
import Benchmarks.CompoundIII.Comet.GetterCommon
import Benchmarks.CompoundIII.Comet.RuntimeBlocks_009
import Benchmarks.CompoundIII.Comet.RuntimeBlocks_027

/-!
# CometWithExtendedAssetList `numAssets()`

Per-function proof: calldata decode facts, the EVM trace from the dispatcher arm through the
body, the Solm body evaluation, and the `…Body` theorem `Correct.lean` consumes.
Dispatcher arm entry: pc 970; reach lemma `cometWithExtendedAssetListReachNumAssetsBody`.
-/

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables
open Benchmarks.CompoundIII.Comet.Immutables
open cometWithExtendedAssetListBlocks

namespace Benchmarks.CompoundIII.Comet

set_option maxRecDepth 2000000

theorem numAssetsX {σ σ₀ A I} {g : Sat256} (v : CometWithExtendedAssetListImmutables)
    (hcode : I.code = deployedRuntime v) (hsz : 4 ≤ I.calldata.size)
    (hsize : I.calldata.size < UInt256.size)
    (hsel : selIs I (cometWithExtendedAssetListSelBytes 47)) :
    GetterResult (deployedRuntime v) I g (initState σ σ₀ g A I) σ
      v.numAssets.toByteArray := by
  obtain ⟨k, C, rd⟩ := cometWithExtendedAssetListReachNumAssetsBody
    (σ := σ) (σ₀ := σ₀) (A := A) (g := g) v hcode hsz hsize hsel
  have rd1 := cometWithExtendedAssetList_block_970 (immWords := wordsOf (immStore v))
    (by decide) (by rw [cometWithExtendedAssetListPatchedValidJumpsRuntime v]; jump_dest) rd
  by_cases hvalue : I.weiValue = ⟨0⟩
  · have rd2 := cometWithExtendedAssetList_block_4838_fallthrough
      (immWords := wordsOf (immStore v)) (by decide) hvalue rd1
    by_cases hhi : I.calldata.size < 2 ^ 255 + 4
    · simp only [GetterResult, hvalue, hhi, and_self, if_true]
      have rd3 := cometWithExtendedAssetList_block_4845_fallthrough
        (immWords := wordsOf (immStore v)) (by decide) (getterLength_ok hsz hhi hsize) rd2
      have rd4 := cometWithExtendedAssetList_block_4857
        (immWords := wordsOf (immStore v)) (by decide) rd3
      rw [wordsOf_immStore_numAssets, wordOfInt_ofNat_toNat_gen, u256_ofNat_toNat] at rd4
      have hclean : UInt256.land v.numAssets (UInt256.ofNat 255) = v.numAssets :=
        lowByteClean v.numAssets_lt
      rw [hclean] at rd4
      exact (getterReturnData v.numAssets) ▸ rd4
    · simp only [GetterResult, hvalue, hhi, and_false, if_false]
      have rd3 := cometWithExtendedAssetList_block_4845_taken
        (immWords := wordsOf (immStore v)) (by decide) (getterLength_huge (by omega) hsize)
        (by rw [cometWithExtendedAssetListPatchedValidJumpsRuntime v]; jump_dest) rd2
      exact cometRevert1410 (by decide) rd3
  · simp only [GetterResult, hvalue, false_and, if_false]
    have rd2 := cometWithExtendedAssetList_block_4838_taken
      (immWords := wordsOf (immStore v)) (by decide) hvalue
      (by rw [cometWithExtendedAssetListPatchedValidJumpsRuntime v]; jump_dest) rd1
    exact cometRevert1410 (by decide) rd2

/-- `numAssets()`: the theorem `Correct.lean` routes selector 47 to. -/
theorem cometWithExtendedAssetListNumAssetsBody {σ σ₀ A I} {g : UInt256} (v : CometWithExtendedAssetListImmutables)
    (hcode : I.code = deployedRuntime v) (hsize : I.calldata.size < UInt256.size)
    (hsel : selIs I (cometWithExtendedAssetListSelBytes 47)) :
    runtimeRefinementFor config contract σ σ₀ g A I (immStore v) := by
  have hsz : 4 ≤ I.calldata.size :=
    calldata_size_ge_of_selIs I (cometWithExtendedAssetListSelBytes 47) rfl hsel
  exact immutableGetter_refines (t := numAssetsTransition) hcode hsz
    (cometSelectorDispatch ⟨47, by decide⟩ hsel) rfl rfl rfl
    (immStore_get_numAssets v) (uint8ReturnEncoding v.numAssets v.numAssets_lt)
    (numAssetsX v hcode hsz hsize hsel)

end Benchmarks.CompoundIII.Comet
