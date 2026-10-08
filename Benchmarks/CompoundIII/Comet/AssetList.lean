import Benchmarks.CompoundIII.Comet.Dispatch
import Benchmarks.CompoundIII.Comet.GetterCommon
import Benchmarks.CompoundIII.Comet.RuntimeBlocks_008
import Benchmarks.CompoundIII.Comet.RuntimeBlocks_032

/-!
# CometWithExtendedAssetList `assetList()`

Per-function proof: calldata decode facts, the EVM trace from the dispatcher arm through the
body, the Solm body evaluation, and the `…Body` theorem `Correct.lean` consumes.
Dispatcher arm entry: pc 826; reach lemma `cometWithExtendedAssetListReachAssetListBody`.
-/

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables
open Benchmarks.CompoundIII.Comet.Immutables
open cometWithExtendedAssetListBlocks

namespace Benchmarks.CompoundIII.Comet

set_option maxRecDepth 2000000

theorem assetListX {σ σ₀ A I} {g : Sat256} (v : CometWithExtendedAssetListImmutables)
    (hcode : I.code = deployedRuntime v) (hsz : 4 ≤ I.calldata.size)
    (hsize : I.calldata.size < UInt256.size)
    (hsel : selIs I (cometWithExtendedAssetListSelBytes 62)) :
    GetterResult (deployedRuntime v) I g (initState σ σ₀ g A I) σ
      (EVM.word v.assetList.val).toByteArray := by
  obtain ⟨k, C, rd⟩ := cometWithExtendedAssetListReachAssetListBody
    (σ := σ) (σ₀ := σ₀) (A := A) (g := g) v hcode hsz hsize hsel
  have rd1 := cometWithExtendedAssetList_block_826 (immWords := wordsOf (immStore v))
    (by decide) (by rw [cometWithExtendedAssetListPatchedValidJumpsRuntime v]; jump_dest) rd
  by_cases hvalue : I.weiValue = ⟨0⟩
  · have rd2 := cometWithExtendedAssetList_block_6047_fallthrough
      (immWords := wordsOf (immStore v)) (by decide) hvalue rd1
    by_cases hhi : I.calldata.size < 2 ^ 255 + 4
    · simp only [GetterResult, hvalue, hhi, and_self, if_true]
      have rd3 := cometWithExtendedAssetList_block_6054_fallthrough
        (immWords := wordsOf (immStore v)) (by decide) (getterLength_ok hsz hhi hsize) rd2
      have rd4 := cometWithExtendedAssetList_block_6066
        (immWords := wordsOf (immStore v)) (by decide) rd3
      rw [wordsOf_immStore_assetList] at rd4
      have hclean := getterAddressClean v.assetList
      change UInt256.land (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1)
        (UInt256.ofNat 160)) (UInt256.ofNat 1)) (EVM.Word.ofNat v.assetList.val) = _ at hclean
      rw [hclean] at rd4
      exact (getterReturnData (EVM.word v.assetList.val)) ▸ rd4
    · simp only [GetterResult, hvalue, hhi, and_false, if_false]
      have rd3 := cometWithExtendedAssetList_block_6054_taken
        (immWords := wordsOf (immStore v)) (by decide) (getterLength_huge (by omega) hsize)
        (by rw [cometWithExtendedAssetListPatchedValidJumpsRuntime v]; jump_dest) rd2
      exact cometRevert1410 (by decide) rd3
  · simp only [GetterResult, hvalue, false_and, if_false]
    have rd2 := cometWithExtendedAssetList_block_6047_taken
      (immWords := wordsOf (immStore v)) (by decide) hvalue
      (by rw [cometWithExtendedAssetListPatchedValidJumpsRuntime v]; jump_dest) rd1
    exact cometRevert1410 (by decide) rd2

/-- `assetList()`: the theorem `Correct.lean` routes selector 62 to. -/
theorem cometWithExtendedAssetListAssetListBody {σ σ₀ A I} {g : UInt256} (v : CometWithExtendedAssetListImmutables)
    (hcode : I.code = deployedRuntime v) (hsize : I.calldata.size < UInt256.size)
    (hsel : selIs I (cometWithExtendedAssetListSelBytes 62)) :
    runtimeRefinementFor config contract σ σ₀ g A I (immStore v) := by
  have hsz : 4 ≤ I.calldata.size :=
    calldata_size_ge_of_selIs I (cometWithExtendedAssetListSelBytes 62) rfl hsel
  exact immutableGetter_refines (t := assetListTransition) hcode hsz
    (cometSelectorDispatch ⟨62, by decide⟩ hsel) rfl rfl rfl
    (immStore_get_assetList v) (getterAddressEncoding v.assetList)
    (assetListX v hcode hsz hsize hsel)

end Benchmarks.CompoundIII.Comet
