import Benchmarks.CompoundIII.Comet.Dispatch
import Benchmarks.CompoundIII.Comet.GetterCommon
import Benchmarks.CompoundIII.Comet.RuntimeBlocks_010
import Benchmarks.CompoundIII.Comet.RuntimeBlocks_021

/-!
# CometWithExtendedAssetList `extensionDelegate()`

Per-function proof: calldata decode facts, the EVM trace from the dispatcher arm through the
body, the Solm body evaluation, and the `…Body` theorem `Correct.lean` consumes.
Dispatcher arm entry: pc 1150; reach lemma `cometWithExtendedAssetListReachExtensionDelegateBody`.
-/

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables
open Benchmarks.CompoundIII.Comet.Immutables
open cometWithExtendedAssetListBlocks

namespace Benchmarks.CompoundIII.Comet

set_option maxRecDepth 2000000

theorem extensionDelegateX {σ σ₀ A I} {g : Sat256} (v : CometWithExtendedAssetListImmutables)
    (hcode : I.code = deployedRuntime v) (hsz : 4 ≤ I.calldata.size)
    (hsize : I.calldata.size < UInt256.size)
    (hsel : selIs I (cometWithExtendedAssetListSelBytes 26)) :
    GetterResult (deployedRuntime v) I g (initState σ σ₀ g A I) σ
      (EVM.word v.extensionDelegate.val).toByteArray := by
  obtain ⟨k, C, rd⟩ := cometWithExtendedAssetListReachExtensionDelegateBody
    (σ := σ) (σ₀ := σ₀) (A := A) (g := g) v hcode hsz hsize hsel
  have rd1 := cometWithExtendedAssetList_block_1150 (immWords := wordsOf (immStore v))
    (by decide) (by rw [cometWithExtendedAssetListPatchedValidJumpsRuntime v]; jump_dest) rd
  by_cases hvalue : I.weiValue = ⟨0⟩
  · have rd2 := cometWithExtendedAssetList_block_3744_fallthrough
      (immWords := wordsOf (immStore v)) (by decide) hvalue rd1
    by_cases hhi : I.calldata.size < 2 ^ 255 + 4
    · simp only [GetterResult, hvalue, hhi, and_self, if_true]
      have rd3 := cometWithExtendedAssetList_block_3751_fallthrough
        (immWords := wordsOf (immStore v)) (by decide) (getterLength_ok hsz hhi hsize) rd2
      have rd4 := cometWithExtendedAssetList_block_3763
        (immWords := wordsOf (immStore v)) (by decide) rd3
      rw [wordsOf_immStore_extensionDelegate] at rd4
      have hclean := getterAddressClean v.extensionDelegate
      change UInt256.land (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1)
        (UInt256.ofNat 160)) (UInt256.ofNat 1)) (EVM.Word.ofNat v.extensionDelegate.val) = _ at hclean
      rw [hclean] at rd4
      exact (getterReturnData (EVM.word v.extensionDelegate.val)) ▸ rd4
    · simp only [GetterResult, hvalue, hhi, and_false, if_false]
      have rd3 := cometWithExtendedAssetList_block_3751_taken
        (immWords := wordsOf (immStore v)) (by decide) (getterLength_huge (by omega) hsize)
        (by rw [cometWithExtendedAssetListPatchedValidJumpsRuntime v]; jump_dest) rd2
      exact cometRevert1410 (by decide) rd3
  · simp only [GetterResult, hvalue, false_and, if_false]
    have rd2 := cometWithExtendedAssetList_block_3744_taken
      (immWords := wordsOf (immStore v)) (by decide) hvalue
      (by rw [cometWithExtendedAssetListPatchedValidJumpsRuntime v]; jump_dest) rd1
    exact cometRevert1410 (by decide) rd2

/-- `extensionDelegate()`: the theorem `Correct.lean` routes selector 26 to. -/
theorem cometWithExtendedAssetListExtensionDelegateBody {σ σ₀ A I} {g : UInt256} (v : CometWithExtendedAssetListImmutables)
    (hcode : I.code = deployedRuntime v) (hsize : I.calldata.size < UInt256.size)
    (hsel : selIs I (cometWithExtendedAssetListSelBytes 26)) :
    runtimeRefinementFor config contract σ σ₀ g A I (immStore v) := by
  have hsz : 4 ≤ I.calldata.size :=
    calldata_size_ge_of_selIs I (cometWithExtendedAssetListSelBytes 26) rfl hsel
  exact immutableGetter_refines (t := extensionDelegateTransition) hcode hsz
    (cometSelectorDispatch ⟨26, by decide⟩ hsel) rfl rfl rfl
    (immStore_get_extensionDelegate v) (getterAddressEncoding v.extensionDelegate)
    (extensionDelegateX v hcode hsz hsize hsel)

end Benchmarks.CompoundIII.Comet
