import Benchmarks.CompoundIII.Comet.Dispatch
import Benchmarks.CompoundIII.Comet.GetterCommon
import Benchmarks.CompoundIII.Comet.RuntimeBlocks_009
import Benchmarks.CompoundIII.Comet.RuntimeBlocks_024
import Benchmarks.CompoundIII.Comet.RuntimeBlocks_025

/-!
# CometWithExtendedAssetList `borrowKink()`

Per-function proof: calldata decode facts, the EVM trace from the dispatcher arm through the
body, the Solm body evaluation, and the `…Body` theorem `Correct.lean` consumes.
Dispatcher arm entry: pc 1042; reach lemma `cometWithExtendedAssetListReachBorrowKinkBody`.
-/

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables
open Benchmarks.CompoundIII.Comet.Immutables
open cometWithExtendedAssetListBlocks

namespace Benchmarks.CompoundIII.Comet

set_option maxRecDepth 2000000

theorem borrowKinkX {σ σ₀ A I} {g : Sat256} (v : CometWithExtendedAssetListImmutables)
    (hcode : I.code = deployedRuntime v) (hsz : 4 ≤ I.calldata.size)
    (hsize : I.calldata.size < UInt256.size)
    (hsel : selIs I (cometWithExtendedAssetListSelBytes 39)) :
    GetterResult (deployedRuntime v) I g (initState σ σ₀ g A I) σ
      v.borrowKink.toByteArray := by
  obtain ⟨k, C, rd⟩ := cometWithExtendedAssetListReachBorrowKinkBody
    (σ := σ) (σ₀ := σ₀) (A := A) (g := g) v hcode hsz hsize hsel
  have rd1 := cometWithExtendedAssetList_block_1042 (immWords := wordsOf (immStore v))
    (by decide) (by rw [cometWithExtendedAssetListPatchedValidJumpsRuntime v]; jump_dest) rd
  by_cases hvalue : I.weiValue = ⟨0⟩
  · have rd2 := cometWithExtendedAssetList_block_4405_fallthrough
      (immWords := wordsOf (immStore v)) (by decide) hvalue rd1
    by_cases hhi : I.calldata.size < 2 ^ 255 + 4
    · simp only [GetterResult, hvalue, hhi, and_self, if_true]
      have rd3 := cometWithExtendedAssetList_block_4412_fallthrough
        (immWords := wordsOf (immStore v)) (by decide) (getterLength_ok hsz hhi hsize) rd2
      have rd4 := cometWithExtendedAssetList_block_4424
        (immWords := wordsOf (immStore v)) (by decide) rd3
      rw [wordsOf_immStore_borrowKink, wordOfInt_ofNat_toNat_gen, u256_ofNat_toNat] at rd4
      exact (getterReturnData v.borrowKink) ▸ rd4
    · simp only [GetterResult, hvalue, hhi, and_false, if_false]
      have rd3 := cometWithExtendedAssetList_block_4412_taken
        (immWords := wordsOf (immStore v)) (by decide) (getterLength_huge (by omega) hsize)
        (by rw [cometWithExtendedAssetListPatchedValidJumpsRuntime v]; jump_dest) rd2
      exact cometRevert1410 (by decide) rd3
  · simp only [GetterResult, hvalue, false_and, if_false]
    have rd2 := cometWithExtendedAssetList_block_4405_taken
      (immWords := wordsOf (immStore v)) (by decide) hvalue
      (by rw [cometWithExtendedAssetListPatchedValidJumpsRuntime v]; jump_dest) rd1
    exact cometRevert1410 (by decide) rd2

/-- `borrowKink()`: the theorem `Correct.lean` routes selector 39 to. -/
theorem cometWithExtendedAssetListBorrowKinkBody {σ σ₀ A I} {g : UInt256} (v : CometWithExtendedAssetListImmutables)
    (hcode : I.code = deployedRuntime v) (hsize : I.calldata.size < UInt256.size)
    (hsel : selIs I (cometWithExtendedAssetListSelBytes 39)) :
    runtimeRefinementFor config contract σ σ₀ g A I (immStore v) := by
  have hsz : 4 ≤ I.calldata.size :=
    calldata_size_ge_of_selIs I (cometWithExtendedAssetListSelBytes 39) rfl hsel
  exact immutableGetter_refines (t := borrowKinkTransition) hcode hsz
    (cometSelectorDispatch ⟨39, by decide⟩ hsel) rfl rfl rfl
    (immStore_get_borrowKink v) (uint256ReturnEncoding v.borrowKink)
    (borrowKinkX v hcode hsz hsize hsel)

end Benchmarks.CompoundIII.Comet
