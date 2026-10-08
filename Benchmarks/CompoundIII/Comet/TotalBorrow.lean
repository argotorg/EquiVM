import Benchmarks.CompoundIII.Comet.Dispatch
import Benchmarks.CompoundIII.Comet.TotalReturn
import Benchmarks.CompoundIII.Comet.RuntimeBlocks_009

/-!
# CometWithExtendedAssetList `totalBorrow()`

Per-function proof: calldata decode facts, the EVM trace from the dispatcher arm through the
body, the Solm body evaluation, and the `…Body` theorem `Correct.lean` consumes.
Dispatcher arm entry: pc 1069; reach lemma `cometWithExtendedAssetListReachTotalBorrowBody`.
-/

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open cometWithExtendedAssetListBlocks
open Reasoning.Immutables
open Benchmarks.CompoundIII.Comet.Immutables

namespace Benchmarks.CompoundIII.Comet

set_option maxRecDepth 10000

theorem totalBorrowX {σ σ₀ A I} {g : Sat256} (v : CometWithExtendedAssetListImmutables)
    (hcode : I.code = deployedRuntime v) (hsz : 4 ≤ I.calldata.size)
    (hsize : I.calldata.size < UInt256.size)
    (hsel : selIs I (cometWithExtendedAssetListSelBytes 35)) :
    CheckedGetterResult
      (CurrentIndicesValid v (solcSlotWordAt ⟨0⟩ σ I) (solcSlotWordAt ⟨1⟩ σ I) (timestampWord I))
      (deployedRuntime v) I g (initState σ σ₀ g A I) σ
      (totalReadWord v (solcSlotWordAt ⟨0⟩ σ I) (solcSlotWordAt ⟨1⟩ σ I)
        (timestampWord I) true).toByteArray := by
  obtain ⟨k, C, rd⟩ := cometWithExtendedAssetListReachTotalBorrowBody
    (σ := σ) (σ₀ := σ₀) (A := A) (g := g) v hcode hsz hsize hsel
  have rd1 := cometWithExtendedAssetList_block_1069 (immWords := wordsOf (immStore v))
    (by decide) (by rw [cometWithExtendedAssetListPatchedValidJumpsRuntime v]; jump_dest) rd
  by_cases hv : I.weiValue = ⟨0⟩
  · have rd2 := cometWithExtendedAssetList_block_4231_fallthrough
      (immWords := wordsOf (immStore v)) (by decide) hv rd1
    by_cases hhi : I.calldata.size < 2^255 + 4
    · have rd3 := cometWithExtendedAssetList_block_4238_fallthrough
        (immWords := wordsOf (immStore v)) (by decide) (getterLength_ok hsz hhi hsize) rd2
      have rd4 := cometWithExtendedAssetList_block_4250
        (immWords := wordsOf (immStore v)) (by decide)
        (by rw [cometWithExtendedAssetListPatchedValidJumpsRuntime v]; jump_dest) rd3
      have hr := cometCurrentIndices (v := v) true (by change 36 ≤ 1024; decide) rd4
      dsimp only at hr
      by_cases hvalid : CurrentIndicesValid v (solcSlotWordAt ⟨0⟩ σ I)
          (solcSlotWordAt ⟨1⟩ σ I) (timestampWord I)
      · unfold CheckedGetterResult
        rw [if_pos ⟨hv, hhi, hvalid⟩]
        rw [if_pos hvalid] at hr
        obtain ⟨k', C', rd5⟩ := hr
        exact cometTotalReturn true _ _ _ (by decide) (currentIndex_lt hvalid true) rd5
      · simp only [CheckedGetterResult, hvalid, and_false, if_false]
        rw [if_neg hvalid] at hr
        exact hr
    · simp only [CheckedGetterResult, hhi, false_and, and_false, if_false]
      have rd3 := cometWithExtendedAssetList_block_4238_taken
        (immWords := wordsOf (immStore v)) (by decide) (getterLength_huge (by omega) hsize)
        (by rw [cometWithExtendedAssetListPatchedValidJumpsRuntime v]; jump_dest) rd2
      exact cometRevert1410 (by decide) rd3
  · simp only [CheckedGetterResult, hv, false_and, if_false]
    have rd2 := cometWithExtendedAssetList_block_4231_taken
      (immWords := wordsOf (immStore v)) (by decide) hv
      (by rw [cometWithExtendedAssetListPatchedValidJumpsRuntime v]; jump_dest) rd1
    exact cometRevert1410 (by decide) rd2

/-- `totalBorrow()`: the theorem `Correct.lean` routes selector 35 to. -/
theorem cometWithExtendedAssetListTotalBorrowBody {σ σ₀ A I} {g : UInt256} (v : CometWithExtendedAssetListImmutables)
    (hcode : I.code = deployedRuntime v) (hsize : I.calldata.size < UInt256.size)
    (hsel : selIs I (cometWithExtendedAssetListSelBytes 35)) :
    runtimeRefinementFor config contract σ σ₀ g A I (immStore v) := by
  have hsz : 4 ≤ I.calldata.size := calldata_size_ge_of_selIs I (cometWithExtendedAssetListSelBytes 35) rfl hsel
  let w := totalReadWord v (solcSlotWordAt ⟨0⟩ σ I) (solcSlotWordAt ⟨1⟩ σ I)
    (timestampWord I) true
  apply checkedGetter_refines (t := totalBorrowTransition) (values := [.int w.toNat])
    hcode hsz (cometSelectorDispatch ⟨35, by decide⟩ hsel) rfl (totalTransition_body true)
    (fun _ ↦ returnEquiv_of_encode (uint256ReturnEncoding w)) ?_ ?_
    (totalBorrowX v hcode hsz hsize hsel)
  · intro hv hhi hvalid
    exact getTotal_returns v true hv hhi hvalid
  · intro hv hhi hvalid
    exact getTotal_reverts v true hv hhi hvalid

end Benchmarks.CompoundIII.Comet
