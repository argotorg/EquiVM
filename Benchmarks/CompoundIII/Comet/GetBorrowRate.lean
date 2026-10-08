import Benchmarks.CompoundIII.Comet.Dispatch
import Benchmarks.CompoundIII.Comet.RateExternal
import Benchmarks.CompoundIII.Comet.BorrowRateRoutine
import Benchmarks.CompoundIII.Comet.RuntimeBlocks_009
import Benchmarks.CompoundIII.Comet.RuntimeBlocks_026
import Benchmarks.CompoundIII.Comet.RuntimeBlocks_025

/-!
# CometWithExtendedAssetList `getBorrowRate(uint256)`

Per-function proof: calldata decode facts, the EVM trace from the dispatcher arm through the
body, the Solm body evaluation, and the `…Body` theorem `Correct.lean` consumes.
Dispatcher arm entry: pc 1006; reach lemma `cometWithExtendedAssetListReachGetBorrowRateBody`.
-/

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open cometWithExtendedAssetListBlocks
open Reasoning.Immutables
open Benchmarks.CompoundIII.Comet.Immutables

namespace Benchmarks.CompoundIII.Comet

set_option maxRecDepth 10000

theorem getBorrowRateX {σ σ₀ A I} {g : Sat256} (v : CometWithExtendedAssetListImmutables)
    (hcode : I.code = deployedRuntime v) (hsz : 4 ≤ I.calldata.size)
    (hsize : I.calldata.size < UInt256.size)
    (hsel : selIs I (cometWithExtendedAssetListSelBytes 43)) :
    UintFunctionResult (RateValid (rateParams v true) (calldataWord I.calldata 4))
      (deployedRuntime v) I g (initState σ σ₀ g A I) σ
      (rateWord (rateParams v true) (calldataWord I.calldata 4)).toByteArray := by
  obtain ⟨k, C, rd⟩ := cometWithExtendedAssetListReachGetBorrowRateBody
    (σ := σ) (σ₀ := σ₀) (A := A) (g := g) v hcode hsz hsize hsel
  have rd1 := cometWithExtendedAssetList_block_1006 (immWords := wordsOf (immStore v))
    (by decide) (by rw [cometWithExtendedAssetListPatchedValidJumpsRuntime v]; jump_dest) rd
  by_cases hv : I.weiValue = ⟨0⟩
  · have rd2 := cometWithExtendedAssetList_block_4645_fallthrough
      (immWords := wordsOf (immStore v)) (by decide) hv rd1
    by_cases hlo : 36 ≤ I.calldata.size
    · by_cases hhi : I.calldata.size < 2 ^ 255 + 4
      · have rd3 := cometWithExtendedAssetList_block_4652_fallthrough
          (immWords := wordsOf (immStore v)) (by decide)
          (calldataLength_ok (need := 32) (by decide) hlo hhi hsize) rd2
        have rd4 := cometWithExtendedAssetList_block_4664
          (immWords := wordsOf (immStore v)) (by decide)
          (by rw [cometWithExtendedAssetListPatchedValidJumpsRuntime v]; jump_dest) rd3
        have hr := cometBorrowRate (v := v) (ret := UInt256.ofNat 4676)
          (u := calldataWord I.calldata 4)
          (by change 17 ≤ 1024; decide)
          (by rw [cometWithExtendedAssetListPatchedValidJumps v]; jump_dest) rd4
        by_cases hvalid : RateValid (rateParams v true) (calldataWord I.calldata 4)
        · simp only [UintFunctionResult, hv, hlo, hhi, hvalid, and_self, if_true]
          rw [if_pos hvalid] at hr
          obtain ⟨k', C', rd5⟩ := hr
          have rd6 := cometWithExtendedAssetList_block_4676
            (immWords := wordsOf (immStore v)) (by decide) rd5
          have hclean : UInt256.land (rateWord (rateParams v true) (calldataWord I.calldata 4))
              (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 64))
                (UInt256.ofNat 1)) =
              rateWord (rateParams v true) (calldataWord I.calldata 4) :=
            u256LandMaskCleanOfToNat _ _ (bits := 64) rfl (rateWord_lt hvalid)
          rw [hclean] at rd6
          exact (getterReturnData (rateWord (rateParams v true) (calldataWord I.calldata 4))) ▸ rd6
        · simp only [UintFunctionResult, hvalid, and_false, if_false]
          rw [if_neg hvalid] at hr
          exact hr
      · simp only [UintFunctionResult, hhi, false_and, and_false, if_false]
        have rd3 := cometWithExtendedAssetList_block_4652_taken
          (immWords := wordsOf (immStore v)) (by decide)
          (calldataLength_huge (need := 32) (by decide) (by omega) hsize)
          (by rw [cometWithExtendedAssetListPatchedValidJumpsRuntime v]; jump_dest) rd2
        exact cometRevert1410 (by decide) rd3
    · simp only [UintFunctionResult, hlo, false_and, and_false, if_false]
      have rd3 := cometWithExtendedAssetList_block_4652_taken
        (immWords := wordsOf (immStore v)) (by decide)
        (calldataLength_short (need := 32) (by decide) hsz (by omega) hsize)
        (by rw [cometWithExtendedAssetListPatchedValidJumpsRuntime v]; jump_dest) rd2
      exact cometRevert1410 (by decide) rd3
  · simp only [UintFunctionResult, hv, false_and, if_false]
    have rd2 := cometWithExtendedAssetList_block_4645_taken
      (immWords := wordsOf (immStore v)) (by decide) hv
      (by rw [cometWithExtendedAssetListPatchedValidJumpsRuntime v]; jump_dest) rd1
    exact cometRevert1410 (by decide) rd2

/-- `getBorrowRate(uint256)`: the theorem `Correct.lean` routes selector 43 to. -/
theorem cometWithExtendedAssetListGetBorrowRateBody {σ σ₀ A I} {g : UInt256} (v : CometWithExtendedAssetListImmutables)
    (hcode : I.code = deployedRuntime v) (hsize : I.calldata.size < UInt256.size)
    (hsel : selIs I (cometWithExtendedAssetListSelBytes 43)) :
    runtimeRefinementFor config contract σ σ₀ g A I (immStore v) := by
  have hsz : 4 ≤ I.calldata.size := calldata_size_ge_of_selIs I (cometWithExtendedAssetListSelBytes 43) rfl hsel
  let w := rateWord (rateParams v true) (calldataWord I.calldata 4)
  apply uintFunction_refines (t := getBorrowRateTransition) (value := .int w.toNat)
    hcode (cometSelectorDispatch ⟨43, by decide⟩ hsel) rfl rfl ?_ ?_ ?_
    (getBorrowRateX v hcode hsz hsize hsel)
  · intro hvalid
    exact returnEquiv_of_encode (uintReturnEncoding ⟨64, by decide⟩ w (rateWord_lt hvalid))
  · intro hv hhi hvalid
    exact getRate_returns v true hv hhi hvalid
  · intro hv hhi hvalid
    exact getRate_reverts v true hv hhi hvalid

end Benchmarks.CompoundIII.Comet
