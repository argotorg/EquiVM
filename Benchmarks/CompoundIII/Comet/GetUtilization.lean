import Benchmarks.CompoundIII.Comet.Dispatch
import Benchmarks.CompoundIII.Comet.UtilizationEvm
import Benchmarks.CompoundIII.Comet.RuntimeBlocks_009
import Benchmarks.CompoundIII.Comet.RuntimeBlocks_012
import Benchmarks.CompoundIII.Comet.RuntimeBlocks_023

/-!
# CometWithExtendedAssetList `getUtilization()`

Per-function proof: calldata decode facts, the EVM trace from the dispatcher arm through the
body, the Solm body evaluation, and the `…Body` theorem `Correct.lean` consumes.
Dispatcher arm entry: pc 1087; reach lemma `cometWithExtendedAssetListReachGetUtilizationBody`.
-/

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open cometWithExtendedAssetListBlocks
open Reasoning.Immutables
open Benchmarks.CompoundIII.Comet.Immutables

namespace Benchmarks.CompoundIII.Comet

set_option maxRecDepth 10000

theorem getUtilization_returns {σ σ₀ A I} {g : Sat256} (imms : Store)
    (hvalue : I.weiValue = ⟨0⟩) (hhi : I.calldata.size < 2 ^ 255 + 4) :
    ∃ frame, ExecTransitionBody config contract (initState σ σ₀ g A I)
      ∅ getUtilizationTransition.body
      (.returned frame (initState σ σ₀ g A I)
        (some [.int (utilizationAt (initState σ σ₀ g A I)).toNat])) imms := by
  let frame := calldataLocalFrame
    { contract := contract, locals := ∅, immutables := imms } (initState σ σ₀ g A I)
  refine ⟨{ frame with
    locals := frame.locals.insert "result" (.int (utilizationAt (initState σ σ₀ g A I)).toNat) },
    .execBlockRet ?_⟩
  apply (calldataPrologue_ok hvalue hhi).run
  apply ExecBlock.consNormal
    (utilization_call frame (initState σ σ₀ g A I) "result" rfl)
  exact ABlock.start.returns (by
    simp only [evalExpr?, EvalResult.ofOption, Std.HashMap.get?_eq_getElem?,
      Std.HashMap.getElem?_insert]
    rfl)

theorem utilizationAt_init {σ σ₀ A I} {g : Sat256} :
    utilizationAt (initState σ σ₀ g A I) =
      utilizationWord (solcSlotWordAt ⟨0⟩ σ I) (solcSlotWordAt ⟨1⟩ σ I) := by
  simp only [utilizationAt, storageLoad_initState_solcSlotWord, solcSlotWordAt]

theorem getUtilizationX {σ σ₀ A I} {g : Sat256} (v : CometWithExtendedAssetListImmutables)
    (hcode : I.code = deployedRuntime v) (hsz : 4 ≤ I.calldata.size)
    (hsize : I.calldata.size < UInt256.size)
    (hsel : selIs I (cometWithExtendedAssetListSelBytes 33)) :
    GetterResult (deployedRuntime v) I g (initState σ σ₀ g A I) σ
      (utilizationWord (solcSlotWordAt ⟨0⟩ σ I) (solcSlotWordAt ⟨1⟩ σ I)).toByteArray := by
  obtain ⟨k, C, rd⟩ := cometWithExtendedAssetListReachGetUtilizationBody
    (σ := σ) (σ₀ := σ₀) (A := A) (g := g) v hcode hsz hsize hsel
  have rd1 := cometWithExtendedAssetList_block_1087 (immWords := wordsOf (immStore v))
    (by decide) (by rw [cometWithExtendedAssetListPatchedValidJumpsRuntime v]; jump_dest) rd
  by_cases hvalue : I.weiValue = ⟨0⟩
  · have rd2 := cometWithExtendedAssetList_block_4143_fallthrough
      (immWords := wordsOf (immStore v)) (by decide) hvalue rd1
    by_cases hhi : I.calldata.size < 2 ^ 255 + 4
    · simp only [GetterResult, hvalue, hhi, and_self, if_true]
      have rd3 := cometWithExtendedAssetList_block_4150_fallthrough
        (immWords := wordsOf (immStore v)) (by decide) (getterLength_ok hsz hhi hsize) rd2
      have rd4 := cometWithExtendedAssetList_block_4162
        (immWords := wordsOf (immStore v)) (by decide)
        (by rw [cometWithExtendedAssetListPatchedValidJumpsRuntime v]; jump_dest) rd3
      obtain ⟨k', C', rd5⟩ := cometUtilization (v := v) (ret := UInt256.ofNat 1504)
        (by change 14 ≤ 1024; decide)
        (by rw [cometWithExtendedAssetListPatchedValidJumps v]; jump_dest) rd4
      have rd6 := cometWithExtendedAssetList_block_1504
        (immWords := wordsOf (immStore v)) (by decide) rd5
      exact (getterReturnData (utilizationWord (solcSlotWordAt ⟨0⟩ σ I) (solcSlotWordAt ⟨1⟩ σ I))) ▸ rd6
    · simp only [GetterResult, hvalue, hhi, and_false, if_false]
      have rd3 := cometWithExtendedAssetList_block_4150_taken
        (immWords := wordsOf (immStore v)) (by decide) (getterLength_huge (by omega) hsize)
        (by rw [cometWithExtendedAssetListPatchedValidJumpsRuntime v]; jump_dest) rd2
      exact cometRevert1410 (by decide) rd3
  · simp only [GetterResult, hvalue, false_and, if_false]
    have rd2 := cometWithExtendedAssetList_block_4143_taken
      (immWords := wordsOf (immStore v)) (by decide) hvalue
      (by rw [cometWithExtendedAssetListPatchedValidJumpsRuntime v]; jump_dest) rd1
    exact cometRevert1410 (by decide) rd2

/-- `getUtilization()`: the theorem `Correct.lean` routes selector 33 to. -/
theorem cometWithExtendedAssetListGetUtilizationBody {σ σ₀ A I} {g : UInt256} (v : CometWithExtendedAssetListImmutables)
    (hcode : I.code = deployedRuntime v) (hsize : I.calldata.size < UInt256.size)
    (hsel : selIs I (cometWithExtendedAssetListSelBytes 33)) :
    runtimeRefinementFor config contract σ σ₀ g A I (immStore v) := by
  have hsz : 4 ≤ I.calldata.size := calldata_size_ge_of_selIs I (cometWithExtendedAssetListSelBytes 33) rfl hsel
  let w := utilizationWord (solcSlotWordAt ⟨0⟩ σ I) (solcSlotWordAt ⟨1⟩ σ I)
  apply guardedGetter_refines (t := getUtilizationTransition) (value := .int w.toNat)
    hcode hsz (cometSelectorDispatch ⟨33, by decide⟩ hsel) rfl rfl rfl
    (uint256ReturnEncoding w) ?_ (getUtilizationX v hcode hsz hsize hsel)
  intro hv hhi
  simpa only [utilizationAt_init] using getUtilization_returns (immStore v) hv hhi

end Benchmarks.CompoundIII.Comet
