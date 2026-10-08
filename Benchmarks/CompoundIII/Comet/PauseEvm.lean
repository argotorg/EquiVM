import Benchmarks.CompoundIII.Comet.Dispatch
import Benchmarks.CompoundIII.Comet.PauseDecode
import Benchmarks.CompoundIII.Comet.PauseAuthEvm
import Benchmarks.CompoundIII.Comet.PauseReturn
import Benchmarks.CompoundIII.Comet.RuntimeBlocks_010

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach Reasoning.Immutables
open Benchmarks.CompoundIII.Comet.Immutables cometWithExtendedAssetListBlocks

namespace Benchmarks.CompoundIII.Comet

set_option maxRecDepth 10000

def PauseResult (v : CometWithExtendedAssetListImmutables) (I : ExecutionEnv)
    (g : Sat256) (s0 : State) (σ : AccountMap) : Prop :=
  if I.weiValue = ⟨0⟩ ∧ 164 ≤ I.calldata.size ∧ I.calldata.size < 2^255 + 4 ∧
      PauseCanonical I.calldata ∧ PauseAuthorized v I then
    if I.perm = true then
      RDret (deployedRuntime v) g s0 (pauseAccounts σ I (pauseInputs I.calldata)) ByteArray.empty
    else RDstatic (deployedRuntime v) g s0
  else RDrev (deployedRuntime v) g s0

theorem pauseX {σ σ₀ A I} {g : Sat256} (v : CometWithExtendedAssetListImmutables)
    (hcode : I.code = deployedRuntime v) (hsz : 4 ≤ I.calldata.size)
    (hsize : I.calldata.size < UInt256.size)
    (hsel : selIs I (cometWithExtendedAssetListSelBytes 25)) :
    PauseResult v I g (initState σ σ₀ g A I) σ := by
  obtain ⟨k, C, rd⟩ := cometWithExtendedAssetListReachPauseBody
    (σ := σ) (σ₀ := σ₀) (A := A) (g := g) v hcode hsz hsize hsel
  have rd1 := cometWithExtendedAssetList_block_1159 (immWords := wordsOf (immStore v))
    (by decide) (by rw [cometWithExtendedAssetListPatchedValidJumpsRuntime v]; jump_dest) rd
  by_cases hv : I.weiValue = ⟨0⟩
  · have rd2 := cometWithExtendedAssetList_block_3361_fallthrough
      (immWords := wordsOf (immStore v)) (by decide) hv rd1
    by_cases hlo : 164 ≤ I.calldata.size
    · by_cases hhi : I.calldata.size < 2^255 + 4
      · have rd3 := cometWithExtendedAssetList_block_3368_fallthrough
          (immWords := wordsOf (immStore v)) (by decide)
          (calldataLength_ok (need := 160) (by decide) hlo hhi hsize) rd2
        have hd := cometPauseDecode (v := v) (by decide) rd3
        by_cases hc : PauseCanonical I.calldata
        · rw [if_pos hc] at hd
          obtain ⟨k4, C4, rd4⟩ := hd
          have ha := cometPauseAuthorize (v := v) (by change 9 ≤ 1024; decide) rd4
          by_cases hallowed : PauseAuthorized v I
          · rw [if_pos hallowed] at ha
            obtain ⟨k5, C5, rd5⟩ := ha
            unfold PauseResult
            rw [if_pos ⟨hv, hlo, hhi, hc, hallowed⟩]
            exact cometPauseReturn (v := v) (pauseInputs I.calldata) (by decide) rd5
          · simp only [PauseResult, hallowed, and_false, if_false]
            rwa [if_neg hallowed] at ha
        · simp only [PauseResult, hc, false_and, and_false, if_false]
          rwa [if_neg hc] at hd
      · simp only [PauseResult, hhi, false_and, and_false, if_false]
        have rd3 := cometWithExtendedAssetList_block_3368_taken
          (immWords := wordsOf (immStore v)) (by decide)
          (calldataLength_huge (need := 160) (by decide) (by omega) hsize)
          (by rw [cometWithExtendedAssetListPatchedValidJumpsRuntime v]; jump_dest) rd2
        exact cometRevert1410 (by decide) rd3
    · simp only [PauseResult, hlo, false_and, and_false, if_false]
      have rd3 := cometWithExtendedAssetList_block_3368_taken
        (immWords := wordsOf (immStore v)) (by decide)
        (calldataLength_short (need := 160) (by decide) hsz (by omega) hsize)
        (by rw [cometWithExtendedAssetListPatchedValidJumpsRuntime v]; jump_dest) rd2
      exact cometRevert1410 (by decide) rd3
  · simp only [PauseResult, hv, false_and, if_false]
    have rd2 := cometWithExtendedAssetList_block_3361_taken
      (immWords := wordsOf (immStore v)) (by decide) hv
      (by rw [cometWithExtendedAssetListPatchedValidJumpsRuntime v]; jump_dest) rd1
    exact cometRevert1410 (by decide) rd2

end Benchmarks.CompoundIII.Comet
