import Benchmarks.CompoundIII.Comet.PauseInputs

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach Reasoning.Immutables
open Benchmarks.CompoundIII.Comet.Immutables cometWithExtendedAssetListBlocks

namespace Benchmarks.CompoundIII.Comet

set_option maxRecDepth 10000

set_option maxHeartbeats 1000000 in
theorem cometPauseDecode {v : CometWithExtendedAssetListImmutables}
    {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem rdata : ByteArray} {aw : UInt256}
    {σ : AccountMap} {k C : Nat} {R : List UInt256}
    (hstack : R.length + 8 ≤ 1024)
    (h : RD (deployedRuntime v) ee g s0 ⟨3380⟩ R mem aw rdata σ k C) :
    if PauseCanonical ee.calldata then
      ∃ k' C', RD (deployedRuntime v) ee g s0 ⟨3431⟩
        (boolWord (pauseInputs ee.calldata).buy :: boolWord (pauseInputs ee.calldata).withdraw ::
          boolWord (pauseInputs ee.calldata).supply :: boolWord (pauseInputs ee.calldata).transfer ::
          boolWord (pauseInputs ee.calldata).absorb :: R) mem aw rdata σ k' C'
    else RDrev (deployedRuntime v) g s0 := by
  have rd1 := cometWithExtendedAssetList_block_3380 (immWords := wordsOf (immStore v))
    (by omega) (by rw [cometWithExtendedAssetListPatchedValidJumpsRuntime v]; jump_dest) h
  by_cases h0 : BoolCanonical (calldataWord ee.calldata 4)
  · obtain ⟨k2, C2, rd2⟩ := cometDecodeBool_ok (v := v) (ee := ee)
      (off := UInt256.ofNat 4) (ret := UInt256.ofNat 3389)
      (by change R.length + 0 + 4 ≤ 1024; omega)
      (by change BoolCanonical (calldataWord ee.calldata 4); exact h0)
      (by rw [cometWithExtendedAssetListPatchedValidJumps v]; jump_dest) rd1
    have rd3 := cometWithExtendedAssetList_block_3389 (immWords := wordsOf (immStore v))
      (by change R.length + 1 + 3 ≤ 1024; omega)
      (by rw [cometWithExtendedAssetListPatchedValidJumpsRuntime v]; jump_dest) rd2
    by_cases h1 : BoolCanonical (calldataWord ee.calldata 36)
    · obtain ⟨k4, C4, rd4⟩ := cometDecodeBool_ok (v := v) (ee := ee)
        (off := UInt256.ofNat 36) (ret := UInt256.ofNat 3399)
        (by change R.length + 1 + 4 ≤ 1024; omega)
        (by change BoolCanonical (calldataWord ee.calldata 36); exact h1)
        (by rw [cometWithExtendedAssetListPatchedValidJumps v]; jump_dest) rd3
      have rd5 := cometWithExtendedAssetList_block_3399 (immWords := wordsOf (immStore v))
        (by change R.length + 2 + 3 ≤ 1024; omega)
        (by rw [cometWithExtendedAssetListPatchedValidJumpsRuntime v]; jump_dest) rd4
      by_cases h2 : BoolCanonical (calldataWord ee.calldata 68)
      · obtain ⟨k6, C6, rd6⟩ := cometDecodeBool_ok (v := v) (ee := ee)
          (off := UInt256.ofNat 68) (ret := UInt256.ofNat 3409)
          (by change R.length + 2 + 4 ≤ 1024; omega)
          (by change BoolCanonical (calldataWord ee.calldata 68); exact h2)
          (by rw [cometWithExtendedAssetListPatchedValidJumps v]; jump_dest) rd5
        have rd7 := cometWithExtendedAssetList_block_3409 (immWords := wordsOf (immStore v))
          (by omega)
          (by rw [cometWithExtendedAssetListPatchedValidJumpsRuntime v]; jump_dest) rd6
        by_cases h3 : BoolCanonical (calldataWord ee.calldata 100)
        · obtain ⟨k8, C8, rd8⟩ := cometDecodeBool_ok (v := v) (ee := ee)
            (off := UInt256.ofNat 100) (ret := UInt256.ofNat 3420)
            (by change R.length + 3 + 4 ≤ 1024; omega)
            (by change BoolCanonical (calldataWord ee.calldata 100); exact h3)
            (by rw [cometWithExtendedAssetListPatchedValidJumps v]; jump_dest) rd7
          have rd9 := cometWithExtendedAssetList_block_3420 (immWords := wordsOf (immStore v))
            (by omega)
            (by rw [cometWithExtendedAssetListPatchedValidJumpsRuntime v]; jump_dest) rd8
          by_cases h4 : BoolCanonical (calldataWord ee.calldata 132)
          · obtain ⟨k10, C10, rd10⟩ := cometDecodeBool_ok (v := v) (ee := ee)
              (off := UInt256.ofNat 132) (ret := UInt256.ofNat 3431)
              (by change R.length + 4 + 4 ≤ 1024; omega)
              (by change BoolCanonical (calldataWord ee.calldata 132); exact h4)
              (by rw [cometWithExtendedAssetListPatchedValidJumps v]; jump_dest) rd9
            rw [if_pos (show PauseCanonical ee.calldata from ⟨h0, h1, h2, h3, h4⟩)]
            refine ⟨k10, C10, ?_⟩
            simpa only [pauseInputs, boolWord_of_canonical h0, boolWord_of_canonical h1,
              boolWord_of_canonical h2, boolWord_of_canonical h3, boolWord_of_canonical h4] using rd10
          · simp only [PauseCanonical, h4, false_and, and_false, if_false]
            exact cometDecodeBool_bad (v := v) (ee := ee)
              (off := UInt256.ofNat 132) (ret := UInt256.ofNat 3431)
              (by change R.length + 4 + 4 ≤ 1024; omega)
              (by change ¬ BoolCanonical (calldataWord ee.calldata 132); exact h4)
              (by rw [cometWithExtendedAssetListPatchedValidJumps v]; jump_dest) rd9
        · simp only [PauseCanonical, h3, false_and, and_false, if_false]
          exact cometDecodeBool_bad (v := v) (ee := ee)
            (off := UInt256.ofNat 100) (ret := UInt256.ofNat 3420)
            (by change R.length + 3 + 4 ≤ 1024; omega)
            (by change ¬ BoolCanonical (calldataWord ee.calldata 100); exact h3)
            (by rw [cometWithExtendedAssetListPatchedValidJumps v]; jump_dest) rd7
      · simp only [PauseCanonical, h2, false_and, and_false, if_false]
        exact cometDecodeBool_bad (v := v) (ee := ee)
          (off := UInt256.ofNat 68) (ret := UInt256.ofNat 3409)
          (by change R.length + 2 + 4 ≤ 1024; omega)
          (by change ¬ BoolCanonical (calldataWord ee.calldata 68); exact h2)
          (by rw [cometWithExtendedAssetListPatchedValidJumps v]; jump_dest) rd5
    · simp only [PauseCanonical, h1, false_and, and_false, if_false]
      exact cometDecodeBool_bad (v := v) (ee := ee)
        (off := UInt256.ofNat 36) (ret := UInt256.ofNat 3399)
        (by change R.length + 1 + 4 ≤ 1024; omega)
        (by change ¬ BoolCanonical (calldataWord ee.calldata 36); exact h1)
        (by rw [cometWithExtendedAssetListPatchedValidJumps v]; jump_dest) rd3
  · simp only [PauseCanonical, h0, false_and, and_false, if_false]
    exact cometDecodeBool_bad (v := v) (ee := ee)
      (off := UInt256.ofNat 4) (ret := UInt256.ofNat 3389)
      (by change R.length + 0 + 4 ≤ 1024; omega)
      (by change ¬ BoolCanonical (calldataWord ee.calldata 4); exact h0)
      (by rw [cometWithExtendedAssetListPatchedValidJumps v]; jump_dest) rd1

end Benchmarks.CompoundIII.Comet
