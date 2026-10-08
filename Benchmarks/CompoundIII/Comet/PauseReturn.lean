import Benchmarks.CompoundIII.Comet.PauseFlagsEvm
import Benchmarks.CompoundIII.Comet.PauseStatic

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach Reasoning.Immutables
open Benchmarks.CompoundIII.Comet.Immutables cometWithExtendedAssetListBlocks

namespace Benchmarks.CompoundIII.Comet

set_option maxRecDepth 10000

theorem cometPauseReturn {v : CometWithExtendedAssetListImmutables}
    {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem rdata : ByteArray} {aw : UInt256}
    {σ : AccountMap} {k C : Nat} {R : List UInt256} (a : PauseInputs)
    (hstack : R.length + 15 ≤ 1024)
    (h : RD (deployedRuntime v) ee g s0 ⟨3489⟩
      (boolWord a.buy :: boolWord a.withdraw :: boolWord a.supply :: boolWord a.transfer ::
        boolWord a.absorb :: R) mem aw rdata σ k C) :
    if ee.perm = true then RDret (deployedRuntime v) g s0 (pauseAccounts σ ee a) ByteArray.empty
    else RDstatic (deployedRuntime v) g s0 := by
  obtain ⟨k1, C1, rd1⟩ := cometPauseFlags (v := v) a hstack h
  by_cases hp : ee.perm = true
  · rw [if_pos hp]
    obtain ⟨k2, C2, rd2⟩ := cometWithExtendedAssetList_block_11083
      (immWords := wordsOf (immStore v)) (by change R.length + 7 + 7 ≤ 1024; omega) hp
      (by rw [cometWithExtendedAssetListPatchedValidJumpsRuntime v]; jump_dest) rd1
    have rd3 := cometWithExtendedAssetList_block_3624
      (immWords := wordsOf (immStore v)) (by change R.length + 1 + 12 ≤ 1024; omega)
      (by rw [cometWithExtendedAssetListPatchedValidJumpsRuntime v]; jump_dest) rd2
    exact cometWithExtendedAssetList_block_3677 (immWords := wordsOf (immStore v))
      (by omega) hp rd3
  · rw [if_neg hp]
    exact cometStorePauseStatic (v := v) (by change R.length + 7 + 7 ≤ 1024; omega)
      (Bool.eq_false_iff.mpr hp) rd1

end Benchmarks.CompoundIII.Comet
