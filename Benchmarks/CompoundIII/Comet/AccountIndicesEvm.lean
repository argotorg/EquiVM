import Benchmarks.CompoundIII.Comet.CurrentIndicesEvm
import Benchmarks.CompoundIII.Comet.RuntimeBlocks_081

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables
open Benchmarks.CompoundIII.Comet.Immutables
open cometWithExtendedAssetListBlocks

namespace Benchmarks.CompoundIII.Comet

set_option maxRecDepth 10000

theorem cometAccountIndices {v : CometWithExtendedAssetListImmutables}
    {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem rdata : ByteArray}
    {aw ret : UInt256} {σ : AccountMap} {k C : Nat} {R : List UInt256}
    (hstack : R.length + 32 ≤ 1024)
    (hret : (D_J (deployedRuntime v) 0).contains ret = true)
    (h : RD (deployedRuntime v) ee g s0 ⟨7614⟩ (⟨18263⟩ :: ret :: R)
      mem aw rdata σ k C) :
    let w0 := solcSlotWordAt ⟨0⟩ σ ee
    let w1 := solcSlotWordAt ⟨1⟩ σ ee
    if CurrentIndicesValid v w0 w1 (timestampWord ee) then
      ∃ k' C', RD (deployedRuntime v) ee g s0 ret
        (currentIndex v w0 w1 (timestampWord ee) true ::
          currentIndex v w0 w1 (timestampWord ee) false :: R) mem aw rdata σ k' C'
    else RDrev (deployedRuntime v) g s0 := by
  dsimp only
  by_cases ht : (timestampWord ee).toNat < 2^40
  · obtain ⟨k1, C1, r1⟩ := cometNow (v := v)
      (by simp only [List.length_cons]; omega) ht
      (by rw [cometWithExtendedAssetListPatchedValidJumps v]; jump_dest) h
    obtain ⟨k2, C2, r2⟩ := cometWithExtendedAssetList_block_18263
      (immWords := wordsOf (immStore v)) (by simp only [List.length_cons]; omega)
      (by rw [cometWithExtendedAssetListPatchedValidJumpsRuntime v]; jump_dest) r1
    change RD _ _ _ _ _
      (timestampWord ee :: UInt256.land
        (UInt256.shiftRight (solcSlotWordAt ⟨1⟩ σ ee) ⟨208⟩) ⟨1099511627775⟩ ::
        ⟨1707⟩ :: ⟨1099511627775⟩ :: ret :: R) _ _ _ _ _ _ at r2
    rw [← lastAccrualWord_eq] at r2
    exact cometCurrentIndicesAfterLoad (v := v) hstack ht hret r2
  · rw [if_neg (show ¬ CurrentIndicesValid v _ _ (timestampWord ee) from fun h ↦ ht h.1)]
    exact cometNow_revert (v := v) (by simp only [List.length_cons]; omega) ht h

end Benchmarks.CompoundIII.Comet
