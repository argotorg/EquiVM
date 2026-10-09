import Benchmarks.CompoundIII.Comet.CurrentIndicesEvm
import Benchmarks.CompoundIII.Comet.RuntimeBlocks_047

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach Reasoning.Immutables
open Benchmarks.CompoundIII.Comet.Immutables cometWithExtendedAssetListBlocks

namespace Benchmarks.CompoundIII.Comet

set_option maxRecDepth 10000

theorem cometReservesStart {v : CometWithExtendedAssetListImmutables}
    {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem rdata : ByteArray} {aw ret : UInt256}
    {σ : AccountMap} {k C : Nat} {R : List UInt256}
    (hstack : R.length + 35 ≤ 1024)
    (h : RD (deployedRuntime v) ee g s0 ⟨9825⟩ (ret :: R) mem aw rdata σ k C) :
    let w0 := solcSlotWordAt ⟨0⟩ σ ee
    let w1 := solcSlotWordAt ⟨1⟩ σ ee
    let time := timestampWord ee
    if CurrentIndicesValid v w0 w1 time then
      ∃ k' C', RD (deployedRuntime v) ee g s0 ⟨9871⟩
        (currentIndex v w0 w1 time true :: currentIndex v w0 w1 time false ::
          w1 :: ⟨2425⟩ :: ret :: R) mem aw rdata σ k' C'
    else RDrev (deployedRuntime v) g s0 := by
  dsimp only
  let w0 := solcSlotWordAt ⟨0⟩ σ ee
  let w1 := solcSlotWordAt ⟨1⟩ σ ee
  let time := timestampWord ee
  have r0 := cometWithExtendedAssetList_block_9825
    (immWords := wordsOf (immStore v)) (by change R.length + 1 + 3 ≤ 1024; omega)
    (by rw [cometWithExtendedAssetListPatchedValidJumpsRuntime v]; jump_dest) h
  by_cases ht : time.toNat < 2^40
  · obtain ⟨k1, C1, r1⟩ := cometNow (v := v)
      (by change R.length + 2 + 3 ≤ 1024; omega) ht
      (by rw [cometWithExtendedAssetListPatchedValidJumps v]; jump_dest) r0
    obtain ⟨k2, C2, r2⟩ := cometWithExtendedAssetList_block_9836
      (immWords := wordsOf (immStore v)) (by change R.length + 2 + 8 ≤ 1024; omega)
      (by rw [cometWithExtendedAssetListPatchedValidJumpsRuntime v]; jump_dest) r1
    change RD _ _ _ _ _ (time :: UInt256.land (UInt256.shiftRight w1 ⟨208⟩) ⟨1099511627775⟩ ::
      ⟨7926⟩ :: ⟨9866⟩ :: ⟨9871⟩ :: w1 :: ⟨2425⟩ :: ret :: R) _ _ _ _ _ _ at r2
    rw [← lastAccrualWord_eq] at r2
    by_cases hle : (lastAccrualWord w1).toNat ≤ time.toNat
    · obtain ⟨k3, C3, r3⟩ := cometCheckedSub40 (v := v)
        (by change R.length + 5 + 5 ≤ 1024; omega) ht (lastAccrualWord_lt _) hle
        (by rw [cometWithExtendedAssetListPatchedValidJumps v]; jump_dest) r2
      have hdt := currentElapsed_lt ht hle
      have r4 := cometWithExtendedAssetList_block_7926
        (immWords := wordsOf (immStore v)) (by change R.length + 4 + 3 ≤ 1024; omega)
        (by rw [cometWithExtendedAssetListPatchedValidJumpsRuntime v]; jump_dest) r3
      change RD _ _ _ _ _ (UInt256.land (UInt256.ofNat 1099511627775)
        (currentElapsed time w1) :: ⟨9871⟩ :: w1 :: ⟨2425⟩ :: ret :: R) _ _ _ _ _ _ at r4
      rw [mask40Clean _ hdt] at r4
      have r5 := cometWithExtendedAssetList_block_9866
        (immWords := wordsOf (immStore v)) (by change R.length + 5 + 1 ≤ 1024; omega)
        (by rw [cometWithExtendedAssetListPatchedValidJumpsRuntime v]; jump_dest) r4
      have hr := cometAccruedIndices (v := v) (elapsed := currentElapsed time w1)
        (by change R.length + 3 + 32 ≤ 1024; omega) hdt
        (by rw [cometWithExtendedAssetListPatchedValidJumps v]; jump_dest) r5
      dsimp only at hr
      by_cases hv : AccruedIndicesValid v w0 w1 (currentElapsed time w1)
      · rw [if_pos hv] at hr
        rw [if_pos (show CurrentIndicesValid v w0 w1 time from ⟨ht, hle, hv⟩)]
        exact hr
      · rw [if_neg hv] at hr
        rw [if_neg (show ¬ CurrentIndicesValid v w0 w1 time from fun h ↦ hv h.2.2)]
        exact hr
    · rw [if_neg (show ¬ CurrentIndicesValid v w0 w1 time from fun h ↦ hle h.2.1)]
      exact cometCheckedSub40_revert (v := v)
        (by change R.length + 6 + 4 ≤ 1024; omega) ht (lastAccrualWord_lt _)
        (Nat.lt_of_not_ge hle) r2
  · rw [if_neg (show ¬ CurrentIndicesValid v w0 w1 time from fun h ↦ ht h.1)]
    exact cometNow_revert (v := v) (by change R.length + 3 + 3 ≤ 1024; omega) ht r0

end Benchmarks.CompoundIII.Comet
