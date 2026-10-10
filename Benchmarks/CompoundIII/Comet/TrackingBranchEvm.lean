import Benchmarks.CompoundIII.Comet.TrackingUpdateEvm

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach Reasoning.Immutables
open Benchmarks.CompoundIII.Comet.Immutables cometWithExtendedAssetListBlocks

namespace Benchmarks.CompoundIII.Comet

set_option maxRecDepth 2000

theorem cometTrackingSupplyBranch {v : CometWithExtendedAssetListImmutables}
    {ee : ExecutionEnv} {g : Sat256} {s0 evm : State} {mem rdata : ByteArray}
    {aw : UInt256} {σ : AccountMap} {k C : Nat} {elapsed : UInt256} {R : List UInt256}
    (hstack : R.length + 14 ≤ 1024) (hperm : ee.perm = true) (hs : SourceState s0 ee σ evm)
    (h : RD (deployedRuntime v) ee g s0 ⟨8033⟩ (⟨0⟩ :: elapsed :: R) mem aw rdata σ k C) :
    if TrackingBranchValid v false evm elapsed then
      ∃ σ' dummy k' C', SourceState s0 ee σ' (trackingBranchState evm v false elapsed) ∧
        RD (deployedRuntime v) ee g s0 ⟨8097⟩
          (dummy :: elapsed :: ⟨0⟩ :: v.baseMinForRewards :: R) mem aw rdata σ' k' C'
    else RDrev (deployedRuntime v) g s0 := by
  let w1 := solcSlotWordAt ⟨1⟩ σ ee
  let total := totalsPrincipalWord w1 false
  let mask := UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 104))
    (UInt256.ofNat 1)
  have hfield : UInt256.land mask w1 = total := by
    rw [u256_land_comm]
    exact (totalsPrincipalWord_eq w1 false).symm
  have hclean : UInt256.land mask total = total := by
    rw [u256_land_comm]
    exact u256LandMaskCleanOfToNat _ _ (bits := 104) rfl (totalsPrincipalWord_lt _ _)
  dsimp only [mask] at hclean
  obtain ⟨k1, C1, r1⟩ := cometWithExtendedAssetList_block_8033
    (immWords := wordsOf (immStore v)) (by simp only [List.length_cons]; omega)
    (by rw [cometWithExtendedAssetListPatchedValidJumpsRuntime v]; jump_dest) h
  have r2 := cometWithExtendedAssetList_block_7787 (immWords := wordsOf (immStore v))
    (by simp only [List.length_cons]; omega)
    (by rw [cometWithExtendedAssetListPatchedValidJumpsRuntime v]; jump_dest) r1
  change RD _ _ _ _ _ (UInt256.land mask w1 :: ⟨0⟩ :: elapsed :: R) _ _ _ _ _ _ at r2
  rw [hfield] at r2
  by_cases hen : TrackingEnabled v false evm
  · have hle : v.baseMinForRewards.toNat ≤ total.toNat := by
      simpa only [TrackingEnabled, hs.storageRead] using hen
    have r3 := cometWithExtendedAssetList_block_8044_taken (immWords := wordsOf (immStore v))
      (by omega)
      (by rw [wordsOf_immStore_baseMinForRewards, wordOfInt_ofNat_toNat, hclean,
        ult_zero hle]; decide)
      (by rw [cometWithExtendedAssetListPatchedValidJumpsRuntime v]; jump_dest) r2
    simp only [cometWithExtendedAssetList_block_8044_taken_stack,
      wordsOf_immStore_baseMinForRewards, wordOfInt_ofNat_toNat, hclean] at r3
    have hu := cometTrackingSupplyUpdate (v := v) (by simpa using hstack) hperm hs r3
    simpa only [TrackingBranchValid, trackingBranchState, if_pos hen, hs.storageRead] using hu
  · have hlt : total.toNat < v.baseMinForRewards.toNat := by
      have hn : ¬ v.baseMinForRewards.toNat ≤ total.toNat := by
        simpa only [TrackingEnabled, hs.storageRead] using hen
      omega
    have r3 := cometWithExtendedAssetList_block_8044_fallthrough
      (immWords := wordsOf (immStore v)) (by omega)
      (by rw [wordsOf_immStore_baseMinForRewards, wordOfInt_ofNat_toNat, hclean,
        ult_one hlt]; decide) r2
    simp only [cometWithExtendedAssetList_block_8044_fallthrough_stack,
      wordsOf_immStore_baseMinForRewards, wordOfInt_ofNat_toNat, hclean] at r3
    simp only [TrackingBranchValid, trackingBranchState, if_neg hen, if_true]
    exact ⟨σ, total, _, _, hs, r3⟩

theorem cometTrackingBorrowBranch {v : CometWithExtendedAssetListImmutables}
    {ee : ExecutionEnv} {g : Sat256} {s0 evm : State} {mem rdata : ByteArray}
    {aw : UInt256} {σ : AccountMap} {k C : Nat} {elapsed dummy : UInt256} {R : List UInt256}
    (hstack : R.length + 12 ≤ 1024) (hperm : ee.perm = true) (hs : SourceState s0 ee σ evm)
    (h : RD (deployedRuntime v) ee g s0 ⟨8097⟩
      (dummy :: elapsed :: ⟨0⟩ :: v.baseMinForRewards :: R) mem aw rdata σ k C) :
    if TrackingBranchValid v true evm elapsed then
      ∃ σ' a b c k' C', SourceState s0 ee σ' (trackingBranchState evm v true elapsed) ∧
        RD (deployedRuntime v) ee g s0 ⟨8126⟩ (a :: b :: c :: R) mem aw rdata σ' k' C'
    else RDrev (deployedRuntime v) g s0 := by
  let w1 := solcSlotWordAt ⟨1⟩ σ ee
  let total := totalsPrincipalWord w1 true
  let mask := UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 104))
    (UInt256.ofNat 1)
  have hfield : UInt256.land mask (UInt256.shiftRight w1 ⟨104⟩) = total := by
    rw [u256_land_comm]
    exact (totalsPrincipalWord_eq w1 true).symm
  have hclean : UInt256.land mask total = total := by
    rw [u256_land_comm]
    exact u256LandMaskCleanOfToNat _ _ (bits := 104) rfl (totalsPrincipalWord_lt _ _)
  obtain ⟨k1, C1, r1⟩ := cometWithExtendedAssetList_block_8097
    (immWords := wordsOf (immStore v)) (by simp only [List.length_cons]; omega)
    (by rw [cometWithExtendedAssetListPatchedValidJumpsRuntime v]; jump_dest) h
  have r2 := cometWithExtendedAssetList_block_7871 (immWords := wordsOf (immStore v))
    (by simp only [List.length_cons]; omega)
    (by rw [cometWithExtendedAssetListPatchedValidJumpsRuntime v]; jump_dest) r1
  change RD _ _ _ _ _ (UInt256.land mask (UInt256.shiftRight w1 ⟨104⟩) :: ⟨8117⟩ ::
    elapsed :: ⟨0⟩ :: v.baseMinForRewards :: R) _ _ _ _ _ _ at r2
  rw [hfield] at r2
  have r3 := cometWithExtendedAssetList_block_8112 (immWords := wordsOf (immStore v))
    (by simp only [List.length_cons]; omega)
    (by rw [cometWithExtendedAssetListPatchedValidJumpsRuntime v]; jump_dest) r2
  have r4 := cometWithExtendedAssetList_block_7787 (immWords := wordsOf (immStore v))
    (by simp only [List.length_cons]; omega)
    (by rw [cometWithExtendedAssetListPatchedValidJumpsRuntime v]; jump_dest) r3
  change RD _ _ _ _ _ (UInt256.land mask total :: elapsed :: ⟨0⟩ :: v.baseMinForRewards :: R)
    _ _ _ _ _ _ at r4
  rw [hclean] at r4
  by_cases hen : TrackingEnabled v true evm
  · have hle : v.baseMinForRewards.toNat ≤ total.toNat := by
      simpa only [TrackingEnabled, hs.storageRead] using hen
    have r5 := cometWithExtendedAssetList_block_8117_taken (immWords := wordsOf (immStore v))
      (by omega) (by rw [ult_zero hle]; decide)
      (by rw [cometWithExtendedAssetListPatchedValidJumpsRuntime v]; jump_dest) r4
    have hu := cometTrackingBorrowUpdate (v := v) hstack hperm hs r5
    simpa only [TrackingBranchValid, trackingBranchState, if_pos hen, hs.storageRead] using hu
  · have hlt : total.toNat < v.baseMinForRewards.toNat := by
      have hn : ¬ v.baseMinForRewards.toNat ≤ total.toNat := by
        simpa only [TrackingEnabled, hs.storageRead] using hen
      omega
    have r5 := cometWithExtendedAssetList_block_8117_fallthrough
      (immWords := wordsOf (immStore v)) (by omega) (by rw [ult_one hlt]; decide) r4
    simp only [TrackingBranchValid, trackingBranchState, if_neg hen, if_true]
    exact ⟨σ, elapsed, ⟨0⟩, total, _, _, hs, r5⟩

end Benchmarks.CompoundIII.Comet
