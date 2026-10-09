import Benchmarks.CompoundIII.Comet.TrackingIncrementEvm

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach Reasoning.Immutables
open Benchmarks.CompoundIII.Comet.Immutables cometWithExtendedAssetListBlocks

namespace Benchmarks.CompoundIII.Comet

set_option maxRecDepth 2000

theorem cometTrackingSupplyUpdate {v : CometWithExtendedAssetListImmutables}
    {ee : ExecutionEnv} {g : Sat256} {s0 evm : State} {mem rdata : ByteArray}
    {aw : UInt256} {σ : AccountMap} {k C : Nat} {elapsed : UInt256} {R : List UInt256}
    (hstack : R.length + 13 ≤ 1024) (hperm : ee.perm = true) (hs : SourceState s0 ee σ evm)
    (h : RD (deployedRuntime v) ee g s0 ⟨8289⟩
      (totalsPrincipalWord (solcSlotWordAt ⟨1⟩ σ ee) false :: elapsed :: ⟨0⟩ :: R)
      mem aw rdata σ k C) :
    if TrackingAccrualValid v false (solcSlotWordAt ⟨0⟩ σ ee) (solcSlotWordAt ⟨1⟩ σ ee)
        elapsed then
      ∃ σ' dummy k' C', SourceState s0 ee σ' (trackingAccrualState evm v false elapsed) ∧
        RD (deployedRuntime v) ee g s0 ⟨8097⟩ (dummy :: elapsed :: ⟨0⟩ :: R)
          mem aw rdata σ' k' C'
    else RDrev (deployedRuntime v) g s0 := by
  let w0 := solcSlotWordAt ⟨0⟩ σ ee
  let w1 := solcSlotWordAt ⟨1⟩ σ ee
  let total := totalsPrincipalWord w1 false
  let inc := trackingIncrement v false total elapsed
  let idx := trackingIndexWord w0 false
  have r1 := cometWithExtendedAssetList_block_8289 (immWords := wordsOf (immStore v))
    (by simp only [List.length_cons]; omega)
    (by rw [cometWithExtendedAssetListPatchedValidJumpsRuntime v]; jump_dest) h
  simp only [cometWithExtendedAssetList_block_8289_stack,
    wordsOf_immStore_baseTrackingSupplySpeed, wordOfInt_ofNat_toNat] at r1
  have hi := cometTrackingIncrement (v := v) (borrow := false)
    (by simpa using hstack)
    (by rw [cometWithExtendedAssetListPatchedValidJumps v]; jump_dest) r1
  by_cases hv : TrackingIncrementValid v false total elapsed
  · rw [if_pos hv] at hi
    obtain ⟨k2, C2, r2⟩ := hi
    obtain ⟨k3, C3, r3⟩ := cometWithExtendedAssetList_block_8344
      (immWords := wordsOf (immStore v)) (by omega)
      (by rw [cometWithExtendedAssetListPatchedValidJumpsRuntime v]; jump_dest) r2
    change RD _ _ _ _ _
      (UInt256.land ⟨2^64-1⟩ (UInt256.shiftRight w0 ⟨128⟩) :: inc ::
        ⟨8363⟩ :: ⟨8401⟩ :: elapsed :: ⟨0⟩ :: R) _ _ _ _ _ _ at r3
    have hidx : UInt256.land ⟨2^64-1⟩ (UInt256.shiftRight w0 ⟨128⟩) = idx := by
      rw [u256_land_comm]
      exact (trackingIndexWord_eq w0 false).symm
    rw [hidx] at r3
    by_cases hadd : idx.toNat + inc.toNat < 2^64
    · obtain ⟨k4, C4, r4⟩ := cometCheckedAdd64 (v := v)
        (by simp only [List.length_cons]; omega) (trackingIndexWord_lt _ _) hv.2.2 hadd
        (by rw [cometWithExtendedAssetListPatchedValidJumps v]; jump_dest) r3
      obtain ⟨k5, C5, r5⟩ := cometWithExtendedAssetList_block_8363
        (immWords := wordsOf (immStore v)) (by omega) hperm
        (by rw [cometWithExtendedAssetListPatchedValidJumpsRuntime v]; jump_dest) r4
      let σ' := sstoreAccountMap ee.codeOwner σ ⟨0⟩ (uint64FieldWrite w0 (idx + inc) 2)
      change RD _ _ _ _ _ (elapsed :: ⟨0⟩ :: R) mem aw rdata σ' _ _ at r5
      have r6 := cometWithExtendedAssetList_block_8401 (immWords := wordsOf (immStore v))
        (by simp only [List.length_cons]; omega)
        (by rw [cometWithExtendedAssetListPatchedValidJumpsRuntime v]; jump_dest) r5
      have hs' := sourceState_storeTrackingIndex hs false (idx + inc)
      rw [if_pos (show TrackingAccrualValid v false w0 w1 elapsed from ⟨hv, hadd⟩)]
      refine ⟨σ', _, _, _, ?_, r6⟩
      simpa only [trackingAccrualState, hs.storageRead] using hs'
    · rw [if_neg (show ¬ TrackingAccrualValid v false w0 w1 elapsed from fun h ↦ hadd h.2)]
      exact cometCheckedAdd64_revert (v := v) (by simp only [List.length_cons]; omega)
        (trackingIndexWord_lt _ _) hv.2.2 (le_of_not_gt hadd) r3
  · rw [if_neg hv] at hi
    rw [if_neg (show ¬ TrackingAccrualValid v false w0 w1 elapsed from fun h ↦ hv h.1)]
    exact hi

theorem cometTrackingBorrowUpdate {v : CometWithExtendedAssetListImmutables}
    {ee : ExecutionEnv} {g : Sat256} {s0 evm : State} {mem rdata : ByteArray}
    {aw : UInt256} {σ : AccountMap} {k C : Nat} {elapsed : UInt256} {R : List UInt256}
    (hstack : R.length + 12 ≤ 1024) (hperm : ee.perm = true) (hs : SourceState s0 ee σ evm)
    (h : RD (deployedRuntime v) ee g s0 ⟨8169⟩
      (elapsed :: ⟨0⟩ :: totalsPrincipalWord (solcSlotWordAt ⟨1⟩ σ ee) true :: R)
      mem aw rdata σ k C) :
    if TrackingAccrualValid v true (solcSlotWordAt ⟨0⟩ σ ee) (solcSlotWordAt ⟨1⟩ σ ee)
        elapsed then
      ∃ σ' a b c k' C', SourceState s0 ee σ' (trackingAccrualState evm v true elapsed) ∧
        RD (deployedRuntime v) ee g s0 ⟨8126⟩ (a :: b :: c :: R) mem aw rdata σ' k' C'
    else RDrev (deployedRuntime v) g s0 := by
  let w0 := solcSlotWordAt ⟨0⟩ σ ee
  let w1 := solcSlotWordAt ⟨1⟩ σ ee
  let total := totalsPrincipalWord w1 true
  let inc := trackingIncrement v true total elapsed
  let idx := trackingIndexWord w0 true
  have r1 := cometWithExtendedAssetList_block_8169 (immWords := wordsOf (immStore v))
    (by omega)
    (by rw [cometWithExtendedAssetListPatchedValidJumpsRuntime v]; jump_dest) h
  simp only [cometWithExtendedAssetList_block_8169_stack,
    wordsOf_immStore_baseTrackingBorrowSpeed, wordOfInt_ofNat_toNat] at r1
  have hi := cometTrackingIncrement (v := v) (borrow := true)
    (by simpa using hstack)
    (by rw [cometWithExtendedAssetListPatchedValidJumps v]; jump_dest) r1
  by_cases hv : TrackingIncrementValid v true total elapsed
  · rw [if_pos hv] at hi
    obtain ⟨k2, C2, r2⟩ := hi
    obtain ⟨k3, C3, r3⟩ := cometWithExtendedAssetList_block_8234
      (immWords := wordsOf (immStore v)) (by simp only [List.length_cons]; omega)
      (by rw [cometWithExtendedAssetListPatchedValidJumpsRuntime v]; jump_dest) r2
    change RD _ _ _ _ _
      (UInt256.shiftRight w0 ⟨192⟩ :: inc :: ⟨8249⟩ :: ⟨0⟩ :: ⟨8281⟩ :: R) _ _ _ _ _ _ at r3
    have hidx : UInt256.shiftRight w0 ⟨192⟩ = idx := (trackingIndexWord_eq w0 true).symm
    rw [hidx] at r3
    by_cases hadd : idx.toNat + inc.toNat < 2^64
    · obtain ⟨k4, C4, r4⟩ := cometCheckedAdd64 (v := v)
        (by simp only [List.length_cons]; omega) (trackingIndexWord_lt _ _) hv.2.2 hadd
        (by rw [cometWithExtendedAssetListPatchedValidJumps v]; jump_dest) r3
      obtain ⟨k5, C5, r5⟩ := cometWithExtendedAssetList_block_8249
        (immWords := wordsOf (immStore v)) (by omega) hperm
        (by rw [cometWithExtendedAssetListPatchedValidJumpsRuntime v]; jump_dest) r4
      let σ' := sstoreAccountMap ee.codeOwner σ ⟨0⟩ (uint64FieldWrite w0 (idx + inc) 3)
      change RD _ _ _ _ _ R mem aw rdata σ' _ _ at r5
      have r6 := cometWithExtendedAssetList_block_8281 (immWords := wordsOf (immStore v))
        (by omega)
        (by rw [cometWithExtendedAssetListPatchedValidJumpsRuntime v]; jump_dest) r5
      have hs' := sourceState_storeTrackingIndex hs true (idx + inc)
      rw [if_pos (show TrackingAccrualValid v true w0 w1 elapsed from ⟨hv, hadd⟩)]
      refine ⟨σ', _, _, _, _, _, ?_, r6⟩
      simpa only [trackingAccrualState, hs.storageRead] using hs'
    · rw [if_neg (show ¬ TrackingAccrualValid v true w0 w1 elapsed from fun h ↦ hadd h.2)]
      exact cometCheckedAdd64_revert (v := v) (by simp only [List.length_cons]; omega)
        (trackingIndexWord_lt _ _) hv.2.2 (le_of_not_gt hadd) r3
  · rw [if_neg hv] at hi
    rw [if_neg (show ¬ TrackingAccrualValid v true w0 w1 elapsed from fun h ↦ hv h.1)]
    exact hi

end Benchmarks.CompoundIII.Comet
