import Benchmarks.CompoundIII.Comet.AssetMembershipControl

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach Reasoning.Immutables
open Benchmarks.CompoundIII.Comet.Immutables cometWithExtendedAssetListBlocks

namespace Benchmarks.CompoundIII.Comet

set_option maxRecDepth 2000

theorem cometUpdateAssetsIn {v : CometWithExtendedAssetListImmutables}
    {ee : ExecutionEnv} {g : Sat256} {s0 evm : State} {mem rdata : ByteArray}
    {aw offset ptr initial final ret : UInt256} {σ : AccountMap} {k C : Nat} {R : List UInt256}
    (account : AccountAddress) (hstack : R.length + 14 ≤ 1024)
    (hoffset : memLoad ptr mem = offset) (ho : offset.toNat < 256)
    (hi : initial.toNat < 2^128) (hf : final.toNat < 2^128)
    (hret : (D_J (deployedRuntime v) 0).contains ret = true) (hs : SourceState s0 ee σ evm)
    (h : RD (deployedRuntime v) ee g s0 ⟨14132⟩
      (EVM.word account.val :: ptr :: initial :: final :: ret :: R) mem aw rdata σ k C) :
    AssetMembershipRun v ee g s0 mem rdata account ret R
      (assetMembershipResult evm account offset initial final) := by
  let mask := UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 128))
    (UInt256.ofNat 1)
  have hci : UInt256.land mask initial = initial := by
    rw [u256_land_comm]; exact u256LandMaskCleanOfToNat _ _ (bits := 128) rfl hi
  have hcf : UInt256.land final mask = final :=
    u256LandMaskCleanOfToNat _ _ (bits := 128) rfl hf
  have hco : UInt256.land (UInt256.ofNat 255) offset = offset := by
    rw [u256_land_comm]; exact u256LandMaskCleanOfToNat _ _ (bits := 8) rfl ho
  by_cases hi0 : initial = ⟨0⟩
  · have r1 := cometWithExtendedAssetList_block_14132_taken
      (immWords := wordsOf (immStore v)) (by change R.length + 1 + 8 ≤ 1024; omega)
      (by change UInt256.isZero (UInt256.land mask initial) ≠ UInt256.ofNat 0
          rw [hci, hi0]; decide)
      (by rw [cometWithExtendedAssetListPatchedValidJumpsRuntime v]; jump_dest) h
    change RD _ _ _ _ _
      (UInt256.isZero (UInt256.land mask initial) ::
        UInt256.isZero (UInt256.land mask initial) :: mask :: final ::
        EVM.word account.val :: ptr :: ret :: R) _ _ _ _ _ _ at r1
    rw [hci, hi0] at r1
    have r2 := cometWithExtendedAssetList_block_14485
      (immWords := wordsOf (immStore v)) (by change R.length + 3 + 5 ≤ 1024; omega)
      (by rw [cometWithExtendedAssetListPatchedValidJumpsRuntime v]; jump_dest) r1
    dsimp only [cometWithExtendedAssetList_block_14485_stack] at r2
    rw [hcf] at r2
    by_cases hf0 : final = ⟨0⟩
    · have r3 := cometWithExtendedAssetList_block_14155_taken
        (immWords := wordsOf (immStore v)) (by change R.length + 6 + 2 ≤ 1024; omega)
        (by rw [hf0]; decide)
        (by rw [cometWithExtendedAssetListPatchedValidJumpsRuntime v]; jump_dest) r2
      have r4 := cometWithExtendedAssetList_block_14321_fallthrough
        (immWords := wordsOf (immStore v)) (by change R.length + 3 + 5 ≤ 1024; omega)
        (by decide) r3
      have r5 := cometWithExtendedAssetList_block_14329_fallthrough
        (immWords := wordsOf (immStore v)) (by change R.length + 3 + 3 ≤ 1024; omega)
        (by decide) r4
      have r6 := cometWithExtendedAssetList_block_14336
        (immWords := wordsOf (immStore v)) (by omega) hret r5
      refine ⟨mem, Or.inl rfl, ?_⟩
      simp only [assetMembershipResult, assetMembershipChange, if_pos hi0, if_pos hf0]
      exact ⟨σ, _, _, _, hs, r6⟩
    · have r3 := cometWithExtendedAssetList_block_14155_fallthrough
        (immWords := wordsOf (immStore v)) (by change R.length + 6 + 2 ≤ 1024; omega)
        (by rw [isZero_eq_zero_of_ne hf0]; decide) r2
      have r4 := cometWithExtendedAssetList_block_14161
        (immWords := wordsOf (immStore v)) (by change R.length + 1 + 5 ≤ 1024; omega)
        (by rw [cometWithExtendedAssetListPatchedValidJumpsRuntime v]; jump_dest) r3
      dsimp only [cometWithExtendedAssetList_block_14161_stack] at r4
      rw [hoffset, hco] at r4
      simp only [assetMembershipResult, assetMembershipChange, if_pos hi0, if_neg hf0]
      exact cometMembershipChange (v := v) account true hstack hoffset ho hret hs r4
  · have r1 := cometWithExtendedAssetList_block_14132_fallthrough
      (immWords := wordsOf (immStore v)) (by change R.length + 1 + 8 ≤ 1024; omega)
      (by change UInt256.isZero (UInt256.land mask initial) = UInt256.ofNat 0
          rw [hci]; exact isZero_eq_zero_of_ne hi0) h
    change RD _ _ _ _ _
      (UInt256.isZero (UInt256.land mask initial) ::
        UInt256.isZero (UInt256.land mask initial) :: mask :: final ::
        EVM.word account.val :: ptr :: ret :: R) _ _ _ _ _ _ at r1
    rw [hci, isZero_eq_zero_of_ne hi0] at r1
    have r2 := cometWithExtendedAssetList_block_14155_taken
      (immWords := wordsOf (immStore v)) (by change R.length + 6 + 2 ≤ 1024; omega)
      (by decide) (by rw [cometWithExtendedAssetListPatchedValidJumpsRuntime v]; jump_dest) r1
    have r3 := cometWithExtendedAssetList_block_14321_taken
      (immWords := wordsOf (immStore v)) (by change R.length + 3 + 5 ≤ 1024; omega)
      (by decide) (by rw [cometWithExtendedAssetListPatchedValidJumpsRuntime v]; jump_dest) r2
    have r4 := cometWithExtendedAssetList_block_14474
      (immWords := wordsOf (immStore v)) (by change R.length + 3 + 4 ≤ 1024; omega)
      (by rw [cometWithExtendedAssetListPatchedValidJumpsRuntime v]; jump_dest) r3
    dsimp only [cometWithExtendedAssetList_block_14474_stack] at r4
    rw [hcf] at r4
    by_cases hf0 : final = ⟨0⟩
    · have r5 := cometWithExtendedAssetList_block_14329_taken
        (immWords := wordsOf (immStore v)) (by change R.length + 3 + 3 ≤ 1024; omega)
        (by rw [hf0]; decide)
        (by rw [cometWithExtendedAssetListPatchedValidJumpsRuntime v]; jump_dest) r4
      simp only [assetMembershipResult, assetMembershipChange, if_neg hi0, if_pos hf0]
      exact cometMembershipChange (v := v) account false hstack hoffset ho hret hs r5
    · have r5 := cometWithExtendedAssetList_block_14329_fallthrough
        (immWords := wordsOf (immStore v)) (by change R.length + 3 + 3 ≤ 1024; omega)
        (isZero_eq_zero_of_ne hf0) r4
      have r6 := cometWithExtendedAssetList_block_14336
        (immWords := wordsOf (immStore v)) (by omega) hret r5
      refine ⟨mem, Or.inl rfl, ?_⟩
      simp only [assetMembershipResult, assetMembershipChange, if_neg hi0, if_neg hf0]
      exact ⟨σ, _, _, _, hs, r6⟩

end Benchmarks.CompoundIII.Comet
