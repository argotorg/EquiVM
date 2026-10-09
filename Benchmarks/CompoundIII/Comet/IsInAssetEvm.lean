import Benchmarks.CompoundIII.Comet.BitMembershipWords
import Benchmarks.CompoundIII.Comet.RuntimeBlocks_054

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach Reasoning.Immutables
open Benchmarks.CompoundIII.Comet.Immutables cometWithExtendedAssetListBlocks

namespace Benchmarks.CompoundIII.Comet

set_option maxRecDepth 2000

theorem cometIsInAsset {v : CometWithExtendedAssetListImmutables}
    {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem rdata : ByteArray}
    {aw assets offset reserved ret : UInt256} {σ : AccountMap} {k C : Nat} {R : List UInt256}
    (hstack : R.length + 7 ≤ 1024)
    (ha : assets.toNat < 2^16) (ho : offset.toNat < 2^8) (hr : reserved.toNat < 2^8)
    (hret : (D_J (deployedRuntime v) 0).contains ret = true)
    (h : RD (deployedRuntime v) ee g s0 ⟨11456⟩
      (assets :: offset :: reserved :: ret :: R) mem aw rdata σ k C) :
    ∃ k' C', RD (deployedRuntime v) ee g s0 ret
      (boolWord (isInAssetBool assets offset reserved) :: R) mem aw rdata σ k' C' := by
  have hc : UInt256.land (UInt256.ofNat 255) offset = offset := by
    rw [u256_land_comm]
    exact u256LandMaskCleanOfToNat _ _ (bits := 8) rfl ho
  by_cases h16 : offset.toNat < 16
  · rw [isInAssetBool, if_pos h16]
    have r1 := cometWithExtendedAssetList_block_11456_fallthrough
      (immWords := wordsOf (immStore v)) (by simpa only [List.length_cons] using
        (show R.length + 1 + 5 ≤ 1024 by omega))
      (by rw [hc, ult_one h16]; decide) h
    dsimp only [cometWithExtendedAssetList_block_11456_fallthrough_stack] at r1
    rw [hc] at r1
    have r2 := cometWithExtendedAssetList_block_11473
      (immWords := wordsOf (immStore v)) (by omega) hret r1
    dsimp only [cometWithExtendedAssetList_block_11473_stack] at r2
    rw [bitMembership_word assets offset (UInt256.ofNat 65535) 16 ha (by omega) rfl] at r2
    exact ⟨_, _, r2⟩
  · rw [isInAssetBool, if_neg h16]
    have r1 := cometWithExtendedAssetList_block_11456_taken
      (immWords := wordsOf (immStore v)) (by simpa only [List.length_cons] using
        (show R.length + 1 + 5 ≤ 1024 by omega))
      (by rw [hc, ult_zero (by change 16 ≤ offset.toNat; omega)]; decide)
      (by rw [cometWithExtendedAssetListPatchedValidJumpsRuntime v]; jump_dest) h
    dsimp only [cometWithExtendedAssetList_block_11456_taken_stack] at r1
    rw [hc] at r1
    by_cases h24 : offset.toNat < 24
    · rw [if_pos h24]
      have r2 := cometWithExtendedAssetList_block_11487_taken
        (immWords := wordsOf (immStore v)) (by simp only [List.length_cons]; omega)
        (by rw [ult_one h24]; decide)
        (by rw [cometWithExtendedAssetListPatchedValidJumpsRuntime v]; jump_dest) r1
      have r3 := cometWithExtendedAssetList_block_11504
        (immWords := wordsOf (immStore v)) hstack hret r2
      dsimp only [cometWithExtendedAssetList_block_11504_stack] at r3
      rw [isInAssetOffset_word offset (by omega) h24] at r3
      have hd : (UInt256.ofNat (offset.toNat - 16)).toNat = offset.toNat - 16 :=
        UInt256.toNat_ofNat_of_lt (by change offset.toNat - 16 < 2^256; omega)
      rw [bitMembership_word reserved (UInt256.ofNat (offset.toNat - 16))
        (UInt256.ofNat 255) 8 hr (by rw [hd]; omega) rfl, hd] at r3
      exact ⟨_, _, r3⟩
    · rw [if_neg h24]
      have r2 := cometWithExtendedAssetList_block_11487_fallthrough
        (immWords := wordsOf (immStore v)) (by simp only [List.length_cons]; omega)
        (ult_zero (by change 24 ≤ offset.toNat; omega)) r1
      have r3 := cometWithExtendedAssetList_block_11498
        (immWords := wordsOf (immStore v)) (by omega) hret r2
      exact ⟨_, _, r3⟩

end Benchmarks.CompoundIII.Comet
