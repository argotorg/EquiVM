import Benchmarks.CompoundIII.Comet.AbsorbBalanceModel
import Benchmarks.CompoundIII.Comet.Signed256
import Benchmarks.CompoundIII.Comet.SignedArithmeticEvm
import Benchmarks.CompoundIII.Comet.RuntimeBlocks_050
import Benchmarks.CompoundIII.Comet.RuntimeBlocks_077
import Benchmarks.CompoundIII.Comet.RuntimeBlocks_078
import Benchmarks.CompoundIII.Comet.RuntimeBlocks_079

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach Reasoning.Immutables
open Benchmarks.CompoundIII.Comet.Immutables cometWithExtendedAssetListBlocks

namespace Benchmarks.CompoundIII.Comet

set_option maxRecDepth 2000

theorem cometAbsorbBalance {v : CometWithExtendedAssetListImmutables}
    {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem rdata : ByteArray} {aw : UInt256}
    {σ : AccountMap} {k C : Nat} {i bits reserved old principal price saved delta : UInt256}
    {R : List UInt256} (hstack : R.length + 18 ≤ 1024)
    (h : RD (deployedRuntime v) ee g s0 ⟨17156⟩
      (i :: bits :: reserved :: old :: principal :: price :: saved :: delta :: R)
      mem aw rdata σ k C) :
    if AbsorbBalanceValid v old delta price then
      ∃ k' C', RD (deployedRuntime v) ee g s0 ⟨17240⟩
        (principal :: old :: absorbBalanceWord v old delta price :: price :: saved ::
          collateralBaseScale v :: R) mem aw rdata σ k' C'
    else RDrev (deployedRuntime v) g s0 := by
  have r1 := cometWithExtendedAssetList_block_17156 (immWords := wordsOf (immStore v))
    (by omega) (by rw [cometWithExtendedAssetListPatchedValidJumpsRuntime v]; jump_dest) h
  simp only [cometWithExtendedAssetList_block_17156_stack, wordsOf_immStore_baseScale,
    wordOfInt_ofNat_toNat] at r1
  change RD _ _ _ _ _ (delta :: collateralBaseScale v :: UInt256.ofNat 17219 :: price ::
    UInt256.ofNat 10598 :: UInt256.ofNat 17224 :: UInt256.ofNat 17230 :: old :: principal ::
      price :: saved :: collateralBaseScale v :: R) _ _ _ _ _ _ at r1
  by_cases hm : delta.toNat * (collateralBaseScale v).toNat < UInt256.size
  · obtain ⟨k2, C2, r2⟩ := cometCheckedMul (v := v)
      (by change R.length + 9 + 5 ≤ 1024; omega) hm
      (by rw [cometWithExtendedAssetListPatchedValidJumps v]; jump_dest) r1
    have r3 := cometWithExtendedAssetList_block_17219 (immWords := wordsOf (immStore v))
      (by change R.length + 10 + 1 ≤ 1024; omega)
      (by rw [cometWithExtendedAssetListPatchedValidJumpsRuntime v]; jump_dest) r2
    have hd := cometCheckedDiv (v := v) (by change R.length + 7 + 6 ≤ 1024; omega)
      (by rw [cometWithExtendedAssetListPatchedValidJumps v]; jump_dest) r3
    by_cases hz : price ≠ ⟨0⟩
    · rw [if_pos hz] at hd
      obtain ⟨k4, C4, r4⟩ := hd
      change RD _ _ _ _ _ (absorbDeltaBalance v delta price :: UInt256.ofNat 17224 ::
        UInt256.ofNat 17230 :: old :: principal :: price :: saved :: collateralBaseScale v :: R)
        _ _ _ _ _ _ at r4
      have r5 := cometWithExtendedAssetList_block_10598 (immWords := wordsOf (immStore v))
        (by change R.length + 8 + 1 ≤ 1024; omega)
        (by rw [cometWithExtendedAssetListPatchedValidJumpsRuntime v]; jump_dest) r4
      by_cases hd : (absorbDeltaBalance v delta price).toNat < 2^255
      · obtain ⟨k6, C6, r6⟩ := cometSigned256 (v := v)
          (by change R.length + 6 + 5 ≤ 1024; omega) hd
          (by rw [cometWithExtendedAssetListPatchedValidJumps v]; jump_dest) r5
        have r7 := cometWithExtendedAssetList_block_17224 (immWords := wordsOf (immStore v))
          (by change R.length + 4 + 5 ≤ 1024; omega)
          (by rw [cometWithExtendedAssetListPatchedValidJumpsRuntime v]; jump_dest) r6
        simp only [cometWithExtendedAssetList_block_17224_stack] at r7
        have ha := cometSignedAddNonnegRight (v := v)
          (by change R.length + 5 + 8 ≤ 1024; omega) hd
          (by rw [cometWithExtendedAssetListPatchedValidJumps v]; jump_dest) r7
        by_cases hsum : signedWord old + Int.ofNat (absorbDeltaBalance v delta price).toNat <
            (2^255 : Int)
        · rw [if_pos hsum] at ha
          rw [if_pos (show AbsorbBalanceValid v old delta price from ⟨⟨hm, hz⟩, hd, hsum⟩)]
          obtain ⟨k8, C8, r8⟩ := ha
          change RD _ _ _ _ _ (absorbBalanceSum v old delta price :: old :: principal ::
            price :: saved :: collateralBaseScale v :: R) _ _ _ _ _ _ at r8
          by_cases hp : (absorbBalanceSum v old delta price).toNat < 2^255
          · have hs : UInt256.slt (absorbBalanceSum v old delta price) (UInt256.ofNat 0) =
                UInt256.ofNat 0 := slt_lit_zero (by decide) (Nat.zero_le _) hp
            have r9 := cometWithExtendedAssetList_block_17230_fallthrough
              (immWords := wordsOf (immStore v)) (by change R.length + 3 + 5 ≤ 1024; omega) hs r8
            simpa only [absorbBalanceWord, if_pos hp] using ⟨_, _, r9⟩
          · have hs : UInt256.slt (absorbBalanceSum v old delta price) (UInt256.ofNat 0) ≠
                UInt256.ofNat 0 := u256_slt_zero_ne_zero_of_high (by
                  change 2^255 ≤ (absorbBalanceSum v old delta price).toNat; omega)
            have r9 := cometWithExtendedAssetList_block_17230_taken
              (immWords := wordsOf (immStore v)) (by change R.length + 3 + 5 ≤ 1024; omega) hs
              (by rw [cometWithExtendedAssetListPatchedValidJumpsRuntime v]; jump_dest) r8
            have r10 := cometWithExtendedAssetList_block_17542 (immWords := wordsOf (immStore v))
              (by change R.length + 3 + 4 ≤ 1024; omega)
              (by rw [cometWithExtendedAssetListPatchedValidJumpsRuntime v]; jump_dest) r9
            simpa only [absorbBalanceWord, if_neg hp] using ⟨_, _, r10⟩
        · rw [if_neg hsum] at ha
          rw [if_neg (fun hv ↦ hsum hv.2.2)]
          exact ha
      · rw [if_neg (fun hv ↦ hd hv.2.1)]
        exact cometSigned256_revert (v := v) (by change R.length + 6 + 5 ≤ 1024; omega) hd r5
    · rw [if_neg hz] at hd
      rw [if_neg (fun hv ↦ hz hv.1.2)]
      exact hd
  · rw [if_neg (fun hv ↦ hm hv.1.1)]
    exact cometCheckedMul_revert (v := v)
      (by change R.length + 10 + 4 ≤ 1024; omega) (le_of_not_gt hm) r1

end Benchmarks.CompoundIII.Comet
