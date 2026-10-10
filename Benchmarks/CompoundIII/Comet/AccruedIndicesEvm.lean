import Benchmarks.CompoundIII.Comet.AccruedIndicesModel
import Benchmarks.CompoundIII.Comet.IndexAccrualEvm
import Benchmarks.CompoundIII.Comet.UtilizationEvm
import Benchmarks.CompoundIII.Comet.SupplyRateRoutine
import Benchmarks.CompoundIII.Comet.BorrowRateRoutine

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables
open Benchmarks.CompoundIII.Comet.Immutables
open cometWithExtendedAssetListBlocks

namespace Benchmarks.CompoundIII.Comet

set_option maxRecDepth 10000

theorem cometAccruedIndices {v : CometWithExtendedAssetListImmutables}
    {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem rdata : ByteArray}
    {aw : UInt256} {σ : AccountMap} {k C : Nat} {elapsed ret : UInt256} {R : List UInt256}
    (hstack : R.length + 32 ≤ 1024) (ht : elapsed.toNat < 2^40)
    (hvalid : (D_J (deployedRuntime v) 0).contains ret = true)
    (h : RD (deployedRuntime v) ee g s0 ⟨8445⟩ (elapsed :: ret :: R) mem aw rdata σ k C) :
    let w0 := solcSlotWordAt ⟨0⟩ σ ee
    let w1 := solcSlotWordAt ⟨1⟩ σ ee
    if AccruedIndicesValid v w0 w1 elapsed then
      ∃ k' C', RD (deployedRuntime v) ee g s0 ret
        (accruedIndex v w0 w1 elapsed true :: accruedIndex v w0 w1 elapsed false :: R)
        mem aw rdata σ k' C'
    else RDrev (deployedRuntime v) g s0 := by
  dsimp only
  let w0 := solcSlotWordAt ⟨0⟩ σ ee
  let w1 := solcSlotWordAt ⟨1⟩ σ ee
  let u := utilizationWord w0 w1
  let mask := UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 64))
    (UInt256.ofNat 1)
  have hiS : UInt256.land mask w0 = totalsIndexWord w0 false := by
    rw [u256_land_comm]
    exact (totalsIndexWord_eq w0 false).symm
  have hiB : UInt256.land mask (UInt256.shiftRight w0 ⟨64⟩) = totalsIndexWord w0 true := by
    rw [u256_land_comm]
    exact (totalsIndexWord_eq w0 true).symm
  change if AccruedIndicesValid v w0 w1 elapsed then
    ∃ k' C', RD _ _ _ _ ret
      (accruedIndex v w0 w1 elapsed true :: accruedIndex v w0 w1 elapsed false :: R)
      mem aw rdata σ k' C' else _
  by_cases hz : elapsed = ⟨0⟩
  · obtain ⟨k1, C1, r1⟩ := cometWithExtendedAssetList_block_8445_fallthrough
      (immWords := wordsOf (immStore v)) (by omega) hz h
    change RD _ _ _ _ _ (mask :: elapsed :: UInt256.land mask w0 :: ret ::
      UInt256.land mask (UInt256.shiftRight w0 ⟨64⟩) :: R) _ _ _ _ _ _ at r1
    rw [hiS, hiB] at r1
    have r2 := cometWithExtendedAssetList_block_8476
      (immWords := wordsOf (immStore v)) (by omega) hvalid r1
    simp only [AccruedIndicesValid, if_pos hz, if_true, accruedIndex]
    exact ⟨_, _, r2⟩
  · obtain ⟨k1, C1, r1⟩ := cometWithExtendedAssetList_block_8445_taken
      (immWords := wordsOf (immStore v)) (by omega) hz
      (by rw [cometWithExtendedAssetListPatchedValidJumpsRuntime v]; jump_dest) h
    change RD _ _ _ _ _ (mask :: elapsed :: UInt256.land mask w0 :: ret ::
      UInt256.land mask (UInt256.shiftRight w0 ⟨64⟩) :: R) _ _ _ _ _ _ at r1
    rw [hiS, hiB] at r1
    have r2 := cometWithExtendedAssetList_block_8482
      (immWords := wordsOf (immStore v)) (by omega)
      (by rw [cometWithExtendedAssetListPatchedValidJumpsRuntime v]; jump_dest) r1
    obtain ⟨k3, C3, r3⟩ := cometUtilization (v := v)
      (by simp only [List.length_cons]; omega)
      (by rw [cometWithExtendedAssetListPatchedValidJumps v]; jump_dest) r2
    have r4 := cometWithExtendedAssetList_block_8520
      (immWords := wordsOf (immStore v)) (by omega)
      (by rw [cometWithExtendedAssetListPatchedValidJumpsRuntime v]; jump_dest) r3
    have rs := cometSupplyRate (v := v) (u := u)
      (by simp only [List.length_cons]; omega)
      (by rw [cometWithExtendedAssetListPatchedValidJumps v]; jump_dest) r4
    simp only [AccruedIndicesValid, if_neg hz]
    by_cases hs : RateValid (rateParams v false) u
    · rw [if_pos hs] at rs
      obtain ⟨k5, C5, r5⟩ := rs
      have r6 := cometWithExtendedAssetList_block_8527
        (immWords := wordsOf (immStore v)) (by omega)
        (by rw [cometWithExtendedAssetListPatchedValidJumpsRuntime v]; jump_dest) r5
      simp only [cometWithExtendedAssetList_block_8527_stack] at r6
      rw [u256LandMaskCleanOfToNat _ _ (bits := 64) rfl (rateWord_lt hs)] at r6
      have rb := cometBorrowRate (v := v) (u := u)
        (by simp only [List.length_cons]; omega)
        (by rw [cometWithExtendedAssetListPatchedValidJumps v]; jump_dest) r6
      by_cases hb : RateValid (rateParams v true) u
      · rw [if_pos hb] at rb
        obtain ⟨k7, C7, r7⟩ := rb
        have r8 := cometWithExtendedAssetList_block_8534
          (immWords := wordsOf (immStore v)) (by omega)
          (by rw [cometWithExtendedAssetListPatchedValidJumpsRuntime v]; jump_dest) r7
        simp only [cometWithExtendedAssetList_block_8534_stack] at r8
        rw [u256LandMaskCleanOfToNat _ _ (bits := 64) rfl (rateWord_lt hb)] at r8
        have ris := cometIndexAccrual (v := v) (index := totalsIndexWord w0 false)
          (rate := accruedRate v w0 w1 false) (elapsed := elapsed)
          (by simp only [List.length_cons]; omega) (totalsIndexWord_lt _ _) (rateWord_lt hs) ht
          (by rw [cometWithExtendedAssetListPatchedValidJumps v]; jump_dest) r8
        by_cases hsf : IndexAccrualValid (totalsIndexWord w0 false)
            (accruedRate v w0 w1 false) elapsed
        · rw [if_pos hsf] at ris
          obtain ⟨k9, C9, r9⟩ := ris
          have r10 := cometWithExtendedAssetList_block_8577
            (immWords := wordsOf (immStore v)) (by omega)
            (by rw [cometWithExtendedAssetListPatchedValidJumpsRuntime v]; jump_dest) r9
          have rib := cometIndexAccrual (v := v) (index := totalsIndexWord w0 true)
            (rate := accruedRate v w0 w1 true) (elapsed := elapsed)
            (by simp only [List.length_cons]; omega) (totalsIndexWord_lt _ _) (rateWord_lt hb) ht
            (by rw [cometWithExtendedAssetListPatchedValidJumps v]; jump_dest) r10
          by_cases hbf : IndexAccrualValid (totalsIndexWord w0 true)
              (accruedRate v w0 w1 true) elapsed
          · rw [if_pos hbf] at rib
            obtain ⟨k11, C11, r11⟩ := rib
            have r12 := cometWithExtendedAssetList_block_8583
              (immWords := wordsOf (immStore v)) (by omega)
              (by rw [cometWithExtendedAssetListPatchedValidJumpsRuntime v]; jump_dest) r11
            have r13 := cometWithExtendedAssetList_block_8476
              (immWords := wordsOf (immStore v)) (by omega) hvalid r12
            rw [if_pos (show AccruedWorkValid v w0 w1 elapsed from ⟨hs, hb, hsf, hbf⟩)]
            simp only [accruedIndex, if_neg hz]
            exact ⟨_, _, r13⟩
          · rw [if_neg hbf] at rib
            rw [if_neg (show ¬ AccruedWorkValid v w0 w1 elapsed from fun hv ↦ hbf hv.2.2.2)]
            exact rib
        · rw [if_neg hsf] at ris
          rw [if_neg (show ¬ AccruedWorkValid v w0 w1 elapsed from fun hv ↦ hsf hv.2.2.1)]
          exact ris
      · rw [if_neg hb] at rb
        rw [if_neg (show ¬ AccruedWorkValid v w0 w1 elapsed from fun hv ↦ hb hv.2.1)]
        exact rb
    · rw [if_neg hs] at rs
      rw [if_neg (show ¬ AccruedWorkValid v w0 w1 elapsed from fun hv ↦ hs hv.1)]
      exact rs

end Benchmarks.CompoundIII.Comet
