import Benchmarks.CompoundIII.Comet.RateModel
import Benchmarks.CompoundIII.Comet.RateFinish
import Benchmarks.CompoundIII.Comet.RuntimeBlocks_043

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables
open Benchmarks.CompoundIII.Comet.Immutables
open cometWithExtendedAssetListBlocks

namespace Benchmarks.CompoundIII.Comet

set_option maxRecDepth 10000

theorem cometSupplyRate {v : CometWithExtendedAssetListImmutables}
    {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem rdata : ByteArray}
    {aw : UInt256} {σ : AccountMap} {k C : Nat} {u ret : UInt256} {R : List UInt256}
    (hstack : R.length + 16 ≤ 1024)
    (hvalid : (D_J (deployedRuntime v) 0).contains ret = true)
    (h : RD (deployedRuntime v) ee g s0 ⟨8614⟩ (u :: ret :: R) mem aw rdata σ k C) :
    if RateValid (rateParams v false) u then
      ∃ k' C', RD (deployedRuntime v) ee g s0 ret
        (rateWord (rateParams v false) u :: R) mem aw rdata σ k' C'
    else RDrev (deployedRuntime v) g s0 := by
  let p := rateParams v false
  have hk : wordsOf (immStore v) "supplyKink" = p.kink := by
    rw [wordsOf_immStore_supplyKink, wordOfInt_ofNat_toNat]
    rfl
  have hl : wordsOf (immStore v) "supplyPerSecondInterestRateSlopeLow" = p.low := by
    rw [wordsOf_immStore_supplyPerSecondInterestRateSlopeLow, wordOfInt_ofNat_toNat]
    rfl
  have hhval : wordsOf (immStore v) "supplyPerSecondInterestRateSlopeHigh" = p.high := by
    rw [wordsOf_immStore_supplyPerSecondInterestRateSlopeHigh, wordOfInt_ofNat_toNat]
    rfl
  have hb : wordsOf (immStore v) "supplyPerSecondInterestRateBase" = p.base := by
    rw [wordsOf_immStore_supplyPerSecondInterestRateBase, wordOfInt_ofNat_toNat]
    rfl
  change if RateValid p u then ∃ k' C', RD _ _ _ _ ret (rateWord p u :: R)
    mem aw rdata σ k' C' else RDrev _ _ _
  by_cases hle : u.toNat ≤ p.kink.toNat
  · have r1 := cometWithExtendedAssetList_block_8614_fallthrough
      (immWords := wordsOf (immStore v)) (by simp only [List.length_cons]; omega)
      (by rw [hk]; exact ugt_zero hle) h
    have r2 := cometWithExtendedAssetList_block_8655
      (immWords := wordsOf (immStore v)) (by simp only [List.length_cons]; omega)
      (by rw [cometWithExtendedAssetListPatchedValidJumpsRuntime v]; jump_dest) r1
    simp only [cometWithExtendedAssetList_block_8655_stack, hl] at r2
    by_cases hm : p.low.toNat * u.toNat < UInt256.size
    · obtain ⟨k3, C3, r3⟩ := cometCheckedMul (v := v)
        (by simp only [List.length_cons]; omega) hm
        (by rw [cometWithExtendedAssetListPatchedValidJumps v]; jump_dest) r2
      have r4 := cometWithExtendedAssetList_block_8712
        (immWords := wordsOf (immStore v)) (by simp only [List.length_cons]; omega)
        (by rw [cometWithExtendedAssetListPatchedValidJumpsRuntime v]; jump_dest) r3
      simp only [cometWithExtendedAssetList_block_8712_stack, hb] at r4
      by_cases ha : p.base.toNat + (mulFactorWord p.low u).toNat < UInt256.size
      · obtain ⟨k5, C5, r5⟩ := cometCheckedAdd (v := v)
          (by simp only [List.length_cons]; omega) ha
          (by rw [cometWithExtendedAssetListPatchedValidJumps v]; jump_dest) r4
        by_cases hs : (p.base + mulFactorWord p.low u).toNat < 2^64
        · simp only [RateValid, hle, hm, ha, hs, and_self, if_true, rateWord]
          exact cometRateFinish (v := v) (by omega) hs hvalid r5
        · simp only [RateValid, hle, hm, ha, hs, and_false, if_true, if_false]
          exact cometRateFinish_revert (v := v) (by simp only [List.length_cons]; omega) hs r5
      · simp only [RateValid, hle, hm, ha, false_and, and_false, if_true, if_false]
        exact cometCheckedAdd_revert (v := v) (by simp only [List.length_cons]; omega)
          (Nat.le_of_not_gt ha) r4
    · simp only [RateValid, hle, hm, false_and, if_true, if_false]
      exact cometCheckedMul_revert (v := v) (by simp only [List.length_cons]; omega)
        (Nat.le_of_not_gt hm) r2
  · have hgt : UInt256.gt u (wordsOf (immStore v) "supplyKink") ≠ UInt256.ofNat 0 := by
      rw [hk, ugt_one (Nat.lt_of_not_ge hle)]
      decide
    have r1 := cometWithExtendedAssetList_block_8614_taken
      (immWords := wordsOf (immStore v)) (by simp only [List.length_cons]; omega) hgt
      (by rw [cometWithExtendedAssetListPatchedValidJumpsRuntime v]; jump_dest) h
    have r2 := cometWithExtendedAssetList_block_8751
      (immWords := wordsOf (immStore v)) (by simp only [List.length_cons]; omega)
      (by rw [cometWithExtendedAssetListPatchedValidJumpsRuntime v]; jump_dest) r1
    simp only [cometWithExtendedAssetList_block_8751_stack, hl, hk] at r2
    by_cases hm : p.low.toNat * p.kink.toNat < UInt256.size
    · obtain ⟨k3, C3, r3⟩ := cometCheckedMul (v := v)
        (by simp only [List.length_cons]; omega) hm
        (by rw [cometWithExtendedAssetListPatchedValidJumps v]; jump_dest) r2
      have r4 := cometWithExtendedAssetList_block_8712
        (immWords := wordsOf (immStore v)) (by simp only [List.length_cons]; omega)
        (by rw [cometWithExtendedAssetListPatchedValidJumpsRuntime v]; jump_dest) r3
      simp only [cometWithExtendedAssetList_block_8712_stack, hb] at r4
      by_cases ha : p.base.toNat + (mulFactorWord p.low p.kink).toNat < UInt256.size
      · obtain ⟨k5, C5, r5⟩ := cometCheckedAdd (v := v)
          (by simp only [List.length_cons]; omega) ha
          (by rw [cometWithExtendedAssetListPatchedValidJumps v]; jump_dest) r4
        have r6 := cometWithExtendedAssetList_block_8818_fallthrough
          (immWords := wordsOf (immStore v)) (by simp only [List.length_cons]; omega)
          (ult_zero (Nat.le_of_lt (Nat.lt_of_not_ge hle))) r5
        have r7 := cometWithExtendedAssetList_block_8827
          (immWords := wordsOf (immStore v)) (by simp only [List.length_cons]; omega)
          (by rw [cometWithExtendedAssetListPatchedValidJumpsRuntime v]; jump_dest) r6
        simp only [cometWithExtendedAssetList_block_8827_stack, hhval] at r7
        by_cases hh : p.high.toNat * (UInt256.sub u p.kink).toNat < UInt256.size
        · obtain ⟨k8, C8, r8⟩ := cometCheckedMul (v := v)
            (by simp only [List.length_cons]; omega) hh
            (by rw [cometWithExtendedAssetListPatchedValidJumps v]; jump_dest) r7
          have r9 := cometWithExtendedAssetList_block_8866
            (immWords := wordsOf (immStore v)) (by simp only [List.length_cons]; omega)
            (by rw [cometWithExtendedAssetListPatchedValidJumpsRuntime v]; jump_dest) r8
          by_cases ha2 : (p.base + mulFactorWord p.low p.kink).toNat +
              (mulFactorWord p.high (UInt256.sub u p.kink)).toNat < UInt256.size
          · obtain ⟨k10, C10, r10⟩ := cometCheckedAdd (v := v)
              (by simp only [List.length_cons]; omega) ha2
              (by rw [cometWithExtendedAssetListPatchedValidJumps v]; jump_dest) r9
            by_cases hs : ((p.base + mulFactorWord p.low p.kink) +
                mulFactorWord p.high (UInt256.sub u p.kink)).toNat < 2^64
            · simp only [RateValid, hle, hm, hh, ha, ha2, hs, and_self, if_false, if_true, rateWord]
              exact cometRateFinish (v := v) (by omega) hs hvalid r10
            · simp only [RateValid, hle, hm, hh, ha, ha2, hs, and_false, if_false]
              exact cometRateFinish_revert (v := v) (by simp only [List.length_cons]; omega) hs r10
          · simp only [RateValid, hle, hm, hh, ha, ha2, false_and, and_false, if_false]
            exact cometCheckedAdd_revert (v := v) (by simp only [List.length_cons]; omega)
              (Nat.le_of_not_gt ha2) r9
        · simp only [RateValid, hle, hm, hh, false_and, and_false, if_false]
          exact cometCheckedMul_revert (v := v) (by simp only [List.length_cons]; omega)
            (Nat.le_of_not_gt hh) r7
      · simp only [RateValid, hle, hm, ha, false_and, and_false, if_false]
        exact cometCheckedAdd_revert (v := v) (by simp only [List.length_cons]; omega)
          (Nat.le_of_not_gt ha) r4
    · simp only [RateValid, hle, hm, false_and, if_false]
      exact cometCheckedMul_revert (v := v) (by simp only [List.length_cons]; omega)
        (Nat.le_of_not_gt hm) r2

end Benchmarks.CompoundIII.Comet
