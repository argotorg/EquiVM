import Benchmarks.CompoundIII.Comet.PrincipalSupplyEvm
import Benchmarks.CompoundIII.Comet.RuntimeBlocks_058

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach Reasoning.Immutables
open Benchmarks.CompoundIII.Comet.Immutables cometWithExtendedAssetListBlocks

namespace Benchmarks.CompoundIII.Comet

set_option maxRecDepth 2000

theorem cometPrincipalBorrow {v : CometWithExtendedAssetListImmutables}
    {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem rdata : ByteArray}
    {aw index present ret : UInt256} {σ : AccountMap} {k C : Nat} {R : List UInt256}
    (hstack : R.length + 9 ≤ 1024)
    (hret : (D_J (deployedRuntime v) 0).contains ret = true)
    (h : RD (deployedRuntime v) ee g s0 ⟨12813⟩ (present :: index :: ret :: R)
      mem aw rdata σ k C) :
    (PrincipalMagnitudeFits true index present ∧ ∃ k' C', RD (deployedRuntime v) ee g s0 ret
      (principalMagnitudeWord true index present :: R) mem aw rdata σ k' C') ∨
    (¬ PrincipalMagnitudeFits true index present ∧ RDrev (deployedRuntime v) g s0) := by
  by_cases hm : present.toNat * 1000000000000000 < UInt256.size
  · have r1 := cometWithExtendedAssetList_block_12813_fallthrough
      (immWords := wordsOf (immStore v)) (by change R.length + 1 + 8 ≤ 1024; omega)
      (checkedMulGuard_zero hm) h
    have r2 := cometWithExtendedAssetList_block_12844
      (immWords := wordsOf (immStore v)) (by change R.length + 5 + 2 ≤ 1024; omega)
      (by rw [cometWithExtendedAssetListPatchedValidJumpsRuntime v]; jump_dest) r1
    by_cases ha : (principalMagnitudeProduct present).toNat + index.toNat < UInt256.size
    · obtain ⟨k3, C3, r3⟩ := cometCheckedAdd (v := v)
        (by change R.length + 3 + 5 ≤ 1024; omega) ha
        (by rw [cometWithExtendedAssetListPatchedValidJumps v]; jump_dest) r2
      change RD _ _ _ _ _ (principalMagnitudeSum index present :: UInt256.lnot ⟨0⟩ ::
        index :: ret :: R) _ _ _ _ _ _ at r3
      by_cases hs : 1 ≤ (principalMagnitudeSum index present).toNat
      · have r4 := cometWithExtendedAssetList_block_12850_fallthrough
          (immWords := wordsOf (immStore v)) (by change R.length + 3 + 3 ≤ 1024; omega)
          (ult_zero hs) r3
        by_cases hi : index ≠ ⟨0⟩
        · have r5 := cometWithExtendedAssetList_block_12859_fallthrough
            (immWords := wordsOf (immStore v)) (by change R.length + 1 + 5 ≤ 1024; omega)
            (isZero_eq_zero_of_ne hi) r4
          have r6 := cometWithExtendedAssetList_block_12866
            (immWords := wordsOf (immStore v)) (by change R.length + 1 + 3 ≤ 1024; omega)
            (by rw [cometWithExtendedAssetListPatchedValidJumpsRuntime v]; jump_dest) r5
          change RD _ _ _ _ _ (UInt256.div
            (principalMagnitudeSum index present + UInt256.lnot ⟨0⟩) index :: ret :: R)
            _ _ _ _ _ _ at r6
          rw [u256_add_lnot_zero_eq_sub_one] at r6
          rcases cometSafe104 (v := v) (by omega) hret r6 with
            ⟨hq, k7, C7, r7⟩ | ⟨hq, hr⟩
          · exact Or.inl ⟨⟨⟨hm, fun _ ↦ ⟨ha, hs⟩, hi⟩, hq⟩, _, _, r7⟩
          · exact Or.inr ⟨fun hf ↦ hq hf.2, hr⟩
        · have hz : index = ⟨0⟩ := not_ne_iff.mp hi
          have r5 := cometWithExtendedAssetList_block_12859_taken
            (immWords := wordsOf (immStore v)) (by change R.length + 1 + 5 ≤ 1024; omega)
            (by rw [hz]; decide)
            (by rw [cometWithExtendedAssetListPatchedValidJumpsRuntime v]; jump_dest) r4
          have r6 := cometWithExtendedAssetList_block_12878
            (immWords := wordsOf (immStore v)) (by change R.length + 4 + 2 ≤ 1024; omega)
            (by rw [cometWithExtendedAssetListPatchedValidJumpsRuntime v]; jump_dest) r5
          exact Or.inr ⟨fun hf ↦ hi hf.1.2.2,
            cometWithExtendedAssetList_block_9151 (immWords := wordsOf (immStore v))
              (by change R.length + 4 + 2 ≤ 1024; omega) r6⟩
      · have r4 := cometWithExtendedAssetList_block_12850_taken
          (immWords := wordsOf (immStore v)) (by change R.length + 3 + 3 ≤ 1024; omega)
          (by rw [ult_one (a := principalMagnitudeSum index present) (b := UInt256.ofNat 1)
                (by change (principalMagnitudeSum index present).toNat < 1; omega)]
              decide)
          (by rw [cometWithExtendedAssetListPatchedValidJumpsRuntime v]; jump_dest) r3
        have r5 := cometWithExtendedAssetList_block_12891
          (immWords := wordsOf (immStore v)) (by change R.length + 4 + 2 ≤ 1024; omega)
          (by rw [cometWithExtendedAssetListPatchedValidJumpsRuntime v]; jump_dest) r4
        exact Or.inr ⟨fun hf ↦ hs (hf.1.2.1 rfl).2,
          cometWithExtendedAssetList_block_7730 (immWords := wordsOf (immStore v))
            (by change R.length + 4 + 2 ≤ 1024; omega) r5⟩
    · exact Or.inr ⟨fun hf ↦ ha (hf.1.2.1 rfl).1,
        cometCheckedAdd_revert (v := v) (by change R.length + 4 + 4 ≤ 1024; omega)
          (Nat.le_of_not_lt ha) r2⟩
  · have r1 := cometWithExtendedAssetList_block_12813_taken
      (immWords := wordsOf (immStore v)) (by change R.length + 1 + 8 ≤ 1024; omega)
      (checkedMulGuard_nonzero (by change UInt256.size ≤ present.toNat * 1000000000000000; omega))
      (by rw [cometWithExtendedAssetListPatchedValidJumpsRuntime v]; jump_dest) h
    have r2 := cometWithExtendedAssetList_block_12904
      (immWords := wordsOf (immStore v)) (by change R.length + 7 + 2 ≤ 1024; omega)
      (by rw [cometWithExtendedAssetListPatchedValidJumpsRuntime v]; jump_dest) r1
    exact Or.inr ⟨fun hf ↦ hm hf.1.1,
      cometWithExtendedAssetList_block_7730 (immWords := wordsOf (immStore v))
        (by change R.length + 7 + 2 ≤ 1024; omega) r2⟩

end Benchmarks.CompoundIII.Comet
