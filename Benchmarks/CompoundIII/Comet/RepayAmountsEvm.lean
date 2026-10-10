import Benchmarks.CompoundIII.Comet.RepayAmountsModel
import Benchmarks.CompoundIII.Comet.WithdrawAmountsWords
import Benchmarks.CompoundIII.Comet.Signed104SubEvm
import Benchmarks.CompoundIII.Comet.Negate104PackedEvm
import Benchmarks.CompoundIII.Comet.RuntimeBlocks_061

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach Reasoning.Immutables
open Benchmarks.CompoundIII.Comet.Immutables cometWithExtendedAssetListBlocks

namespace Benchmarks.CompoundIII.Comet

set_option maxRecDepth 2000
attribute [local irreducible] signed104

theorem cometRepayAmounts {v : CometWithExtendedAssetListImmutables}
    {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem rdata : ByteArray}
    {aw old next ret : UInt256} {σ : AccountMap} {k C : Nat} {R : List UInt256}
    (hstack : R.length + 10 ≤ 1024)
    (hret : (D_J (deployedRuntime v) 0).contains ret = true)
    (h : RD (deployedRuntime v) ee g s0 ⟨13148⟩ (old :: next :: ret :: R)
      mem aw rdata σ k C) :
    (RepayAmountsFits old next ∧ ∃ k' C', RD (deployedRuntime v) ee g s0 ret
      (supplyAmount old next :: repayAmount old next :: R)
      mem aw rdata σ k' C') ∨
    (¬ RepayAmountsFits old next ∧ RDrev (deployedRuntime v) g s0) := by
  have hmask (w : UInt256) (hw : w.toNat < 2^104) :
      UInt256.land (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 104))
        (UInt256.ofNat 1)) w = w := by
    rw [u256_land_comm]
    exact u256LandMaskCleanOfToNat w _ rfl hw
  by_cases hi : signed104 next < signed104 old
  · have r1 := cometWithExtendedAssetList_block_13148_taken
      (immWords := wordsOf (immStore v)) (by omega)
      (by rw [signedWord_slt, signedWord_signextend104, signedWord_signextend104,
            decide_eq_true hi]; decide)
      (by rw [cometWithExtendedAssetListPatchedValidJumpsRuntime v]; jump_dest) h
    have r2 := cometWithExtendedAssetList_block_13259
      (immWords := wordsOf (immStore v)) (by omega) hret r1
    refine Or.inl ⟨by simp only [RepayAmountsFits, if_pos hi], k + 15 + 11, C + 54 + 32, ?_⟩
    simpa only [supplyAmount, repayAmount, if_pos hi] using r2
  · have hle : signed104 old ≤ signed104 next := by omega
    have r1 := cometWithExtendedAssetList_block_13148_fallthrough
      (immWords := wordsOf (immStore v)) (by omega)
      (by rw [signedWord_slt, signedWord_signextend104, signedWord_signextend104,
            decide_eq_false hi]; rfl) h
    by_cases hn : signed104 next ≤ 0
    · have r2 := cometWithExtendedAssetList_block_13167_fallthrough
        (immWords := wordsOf (immStore v)) (by change R.length + 4 + 2 ≤ 1024; omega)
        (by rw [signedWord_slt, signedWord_signextend104]
            change UInt256.fromBool (decide (0 < signed104 next)) = _
            rw [decide_eq_false (by omega)]; rfl) r1
      have r3 := cometWithExtendedAssetList_block_13174
        (immWords := wordsOf (immStore v)) (by omega)
        (by rw [cometWithExtendedAssetListPatchedValidJumpsRuntime v]; jump_dest) r2
      rcases cometSigned104SubNonneg (v := v) (by change R.length + 1 + 8 ≤ 1024; omega)
          hle (by rw [cometWithExtendedAssetListPatchedValidJumps v]; jump_dest) r3 with
        ⟨hf, k4, C4, r4⟩ | ⟨hf, hr⟩
      · rw [principalDecrease_word hle] at r4
        have r5 := cometWithExtendedAssetList_block_13184
          (immWords := wordsOf (immStore v)) (by omega) hret r4
        change RD _ _ _ _ _ (UInt256.ofNat 0 :: UInt256.land _
          (principalDecrease next old) :: R) _ _ _ _ _ _ at r5
        rw [hmask _ (principalDecrease_lt next old)] at r5
        refine Or.inl ⟨by simpa only [RepayAmountsFits, if_neg hi, if_pos hn] using hf,
          k4 + 11, C4 + 36, ?_⟩
        simpa only [supplyAmount, repayAmount, if_neg hi, if_pos hn] using r5
      · exact Or.inr ⟨by simpa only [RepayAmountsFits, if_neg hi, if_pos hn] using hf, hr⟩
    · have r2 := cometWithExtendedAssetList_block_13167_taken
        (immWords := wordsOf (immStore v)) (by change R.length + 4 + 2 ≤ 1024; omega)
        (by rw [signedWord_slt, signedWord_signextend104]
            change UInt256.fromBool (decide (0 < signed104 next)) ≠ _
            rw [decide_eq_true (by omega)]; decide)
        (by rw [cometWithExtendedAssetListPatchedValidJumpsRuntime v]; jump_dest) r1
      by_cases ho : 0 ≤ signed104 old
      · have r3 := cometWithExtendedAssetList_block_13199_fallthrough
          (immWords := wordsOf (immStore v)) (by change R.length + 3 + 2 ≤ 1024; omega)
          (by rw [signedWord_sgt, signedWord_signextend104]
              change UInt256.fromBool (decide (signed104 old < 0)) = _
              rw [decide_eq_false (by omega)]; rfl) r2
        have r4 := cometWithExtendedAssetList_block_13207
          (immWords := wordsOf (immStore v)) (by omega)
          (by rw [cometWithExtendedAssetListPatchedValidJumpsRuntime v]; jump_dest) r3
        rcases cometSigned104SubNonneg (v := v) (by change R.length + 1 + 8 ≤ 1024; omega)
            hle (by rw [cometWithExtendedAssetListPatchedValidJumps v]; jump_dest) r4 with
          ⟨hf, k5, C5, r5⟩ | ⟨hf, hr⟩
        · rw [principalDecrease_word hle] at r5
          have r6 := cometWithExtendedAssetList_block_13216
            (immWords := wordsOf (immStore v)) (by omega) hret r5
          change RD _ _ _ _ _ (UInt256.land _ (principalDecrease next old) ::
            UInt256.ofNat 0 :: R) _ _ _ _ _ _ at r6
          rw [hmask _ (principalDecrease_lt next old)] at r6
          refine Or.inl ⟨by simpa only [RepayAmountsFits, if_neg hi, if_neg hn, if_pos ho]
              using hf, k5 + 14, C5 + 45, ?_⟩
          simpa only [supplyAmount, repayAmount, if_neg hi, if_neg hn,
            if_pos ho] using r6
        · exact Or.inr ⟨by simpa only [RepayAmountsFits, if_neg hi, if_neg hn, if_pos ho]
            using hf, hr⟩
      · have r3 := cometWithExtendedAssetList_block_13199_taken
          (immWords := wordsOf (immStore v)) (by change R.length + 3 + 2 ≤ 1024; omega)
          (by rw [signedWord_sgt, signedWord_signextend104]
              change UInt256.fromBool (decide (signed104 old < 0)) ≠ _
              rw [decide_eq_true (by omega)]; decide)
          (by rw [cometWithExtendedAssetListPatchedValidJumpsRuntime v]; jump_dest) r2
        have r4 := cometWithExtendedAssetList_block_13234
          (immWords := wordsOf (immStore v)) (by change R.length + 2 + 3 ≤ 1024; omega)
          (by rw [cometWithExtendedAssetListPatchedValidJumpsRuntime v]; jump_dest) r3
        rcases cometNegate104Packed (v := v) (by change R.length + 2 + 5 ≤ 1024; omega)
            (by omega) (by rw [cometWithExtendedAssetListPatchedValidJumps v]; jump_dest) r4 with
          ⟨hf, k5, C5, r5⟩ | ⟨hf, hr⟩
        · have r6 := cometWithExtendedAssetList_block_13243
            (immWords := wordsOf (immStore v)) (by omega) hret r5
          change RD _ _ _ _ _ (UInt256.land next _ ::
            UInt256.land _ (negativePrincipal old) :: R) _ _ _ _ _ _ at r6
          rw [u256_land_comm next _, hmask _ (lt_trans (negativePrincipal_lt hf) (by decide)),
            mask104_positivePrincipal (by omega : 0 ≤ signed104 next)] at r6
          refine Or.inl ⟨by simpa only [RepayAmountsFits, if_neg hi, if_neg hn, if_neg ho]
              using hf, k5 + 13, C5 + 42, ?_⟩
          simpa only [supplyAmount, repayAmount, if_neg hi, if_neg hn,
            if_neg ho] using r6
        · exact Or.inr ⟨by simpa only [RepayAmountsFits, if_neg hi, if_neg hn, if_neg ho]
            using hf, hr⟩

end Benchmarks.CompoundIII.Comet
