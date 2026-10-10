import Benchmarks.CompoundIII.Comet.PauseSource
import Benchmarks.CompoundIII.Comet.RuntimeBlocks_021

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach Reasoning.Immutables
open Benchmarks.CompoundIII.Comet.Immutables cometWithExtendedAssetListBlocks

namespace Benchmarks.CompoundIII.Comet

set_option maxRecDepth 10000

-- LIBRARY CANDIDATE: address inequality as the compiler's EQ/ISZERO word.
theorem addressMismatchWord (a b : AccountAddress) :
    UInt256.isZero (UInt256.eq (UInt256.ofNat a.val) (UInt256.ofNat b.val)) =
      boolWord (decide (a ≠ b)) := by
  by_cases he : a = b
  · subst b
    rw [uInt256_eq_self]
    simp only [ne_eq, not_true_eq_false, decide_false, boolWord, Bool.false_eq_true, if_false]
    rfl
  · have hw : UInt256.ofNat a.val ≠ UInt256.ofNat b.val := by
      intro hh
      apply he
      have hr := congrArg (fun w : UInt256 ↦ AccountAddress.ofNat w.toNat) hh
      change AccountAddress.ofNat (EVM.word a.val).toNat =
        AccountAddress.ofNat (EVM.word b.val).toNat at hr
      simpa only [accountAddress_of_word_val] using hr
    rw [uInt256_eq_zero_of_ne (fun h ↦ hw (uInt256_eq_one_eq h)), decide_eq_true he]
    rfl

theorem cometPauseAuthorize {v : CometWithExtendedAssetListImmutables}
    {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem rdata : ByteArray} {aw : UInt256}
    {σ : AccountMap} {k C : Nat} {R : List UInt256}
    (hstack : R.length + 4 ≤ 1024)
    (h : RD (deployedRuntime v) ee g s0 ⟨3431⟩ R mem aw rdata σ k C) :
    if PauseAuthorized v ee then
      ∃ k' C', RD (deployedRuntime v) ee g s0 ⟨3489⟩ R mem aw rdata σ k' C'
    else RDrev (deployedRuntime v) g s0 := by
  have hgov : UInt256.isZero (UInt256.eq (UInt256.ofNat ee.source.val)
      (UInt256.land (wordsOf (immStore v) "governor")
        (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160))
          (UInt256.ofNat 1)))) = boolWord (decide (ee.source ≠ v.governor)) := by
    rw [wordsOf_immStore_governor]
    change UInt256.isZero (UInt256.eq (UInt256.ofNat ee.source.val)
      (UInt256.land (EVM.word v.governor.val) solcAddrMask)) = _
    rw [addressWord_val_clean]
    exact addressMismatchWord _ _
  have hguard : UInt256.isZero (UInt256.eq (UInt256.ofNat ee.source.val)
      (UInt256.land (wordsOf (immStore v) "pauseGuardian")
        (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160))
          (UInt256.ofNat 1)))) = boolWord (decide (ee.source ≠ v.pauseGuardian)) := by
    rw [wordsOf_immStore_pauseGuardian]
    change UInt256.isZero (UInt256.eq (UInt256.ofNat ee.source.val)
      (UInt256.land (EVM.word v.pauseGuardian.val) solcAddrMask)) = _
    rw [addressWord_val_clean]
    exact addressMismatchWord _ _
  by_cases hg : ee.source = v.governor
  · have hz : boolWord (decide (ee.source ≠ v.governor)) = ⟨0⟩ := by simp [boolWord, hg]
    have rd1 := cometWithExtendedAssetList_block_3431_fallthrough
      (immWords := wordsOf (immStore v)) hstack (by rw [hgov, hz]; rfl) h
    have rd2 := cometWithExtendedAssetList_block_3483_fallthrough
      (immWords := wordsOf (immStore v)) (by omega) (by exact hgov.trans hz) rd1
    rw [if_pos (show PauseAuthorized v ee from Or.inl hg)]
    exact ⟨_, _, rd2⟩
  · have ho : boolWord (decide (ee.source ≠ v.governor)) = ⟨1⟩ := by simp [boolWord, hg]
    have rd1 := cometWithExtendedAssetList_block_3431_taken
      (immWords := wordsOf (immStore v)) hstack (by rw [hgov, ho]; decide)
      (by rw [cometWithExtendedAssetListPatchedValidJumpsRuntime v]; jump_dest) h
    have rd2 := cometWithExtendedAssetList_block_3699 (immWords := wordsOf (immStore v))
      (by omega) (by rw [cometWithExtendedAssetListPatchedValidJumpsRuntime v]; jump_dest) rd1
    by_cases hp : ee.source = v.pauseGuardian
    · have hz : boolWord (decide (ee.source ≠ v.pauseGuardian)) = ⟨0⟩ := by simp [boolWord, hp]
      have rd3 := cometWithExtendedAssetList_block_3483_fallthrough
        (immWords := wordsOf (immStore v)) (by omega) (by exact hguard.trans hz) rd2
      rw [if_pos (show PauseAuthorized v ee from Or.inr hp)]
      exact ⟨_, _, rd3⟩
    · have ho' : boolWord (decide (ee.source ≠ v.pauseGuardian)) = ⟨1⟩ := by
        simp [boolWord, hp]
      have rd3 := cometWithExtendedAssetList_block_3483_taken
        (immWords := wordsOf (immStore v)) (by omega)
        (by change UInt256.isZero _ ≠ ⟨0⟩; rw [hguard, ho']; decide)
        (by rw [cometWithExtendedAssetListPatchedValidJumpsRuntime v]; jump_dest) rd2
      rw [if_neg (show ¬ PauseAuthorized v ee from by simp [PauseAuthorized, hg, hp])]
      exact cometWithExtendedAssetList_block_3682 (immWords := wordsOf (immStore v))
        (by change R.length + 3 ≤ 1024; omega) rd3

end Benchmarks.CompoundIII.Comet
