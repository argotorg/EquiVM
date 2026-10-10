import Benchmarks.CompoundIII.Comet.SignedWord
import Benchmarks.CompoundIII.Comet.RuntimeBlocks_039
import Benchmarks.CompoundIII.Comet.RuntimeBlocks_046
import Benchmarks.CompoundIII.Comet.RuntimeBlocks_047

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach Reasoning.Immutables
open Benchmarks.CompoundIII.Comet.Immutables cometWithExtendedAssetListBlocks

namespace Benchmarks.CompoundIII.Comet

set_option maxRecDepth 10000

theorem cometSignedSubNonneg {v : CometWithExtendedAssetListImmutables}
    {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem rdata : ByteArray} {aw : UInt256}
    {σ : AccountMap} {k C : Nat} {a b ret : UInt256} {R : List UInt256}
    (hstack : R.length + 7 ≤ 1024) (ha : a.toNat < 2^255) (hb : b.toNat < 2^255)
    (hret : (D_J (deployedRuntime v) 0).contains ret = true)
    (h : RD (deployedRuntime v) ee g s0 ⟨9713⟩ (a :: b :: ret :: R) mem aw rdata σ k C) :
    ∃ k' C', RD (deployedRuntime v) ee g s0 ret (UInt256.sub a b :: R)
      mem aw rdata σ k' C' := by
  have hb0 : UInt256.slt b (UInt256.ofNat 0) = ⟨0⟩ :=
    slt_lit_zero (by decide) (Nat.zero_le _) hb
  have hcmp : UInt256.slt a
      (b + UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 255)) = ⟨0⟩ := by
    apply slt_zero_low_high ha
    rw [uadd_toNat]
    rw [show (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 255)).toNat = 2^255
      by decide +kernel]
    rw [Nat.mod_eq_of_lt (by norm_num [UInt256.size]; omega)]
    omega
  have r1 := cometWithExtendedAssetList_block_9713_fallthrough
    (immWords := wordsOf (immStore v)) (by simpa using hstack)
    (by rw [hcmp]; exact uint256_land_zero_left _) h
  have r2 := cometWithExtendedAssetList_block_9734_fallthrough
    (immWords := wordsOf (immStore v)) (by change R.length + 1 + 6 ≤ 1024; omega)
    (by change UInt256.land _ (UInt256.slt b (UInt256.ofNat 0)) = ⟨0⟩
        rw [hb0]; exact uint256_land_zero_right _) r1
  exact ⟨_, _, cometWithExtendedAssetList_block_9752
    (immWords := wordsOf (immStore v)) (by omega) hret r2⟩

theorem cometSignedAddNonneg {v : CometWithExtendedAssetListImmutables}
    {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem rdata : ByteArray} {aw : UInt256}
    {σ : AccountMap} {k C : Nat} {a b ret : UInt256} {R : List UInt256}
    (hstack : R.length + 8 ≤ 1024) (hb : b.toNat < 2^255)
    (hret : (D_J (deployedRuntime v) 0).contains ret = true)
    (h : RD (deployedRuntime v) ee g s0 ⟨9768⟩ (b :: a :: ret :: R) mem aw rdata σ k C) :
    if signedWord a + Int.ofNat b.toNat < (2^255 : Int) then
      ∃ k' C', RD (deployedRuntime v) ee g s0 ret ((a + b) :: R) mem aw rdata σ k' C'
    else RDrev (deployedRuntime v) g s0 := by
  let limit := UInt256.sub
    (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 255))
      (UInt256.ofNat 1)) b
  have hln : limit.toNat = 2^255 - 1 - b.toNat := by
    apply usub_toNat
    change b.toNat ≤ 2^255 - 1
    omega
  have hli : signedWord limit = (2^255 : Int) - 1 - Int.ofNat b.toNat := by
    rw [signedWord_low (by rw [hln]; omega), hln]
    simp only [Int.ofNat_eq_natCast]
    omega
  have hb0 : UInt256.slt b (UInt256.ofNat 0) = ⟨0⟩ :=
    slt_lit_zero (by decide) (Nat.zero_le _) hb
  split_ifs with hi
  · have hcmp : UInt256.sgt a limit = ⟨0⟩ := by
      rw [signedWord_sgt, hli, decide_eq_false (by omega)]
      rfl
    have r1 := cometWithExtendedAssetList_block_9768_fallthrough
      (immWords := wordsOf (immStore v)) (by simpa using hstack)
      (by change UInt256.land (UInt256.sgt a limit) _ = ⟨0⟩
          rw [hcmp]; exact uint256_land_zero_left _) h
    have r2 := cometWithExtendedAssetList_block_9793_fallthrough
      (immWords := wordsOf (immStore v)) (by change R.length + 1 + 5 ≤ 1024; omega)
      (by change UInt256.land _ (UInt256.slt b (UInt256.ofNat 0)) = ⟨0⟩
          rw [hb0]; exact uint256_land_zero_right _) r1
    have r3 := cometWithExtendedAssetList_block_9809
      (immWords := wordsOf (immStore v)) (by omega) hret r2
    change RD _ _ _ _ _ ((b + a) :: R) _ _ _ _ _ _ at r3
    rw [u256_add_comm b a] at r3
    exact ⟨_, _, r3⟩
  · have hcmp : UInt256.sgt a limit = ⟨1⟩ := by
      rw [signedWord_sgt, hli, decide_eq_true (by omega)]
      rfl
    have r1 := cometWithExtendedAssetList_block_9768_taken
      (immWords := wordsOf (immStore v)) (by simpa using hstack)
      (by change UInt256.land (UInt256.sgt a limit)
            (UInt256.isZero (UInt256.slt b (UInt256.ofNat 0))) ≠ ⟨0⟩
          rw [hcmp, hb0]; decide)
      (by rw [cometWithExtendedAssetListPatchedValidJumpsRuntime v]; jump_dest) h
    have r2 := cometWithExtendedAssetList_block_9812
      (immWords := wordsOf (immStore v)) (by change R.length + 4 + 2 ≤ 1024; omega)
      (by rw [cometWithExtendedAssetListPatchedValidJumpsRuntime v]; jump_dest) r1
    exact cometWithExtendedAssetList_block_7730
      (immWords := wordsOf (immStore v)) (by change R.length + 4 + 2 ≤ 1024; omega) r2

theorem cometSignedAddNonnegRight {v : CometWithExtendedAssetListImmutables}
    {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem rdata : ByteArray} {aw : UInt256}
    {σ : AccountMap} {k C : Nat} {a b ret : UInt256} {R : List UInt256}
    (hstack : R.length + 8 ≤ 1024) (hb : b.toNat < 2^255)
    (hret : (D_J (deployedRuntime v) 0).contains ret = true)
    (h : RD (deployedRuntime v) ee g s0 ⟨9768⟩ (a :: b :: ret :: R) mem aw rdata σ k C) :
    if signedWord a + Int.ofNat b.toNat < (2^255 : Int) then
      ∃ k' C', RD (deployedRuntime v) ee g s0 ret ((a + b) :: R) mem aw rdata σ k' C'
    else RDrev (deployedRuntime v) g s0 := by
  by_cases ha : a.toNat < 2^255
  · have hr := cometSignedAddNonneg hstack ha hret h
    have heq : signedWord b + Int.ofNat a.toNat = signedWord a + Int.ofNat b.toNat := by
      rw [signedWord_low ha, signedWord_low hb]
      omega
    rw [heq] at hr
    split_ifs with hi
    · rw [if_pos hi] at hr
      obtain ⟨k', C', hr⟩ := hr
      rw [u256_add_comm b a] at hr
      exact ⟨_, _, hr⟩
    · rw [if_neg hi] at hr
      exact hr
  · have ha0 : UInt256.slt a (UInt256.ofNat 0) = ⟨1⟩ :=
      slt_lit_one_high (by decide) (Nat.le_of_not_gt ha)
    have hbound : signedWord a + Int.ofNat b.toNat < (2^255 : Int) := by
      rw [signedWord_eq, if_neg ha]
      have hw := a.val.isLt
      change a.toNat < 2^256 at hw
      simp only [Int.ofNat_eq_natCast]
      omega
    rw [if_pos hbound]
    have hcmp : UInt256.slt b
        (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 255)) a) = ⟨0⟩ := by
      have hmin : (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 255)).toNat = 2^255 :=
        by decide +kernel
      by_cases heq : a.toNat = 2^255
      · have hz : UInt256.sub
            (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 255)) a = UInt256.ofNat 0 := by
          apply u256_inj
          rw [usub_toNat (by rw [hmin, heq]), hmin, heq]
          rfl
        rw [hz]
        exact slt_lit_zero (by decide) (Nat.zero_le _) hb
      · apply slt_zero_low_high hb
        rw [usub_toNat_underflow (by rw [hmin]; omega), hmin]
        have hw := a.val.isLt
        change a.toNat < UInt256.size at hw
        norm_num [UInt256.size] at hw ⊢
        omega
    have r1 := cometWithExtendedAssetList_block_9768_fallthrough
      (immWords := wordsOf (immStore v)) (by simpa using hstack)
      (by rw [ha0]; exact uint256_land_zero_right _) h
    have r2 := cometWithExtendedAssetList_block_9793_fallthrough
      (immWords := wordsOf (immStore v)) (by change R.length + 1 + 5 ≤ 1024; omega)
      (by change UInt256.land (UInt256.slt b
            (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 255)) a)) _ = ⟨0⟩
          rw [hcmp]; exact uint256_land_zero_left _) r1
    exact ⟨_, _, cometWithExtendedAssetList_block_9809
      (immWords := wordsOf (immStore v)) (by omega) hret r2⟩

end Benchmarks.CompoundIII.Comet
