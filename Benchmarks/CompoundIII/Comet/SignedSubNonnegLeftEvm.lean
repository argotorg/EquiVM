import Benchmarks.CompoundIII.Comet.SignedArithmeticEvm

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach Reasoning.Immutables
open Benchmarks.CompoundIII.Comet.Immutables cometWithExtendedAssetListBlocks

namespace Benchmarks.CompoundIII.Comet

set_option maxRecDepth 2000

-- GENERALIZES cometSignedSubNonneg to an arbitrary signed subtrahend, including overflow.
theorem cometSignedSubNonnegLeft {v : CometWithExtendedAssetListImmutables}
    {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem rdata : ByteArray} {aw : UInt256}
    {σ : AccountMap} {k C : Nat} {a b ret : UInt256} {R : List UInt256}
    (hstack : R.length + 7 ≤ 1024) (ha : a.toNat < 2^255)
    (hret : (D_J (deployedRuntime v) 0).contains ret = true)
    (h : RD (deployedRuntime v) ee g s0 ⟨9713⟩ (a :: b :: ret :: R) mem aw rdata σ k C) :
    if signedWord a - signedWord b < (2^255 : Int) then
      ∃ k' C', RD (deployedRuntime v) ee g s0 ret (UInt256.sub a b :: R)
        mem aw rdata σ k' C'
    else RDrev (deployedRuntime v) g s0 := by
  by_cases hb : b.toNat < 2^255
  · have hf : signedWord a - signedWord b < (2^255 : Int) := by
      rw [signedWord_low ha, signedWord_low hb]
      simp only [Int.ofNat_eq_natCast]
      omega
    rw [if_pos hf]
    exact cometSignedSubNonneg hstack ha hb hret h
  · have hneg : signedWord b < 0 := by
      have hn := signedWord_nonneg_iff b
      omega
    have hb0 : UInt256.slt b (UInt256.ofNat 0) = UInt256.ofNat 1 :=
      slt_lit_one_high (by decide) (Nat.le_of_not_gt hb)
    let maxWord := UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 255))
      (UInt256.ofNat 1)
    have hm : maxWord.toNat = 2^255 - 1 := by decide +kernel
    have hlimit : signedWord (b + maxWord) = signedWord b + (2^255 : Int) - 1 := by
      have hbnd := signedWord_bounds b
      rw [signedWord_add_of_range, hm]
      all_goals simp only [hm, Int.ofNat_eq_natCast]; omega
    have r1 := cometWithExtendedAssetList_block_9713_fallthrough
      (immWords := wordsOf (immStore v)) (by change R.length + 1 + 6 ≤ 1024; omega)
      (by rw [hb0]; exact uint256_land_zero_right _) h
    split_ifs with hf
    · have hcmp : UInt256.sgt a (b + maxWord) = UInt256.ofNat 0 := by
        rw [signedWord_sgt, hlimit, decide_eq_false (by omega)]; rfl
      have r2 := cometWithExtendedAssetList_block_9734_fallthrough
        (immWords := wordsOf (immStore v)) (by change R.length + 1 + 6 ≤ 1024; omega)
        (by change UInt256.land (UInt256.sgt a (b + maxWord)) _ = _
            rw [hcmp]; exact uint256_land_zero_left _) r1
      exact ⟨_, _, cometWithExtendedAssetList_block_9752
        (immWords := wordsOf (immStore v)) (by omega) hret r2⟩
    · have hcmp : UInt256.sgt a (b + maxWord) = UInt256.ofNat 1 := by
        rw [signedWord_sgt, hlimit, decide_eq_true (by omega)]; rfl
      have r2 := cometWithExtendedAssetList_block_9734_taken
        (immWords := wordsOf (immStore v)) (by change R.length + 1 + 6 ≤ 1024; omega)
        (by change UInt256.land (UInt256.sgt a (b + maxWord))
              (UInt256.slt b (UInt256.ofNat 0)) ≠ _
            rw [hcmp, hb0]; decide)
        (by rw [cometWithExtendedAssetListPatchedValidJumpsRuntime v]; jump_dest) r1
      have r3 := cometWithExtendedAssetList_block_7775 (immWords := wordsOf (immStore v))
        (by change R.length + 3 + 2 ≤ 1024; omega)
        (by rw [cometWithExtendedAssetListPatchedValidJumpsRuntime v]; jump_dest) r2
      exact cometWithExtendedAssetList_block_7730
        (immWords := wordsOf (immStore v)) (by change R.length + 3 + 2 ≤ 1024; omega) r3

end Benchmarks.CompoundIII.Comet
