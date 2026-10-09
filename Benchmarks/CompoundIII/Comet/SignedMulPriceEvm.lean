import Benchmarks.CompoundIII.Comet.SignedMulPriceModel
import Benchmarks.CompoundIII.Comet.RuntimeBlocks_052
import Benchmarks.CompoundIII.Comet.RuntimeBlocks_053
import Benchmarks.CompoundIII.Comet.RuntimeBlocks_043
import Benchmarks.CompoundIII.Comet.NarrowArithmetic

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach Reasoning.Immutables
open Benchmarks.CompoundIII.Comet.Immutables cometWithExtendedAssetListBlocks

namespace Benchmarks.CompoundIII.Comet

set_option maxRecDepth 2000

theorem cometSignedMulPrice {v : CometWithExtendedAssetListImmutables}
    {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem rdata : ByteArray}
    {aw m p scale ret : UInt256} {σ : AccountMap} {k C : Nat} {R : List UInt256}
    (hstack : R.length + 12 ≤ 1024) (hm : m.toNat ≤ 2^255)
    (hp : 0 < p.toNat) (hp' : p.toNat < 2^255) (hscale : scale.toNat < 2^64)
    (hret : (D_J (deployedRuntime v) 0).contains ret = true)
    (h : RD (deployedRuntime v) ee g s0 ⟨11226⟩
      (UInt256.sub (UInt256.ofNat 0) m :: p :: scale :: ret :: R) mem aw rdata σ k C) :
    if signedDebtPriceValid m p scale then
      ∃ k' C', RD (deployedRuntime v) ee g s0 ret
        (signedDebtPriceWord m p scale :: R) mem aw rdata σ k' C'
    else RDrev (deployedRuntime v) g s0 := by
  have hzword : UInt256.ofNat 0 = (⟨0⟩ : UInt256) := rfl
  have hn : signedWord (UInt256.sub (UInt256.ofNat 0) m) = -Int.ofNat m.toNat :=
    signedWord_zeroSub_le hm
  have hng : UInt256.sgt (UInt256.sub (UInt256.ofNat 0) m) (UInt256.ofNat 0) =
      UInt256.ofNat 0 := by
    rw [signedWord_sgt, hn]
    change UInt256.fromBool (decide (0 < -Int.ofNat m.toNat)) = _
    rw [decide_eq_false (by simp only [Int.ofNat_eq_natCast]; omega)]
    rfl
  have hpg : UInt256.sgt p (UInt256.ofNat 0) = UInt256.ofNat 1 := by
    rw [signedWord_sgt, signedWord_low hp']
    change UInt256.fromBool (decide (0 < Int.ofNat p.toNat)) = _
    rw [decide_eq_true (by simp only [Int.ofNat_eq_natCast]; exact_mod_cast hp)]
    rfl
  have hpl : UInt256.slt p (UInt256.ofNat 0) = UInt256.ofNat 0 :=
    slt_lit_zero (by decide) (Nat.zero_le _) hp'
  have r1 := cometWithExtendedAssetList_block_11226
    (immWords := wordsOf (immStore v)) (by simp only [List.length_cons]; omega)
    (by rw [cometWithExtendedAssetListPatchedValidJumpsRuntime v]; jump_dest) h
  obtain ⟨k2, C2, r2⟩ := cometSigned256 (v := v) (n := p) (ret := UInt256.ofNat 11237)
    (R := scale :: UInt256.sub (UInt256.ofNat 0) m :: ret :: R)
    (by simp only [List.length_cons]; omega) hp'
    (by
      change (D_J (immutableLayout.runtime cometWithExtendedAssetListBytecode
        (wordsOf (immStore v))) 0).contains (UInt256.ofNat 11237) = true
      rw [cometWithExtendedAssetListPatchedValidJumpsRuntime v]
      jump_dest) r1
  have r3 := cometWithExtendedAssetList_block_11237_fallthrough
    (immWords := wordsOf (immStore v)) (by simp only [List.length_cons]; omega)
    (by rw [hng]; simp only [hzword, uint256_land_zero_right]) r2
  have r4 := cometWithExtendedAssetList_block_11268_fallthrough
    (immWords := wordsOf (immStore v)) (by simp only [List.length_cons]; omega)
    (by rw [hpl]; simp only [hzword, uint256_land_zero_left, uint256_land_zero_right]) r3
  by_cases hfit : m.toNat * p.toNat ≤ 2^255
  · have hcmp : UInt256.slt (UInt256.sub (UInt256.ofNat 0) m)
        (UInt256.sdiv (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 255)) p) =
        UInt256.ofNat 0 := by
      rw [signedDebtMulGuard m p hm hp hp', decide_eq_false (by omega)]
      rfl
    have r5 := cometWithExtendedAssetList_block_11294_fallthrough
      (immWords := wordsOf (immStore v)) (by simp only [List.length_cons]; omega)
      (by rw [hcmp]; simp only [hzword, uint256_land_zero_left]) r4
    have r6 := cometWithExtendedAssetList_block_11312_fallthrough
      (immWords := wordsOf (immStore v)) (by simp only [List.length_cons]; omega)
      (by rw [hpl]; simp only [hzword, uint256_land_zero_right, uint256_land_zero_left]) r5
    have hs : UInt256.land scale (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1)
        (UInt256.ofNat 64)) (UInt256.ofNat 1)) = scale :=
      u256LandMaskCleanOfToNat _ _ (bits := 64) rfl hscale
    by_cases hz : scale = UInt256.ofNat 0
    · rw [if_neg (fun hv : signedDebtPriceValid m p scale ↦ hv.2 hz)]
      have r7 := cometWithExtendedAssetList_block_11323_taken
        (immWords := wordsOf (immStore v)) (by simp only [List.length_cons]; omega)
        (by rw [hs, hz]; decide)
        (by rw [cometWithExtendedAssetListPatchedValidJumpsRuntime v]; jump_dest) r6
      have r8 := cometWithExtendedAssetList_block_11373
        (immWords := wordsOf (immStore v)) (by change R.length + 4 + 2 ≤ 1024; omega)
        (by rw [cometWithExtendedAssetListPatchedValidJumpsRuntime v]; jump_dest) r7
      exact cometWithExtendedAssetList_block_9151
        (immWords := wordsOf (immStore v)) (by change R.length + 4 + 2 ≤ 1024; omega) r8
    · rw [if_pos ⟨hfit, hz⟩]
      have r7 := cometWithExtendedAssetList_block_11323_fallthrough
        (immWords := wordsOf (immStore v)) (by simp only [List.length_cons]; omega)
        (by rw [hs]; exact isZero_eq_zero_of_ne hz) r6
      dsimp only [cometWithExtendedAssetList_block_11323_fallthrough_stack] at r7
      rw [hs] at r7
      have hsmax : scale ≠ UInt256.lnot (UInt256.ofNat 0) := by
        intro he
        rw [he] at hscale
        contradiction
      have r8 := cometWithExtendedAssetList_block_11345_fallthrough
        (immWords := wordsOf (immStore v)) (by simp only [List.length_cons]; omega)
        (by rw [u256_eq_of_ne hsmax, uint256_land_zero_left]; rfl) r7
      have r9 := cometWithExtendedAssetList_block_11358
        (immWords := wordsOf (immStore v)) (by omega) hret r8
      dsimp only [cometWithExtendedAssetList_block_11358_stack] at r9
      have hprod : (UInt256.mul m p).toNat ≤ 2^255 := by
        rw [u256_mul_toNat, Nat.mod_eq_of_lt (lt_of_le_of_lt hfit (by decide))]
        exact hfit
      rw [wordMul_zeroSub, wordSdiv_zeroSub_low hprod (lt_trans hscale (by decide))] at r9
      exact ⟨_, _, r9⟩
  · rw [if_neg (fun hv : signedDebtPriceValid m p scale ↦ hfit hv.1)]
    have hcmp : UInt256.slt (UInt256.sub (UInt256.ofNat 0) m)
        (UInt256.sdiv (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 255)) p) =
        UInt256.ofNat 1 := by
      rw [signedDebtMulGuard m p hm hp hp', decide_eq_true (by omega)]
      rfl
    have hpos : 0 < m.toNat := by
      by_contra hzero
      have hz : m.toNat = 0 := by omega
      simp only [hz, zero_mul] at hfit
      omega
    have hnl : UInt256.slt (UInt256.sub (UInt256.ofNat 0) m) (UInt256.ofNat 0) =
        UInt256.ofNat 1 := by
      rw [signedWord_slt, hn]
      change UInt256.fromBool (decide (-Int.ofNat m.toNat < 0)) = _
      rw [decide_eq_true (by simp only [Int.ofNat_eq_natCast]; omega)]
      rfl
    have r5 := cometWithExtendedAssetList_block_11294_taken
      (immWords := wordsOf (immStore v)) (by simp only [List.length_cons]; omega)
      (by rw [hcmp, hnl, hpg]; decide)
      (by rw [cometWithExtendedAssetListPatchedValidJumpsRuntime v]; jump_dest) r4
    have r6 := cometWithExtendedAssetList_block_11399
      (immWords := wordsOf (immStore v)) (by change R.length + 9 + 2 ≤ 1024; omega)
      (by rw [cometWithExtendedAssetListPatchedValidJumpsRuntime v]; jump_dest) r5
    exact cometWithExtendedAssetList_block_7730
      (immWords := wordsOf (immStore v)) (by change R.length + 9 + 2 ≤ 1024; omega) r6

end Benchmarks.CompoundIII.Comet
