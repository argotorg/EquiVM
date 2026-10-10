import Benchmarks.CompoundIII.Comet.SignedDebtWords
import Benchmarks.CompoundIII.Comet.NegativePrincipal
import Benchmarks.CompoundIII.Comet.RuntimeBlocks_050

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach Reasoning.Immutables
open Benchmarks.CompoundIII.Comet.Immutables cometWithExtendedAssetListBlocks

namespace Benchmarks.CompoundIII.Comet

set_option maxRecDepth 2000

-- LIBRARY CANDIDATE: identify the only overflowing signed 256-bit negation.
theorem signedWord_gt_min_iff (w : UInt256) :
    -(2^255 : Int) < signedWord w ↔
      w ≠ UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 255) := by
  have he : w = UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 255) ↔
      w.toNat = 2^255 := by
    constructor
    · intro he; rw [he]; rfl
    · intro he; exact u256_inj he
  rw [ne_eq, he, signedWord_eq]
  have hw : w.toNat < 2^256 := w.val.isLt
  split_ifs <;> simp only [Int.ofNat_eq_natCast] <;> omega

-- LIBRARY CANDIDATE: the word negation of a nonpositive signed value is its natural magnitude.
theorem signedWord_negativeMagnitude {w : UInt256} (hw : signedWord w ≤ 0) :
    Int.ofNat (UInt256.sub (UInt256.ofNat 0) w).toNat = -signedWord w := by
  by_cases hz : w = ⟨0⟩
  · subst w; decide
  · have hp : 0 < w.toNat := Nat.pos_of_ne_zero (fun h ↦ hz (uint256_toNat_eq_zero h))
    have hn : ¬ w.toNat < 2^255 := by
      intro hn; rw [signedWord_low hn] at hw
      change (w.toNat : Int) ≤ 0 at hw; omega
    rw [signedWord_eq, if_neg hn, usub_toNat_underflow (a := UInt256.ofNat 0) (b := w) hp]
    have hb : w.toNat < 2^256 := w.val.isLt
    change Int.ofNat (2^256 - w.toNat) = -(Int.ofNat w.toNat - (2^256 : Int))
    simp only [Int.ofNat_eq_natCast]
    omega

theorem cometNegate256 {v : CometWithExtendedAssetListImmutables}
    {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem rdata : ByteArray} {aw : UInt256}
    {σ : AccountMap} {k C : Nat} {value ret : UInt256} {R : List UInt256}
    (hstack : R.length + 4 ≤ 1024)
    (hret : (D_J (deployedRuntime v) 0).contains ret = true)
    (h : RD (deployedRuntime v) ee g s0 ⟨10671⟩ (value :: ret :: R) mem aw rdata σ k C) :
    (-(2^255 : Int) < signedWord value ∧ ∃ k' C', RD (deployedRuntime v) ee g s0 ret
      (UInt256.sub (UInt256.ofNat 0) value :: R) mem aw rdata σ k' C') ∨
    (¬ -(2^255 : Int) < signedWord value ∧ RDrev (deployedRuntime v) g s0) := by
  by_cases hn : -(2^255 : Int) < signedWord value
  · have hne := (signedWord_gt_min_iff value).mp hn
    have r1 := cometWithExtendedAssetList_block_10671_fallthrough
      (immWords := wordsOf (immStore v)) (by change R.length + 1 + 3 ≤ 1024; omega)
      (uInt256_eq_zero_of_ne (fun he ↦ hne (uInt256_eq_one_eq he))) h
    exact Or.inl ⟨hn, _, _, cometWithExtendedAssetList_block_10683
      (immWords := wordsOf (immStore v)) (by omega) hret r1⟩
  · have he : value = UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 255) := by
      by_contra he; exact hn ((signedWord_gt_min_iff value).mpr he)
    have r1 := cometWithExtendedAssetList_block_10671_taken
      (immWords := wordsOf (immStore v)) (by change R.length + 1 + 3 ≤ 1024; omega)
      (by rw [he, uInt256_eq_self]; decide)
      (by rw [cometWithExtendedAssetListPatchedValidJumpsRuntime v]; jump_dest) h
    have r2 := cometWithExtendedAssetList_block_10658
      (immWords := wordsOf (immStore v)) (by change R.length + 2 + 2 ≤ 1024; omega)
      (by rw [cometWithExtendedAssetListPatchedValidJumpsRuntime v]; jump_dest) r1
    exact Or.inr ⟨hn, cometWithExtendedAssetList_block_7730
      (immWords := wordsOf (immStore v)) (by change R.length + 2 + 2 ≤ 1024; omega) r2⟩

theorem cometNegate104Nonneg {v : CometWithExtendedAssetListImmutables}
    {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem rdata : ByteArray} {aw : UInt256}
    {σ : AccountMap} {k C : Nat} {value ret : UInt256} {R : List UInt256}
    (hstack : R.length + 5 ≤ 1024) (hv : value.toNat < 2^103)
    (hret : (D_J (deployedRuntime v) 0).contains ret = true)
    (h : RD (deployedRuntime v) ee g s0 ⟨10633⟩ (value :: ret :: R) mem aw rdata σ k C) :
    ∃ k' C', RD (deployedRuntime v) ee g s0 ret
      (UInt256.sub (UInt256.ofNat 0) value :: R) mem aw rdata σ k' C' := by
  have hne : value ≠ int104MinWord := by
    intro he; have hb := congrArg UInt256.toNat he; rw [int104MinWord_toNat] at hb; omega
  have r1 := cometWithExtendedAssetList_block_10633_fallthrough
    (immWords := wordsOf (immStore v)) (by change R.length + 1 + 4 ≤ 1024; omega)
    (by rw [signextend104_low hv]
        exact uInt256_eq_zero_of_ne (fun he ↦ hne (uInt256_eq_one_eq he))) h
  simp only [cometWithExtendedAssetList_block_10633_fallthrough_stack, signextend104_low hv] at r1
  exact ⟨_, _, cometWithExtendedAssetList_block_10652
    (immWords := wordsOf (immStore v)) (by omega) hret r1⟩

end Benchmarks.CompoundIII.Comet
