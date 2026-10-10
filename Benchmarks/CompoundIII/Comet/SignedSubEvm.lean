import Benchmarks.CompoundIII.Comet.SignedArithmeticEvm
import Benchmarks.CompoundIII.Comet.SignedDebtWords

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach Reasoning.Immutables
open Benchmarks.CompoundIII.Comet.Immutables cometWithExtendedAssetListBlocks

namespace Benchmarks.CompoundIII.Comet

set_option maxRecDepth 2000

-- GENERALIZES cometSignedSubNonneg to a signed left operand, including underflow.
theorem cometSignedSubNonnegRight {v : CometWithExtendedAssetListImmutables}
    {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem rdata : ByteArray} {aw : UInt256}
    {σ : AccountMap} {k C : Nat} {a b ret : UInt256} {R : List UInt256}
    (hstack : R.length + 7 ≤ 1024) (hb : b.toNat < 2^255)
    (hret : (D_J (deployedRuntime v) 0).contains ret = true)
    (h : RD (deployedRuntime v) ee g s0 ⟨9713⟩ (a :: b :: ret :: R) mem aw rdata σ k C) :
    (-(2^255 : Int) ≤ signedWord a - Int.ofNat b.toNat ∧ ∃ k' C',
      RD (deployedRuntime v) ee g s0 ret (UInt256.sub a b :: R) mem aw rdata σ k' C') ∨
    (¬ -(2^255 : Int) ≤ signedWord a - Int.ofNat b.toNat ∧ RDrev (deployedRuntime v) g s0) := by
  have hlimit : signedWord (b + UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 255)) =
      Int.ofNat b.toNat - (2^255 : Int) := by
    rw [signedWord_eq, uadd_toNat]
    rw [show (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 255)).toNat = 2^255
      from by decide]
    rw [Nat.mod_eq_of_lt (by change b.toNat + 2^255 < 2^256; omega), if_neg (by omega)]
    simp only [Int.ofNat_eq_natCast, Nat.cast_add]
    omega
  have hb0 : UInt256.slt b (UInt256.ofNat 0) = UInt256.ofNat 0 :=
    slt_lit_zero (by decide) (Nat.zero_le _) hb
  by_cases hf : -(2^255 : Int) ≤ signedWord a - Int.ofNat b.toNat
  · have hc : UInt256.slt a
        (b + UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 255)) = UInt256.ofNat 0 := by
      rw [signedWord_slt, hlimit, decide_eq_false (by omega)]; rfl
    have r1 := cometWithExtendedAssetList_block_9713_fallthrough
      (immWords := wordsOf (immStore v)) (by change R.length + 1 + 6 ≤ 1024; omega)
      (by rw [hc]; exact uint256_land_zero_left _) h
    have r2 := cometWithExtendedAssetList_block_9734_fallthrough
      (immWords := wordsOf (immStore v)) (by change R.length + 1 + 6 ≤ 1024; omega)
      (by change UInt256.land _ (UInt256.slt b (UInt256.ofNat 0)) = _
          rw [hb0]; exact uint256_land_zero_right _) r1
    exact Or.inl ⟨hf, _, _, cometWithExtendedAssetList_block_9752
      (immWords := wordsOf (immStore v)) (by omega) hret r2⟩
  · have hc : UInt256.slt a
        (b + UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 255)) = UInt256.ofNat 1 := by
      rw [signedWord_slt, hlimit, decide_eq_true (by omega)]; rfl
    have r1 := cometWithExtendedAssetList_block_9713_taken
      (immWords := wordsOf (immStore v)) (by change R.length + 1 + 6 ≤ 1024; omega)
      (by rw [hc, hb0]; decide)
      (by rw [cometWithExtendedAssetListPatchedValidJumpsRuntime v]; jump_dest) h
    have r2 := cometWithExtendedAssetList_block_9755
      (immWords := wordsOf (immStore v)) (by change R.length + 4 + 2 ≤ 1024; omega)
      (by rw [cometWithExtendedAssetListPatchedValidJumpsRuntime v]; jump_dest) r1
    exact Or.inr ⟨hf, cometWithExtendedAssetList_block_7730
      (immWords := wordsOf (immStore v)) (by change R.length + 4 + 2 ≤ 1024; omega) r2⟩

end Benchmarks.CompoundIII.Comet
