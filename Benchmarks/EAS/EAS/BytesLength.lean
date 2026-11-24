import Benchmarks.EAS.EAS.Common
import Benchmarks.EAS.EAS.RuntimeBlocks_025
import Benchmarks.EAS.EAS.RuntimeBlocks_026

variable {fork : Ethereum.Fork}
open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables Benchmarks.EAS.EAS.Immutables
namespace Benchmarks.EAS.EAS
set_option maxRecDepth 10000

-- GENERALIZES Reasoning.WordArithmetic.rpowShiftRight128_toNat to every in-range shift.
theorem wordShiftRight_div (word : UInt256) (shift : Nat) (hshift : shift < 256) :
    UInt256.shiftRight word (UInt256.ofNat shift) = UInt256.div word (UInt256.ofNat (2^shift)) := by
  have hs : shift < UInt256.size := lt_trans hshift (by decide)
  have hp : 2^shift < UInt256.size := by
    change 2^shift < 2^256
    exact Nat.pow_lt_pow_right (by decide) hshift
  apply u256_inj
  rw [udiv_toNat, ulit_toNat' _ hp]
  unfold UInt256.shiftRight UInt256.toNat
  rw [if_neg]
  · rw [Fin.shiftRight_val, Nat.shiftRight_eq_div_pow]
    change word.toNat / 2^((UInt256.ofNat shift).toNat) = word.toNat / 2^shift
    rw [ulit_toNat' shift hs]
  · change ¬ 256 ≤ (UInt256.ofNat shift).toNat
    rw [ulit_toNat' shift hs]
    omega

def storedBytesLengthWord (header : UInt256) : UInt256 :=
  if UInt256.land header ⟨1⟩ = ⟨0⟩ then UInt256.land (UInt256.div header ⟨2⟩) ⟨127⟩ else UInt256.div header ⟨2⟩

def storedBytesValid (header : UInt256) : Prop :=
  UInt256.land header ⟨1⟩ ≠ UInt256.lt (storedBytesLengthWord header) ⟨32⟩
instance (header : UInt256) : Decidable (storedBytesValid header) := inferInstanceAs (Decidable (_ ≠ _))

theorem storedBytesDecode (header : UInt256) : solidityDecodeBytesLengthHeader header =
    if storedBytesValid header then .ok (storedBytesLengthWord header).toNat else .revert := by
  unfold solidityDecodeBytesLengthHeader
  change (if UInt256.sub (UInt256.land header ⟨1⟩) (UInt256.lt (storedBytesLengthWord header) ⟨32⟩) = ⟨0⟩ then _ else _) = _
  simp only [u256_sub_eq_zero_iff_eq]
  by_cases h : storedBytesValid header
  · rw [if_neg h, if_pos h]
    rfl
  · rw [if_pos (not_not.mp h), if_neg h]

theorem easStoredLength_prepare {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap}
    {k C : Nat} {header ret : UInt256} {R : List UInt256} (v : EASImmutables)
    (hstack : R.length + 5 ≤ 1024)
    (rd : RD fork (deployedRuntime v) ee g s0 ⟨6418⟩ (header :: ret :: R) mem aw rdata σ k C) :
    ∃ k' C', RD fork (deployedRuntime v) ee g s0 ⟨6433⟩
      (UInt256.land header ⟨1⟩ :: ret :: storedBytesLengthWord header :: R) mem aw rdata σ k' C' := by
  by_cases hf : UInt256.land header ⟨1⟩ = ⟨0⟩
  · have rd1 := easBlocks.eas_block_6418_taken (immWords := wordsOf (immStore v)) hstack
      (by change UInt256.isZero (UInt256.land header ⟨1⟩) ≠ (⟨0⟩ : UInt256); rw [hf]; decide) (by rw [easPatchedValidJumpsRuntime v]; jump_dest) rd
    have rd2 := easBlocks.eas_block_6491 (immWords := wordsOf (immStore v)) (by omega)
      (by rw [easPatchedValidJumpsRuntime v]; jump_dest) rd1
    refine ⟨k + 12 + 7, C + 41 + 24, ?_⟩
    simpa only [easBlocks.eas_block_6418_taken_stack, easBlocks.eas_block_6491_stack,
      storedBytesLengthWord, if_pos hf, wordShiftRight_div header 1 (by decide),
      u256_land_comm (UInt256.ofNat 127)] using rd2
  · have rd1 := easBlocks.eas_block_6418_fallthrough (immWords := wordsOf (immStore v)) hstack
      (isZero_eq_zero_of_ne hf) rd
    refine ⟨k + 12, C + 41, ?_⟩
    simpa only [easBlocks.eas_block_6418_fallthrough_stack, storedBytesLengthWord, hf, if_false,
      wordShiftRight_div header 1 (by decide)] using rd1

theorem easStoredLength {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap}
    {k C : Nat} {header ret : UInt256} {R : List UInt256} (v : EASImmutables)
    (hstack : R.length + 5 ≤ 1024)
    (hvalid : (D_J (deployedRuntime v) 0).contains ret = true)
    (rd : RD fork (deployedRuntime v) ee g s0 ⟨6418⟩ (header :: ret :: R) mem aw rdata σ k C) :
    if storedBytesValid header then
      ∃ k' C', RD fork (deployedRuntime v) ee g s0 ret (storedBytesLengthWord header :: R) mem aw rdata σ k' C'
    else RDrev fork (deployedRuntime v) g s0 := by
  obtain ⟨k1, C1, rd1⟩ := easStoredLength_prepare v hstack rd
  by_cases hv : storedBytesValid header
  · rw [if_pos hv]
    have heq : UInt256.eq (UInt256.lt (storedBytesLengthWord header) ⟨32⟩) (UInt256.land header ⟨1⟩) = ⟨0⟩ :=
      uInt256_eq_zero_of_ne (fun h => hv (uInt256_eq_one_eq h).symm)
    have rd2 := easBlocks.eas_block_6433_fallthrough (immWords := wordsOf (immStore v)) hstack heq rd1
    have rd3 := easBlocks.eas_block_6443 (immWords := wordsOf (immStore v))
      (by simp only [List.length_cons]; omega) hvalid rd2
    exact ⟨_, _, rd3⟩
  · rw [if_neg hv]
    have heq : UInt256.eq (UInt256.lt (storedBytesLengthWord header) ⟨32⟩) (UInt256.land header ⟨1⟩) ≠ ⟨0⟩ := by
      rw [show UInt256.land header ⟨1⟩ = UInt256.lt (storedBytesLengthWord header) ⟨32⟩ from not_not.mp hv,
        uInt256_eq_self]
      decide
    have rd2 := easBlocks.eas_block_6433_taken (immWords := wordsOf (immStore v)) hstack heq
      (by rw [easPatchedValidJumpsRuntime v]; jump_dest) rd1
    exact easBlocks.eas_block_6444 (immWords := wordsOf (immStore v))
      (by simp only [easBlocks.eas_block_6433_taken_stack, List.length_cons]; omega) rd2

theorem storedBytesLength_bound (header : UInt256) : (storedBytesLengthWord header).toNat < 2^255 := by
  unfold storedBytesLengthWord
  split
  · have hb := u256LandMaskToNatLtOfToNat (bits := 7) (UInt256.div header ⟨2⟩) ⟨127⟩ (by decide)
    change (UInt256.land (UInt256.div header ⟨2⟩) ⟨127⟩).toNat < 2^7 at hb
    omega
  · exact u256_div2_toNat_lt_sign rfl

theorem storedBytesValid_short {header : UInt256}
    (hf : UInt256.land header ⟨1⟩ = ⟨0⟩) (hv : storedBytesValid header) :
    (storedBytesLengthWord header).toNat < 32 := by
  by_contra hn
  apply hv
  exact hf.trans (ult_zero (by change 32 ≤ (storedBytesLengthWord header).toNat; omega)).symm

theorem storedBytesValid_long {header : UInt256}
    (hf : UInt256.land header ⟨1⟩ ≠ ⟨0⟩) (hv : storedBytesValid header) :
    32 ≤ (storedBytesLengthWord header).toNat := by
  by_contra hn
  apply hv
  exact (land_one_eq_one_of_ne_zero hf).trans
    (ult_one (by change (storedBytesLengthWord header).toNat < 32; omega)).symm

-- LIBRARY CANDIDATE: solc's short-byte allocation uses one word exactly when the length is nonzero.
theorem shortBytesRounded (len : UInt256) (hb : len.toNat < 32) :
    UInt256.shiftLeft (UInt256.isZero (UInt256.isZero len)) (UInt256.ofNat 5) =
      UInt256.ofNat (32 * ((len.toNat + 31) / 32)) := by
  by_cases hz : len = ⟨0⟩
  · subst len
    decide
  · rw [isZero_eq_zero_of_ne hz]
    have hn : len.toNat ≠ 0 := fun h => hz (uint256_toNat_eq_zero h)
    rw [show (len.toNat + 31) / 32 = 1 by omega]
    decide

end Benchmarks.EAS.EAS
