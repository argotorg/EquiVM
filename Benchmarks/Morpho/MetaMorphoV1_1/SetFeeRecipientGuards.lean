import Benchmarks.Morpho.MetaMorphoV1_1.SetFeeRecipientEntry

/-! The unchanged-recipient and zero-recipient fee guards in the bytecode. -/

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach Reasoning.Immutables
open Benchmarks.Morpho.MetaMorphoV1_1.Immutables metaMorphoV1_1Blocks

namespace Benchmarks.Morpho.MetaMorphoV1_1

attribute [local irreducible] metaMorphoV1_1Bytecode
set_option maxRecDepth 2000

def feeRecipientInvalidWord (old value : UInt256) : UInt256 :=
  if value = ⟨0⟩ then
    UInt256.isZero (UInt256.isZero (UInt256.land old (UInt256.ofNat (2 ^ 96 - 1))))
  else ⟨0⟩

theorem feeRecipientInvalidWord_zero (old value : UInt256)
    (hvalid : ¬ (value = ⟨0⟩ ∧ UInt256.land old (UInt256.ofNat (2 ^ 96 - 1)) ≠ ⟨0⟩)) :
    feeRecipientInvalidWord old value = ⟨0⟩ := by
  by_cases hz : value = ⟨0⟩
  · have hf : UInt256.land old (UInt256.ofNat (2 ^ 96 - 1)) = ⟨0⟩ := by
      by_contra hf
      exact hvalid ⟨hz, hf⟩
    simp only [feeRecipientInvalidWord, hz, if_pos, hf]; rfl
  · simp only [feeRecipientInvalidWord, if_neg hz]

theorem setFeeRecipientDifferentGuard {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap}
    {k C : Nat} {w : UInt256} {R : List UInt256}
    (v : MetaMorphoV1_1Immutables) (hstack : R.length + 5 ≤ 1024)
    (hcanon : w.toNat < EVM.addressModulus)
    (hne : w ≠ UInt256.shiftRight (codeOwnerStorageWord I σ ⟨18⟩) ⟨96⟩)
    (rd : RD (deployedRuntime v) I g s0 ⟨1191⟩ (w :: R) mem aw rdata σ k C) :
    ∃ aw' k' C', RD (deployedRuntime v) I g s0 ⟨1218⟩
      (codeOwnerStorageWord I σ ⟨18⟩ :: w :: w :: R) mem aw' rdata σ k' C' := by
  have hm : UInt256.land w (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1)
      (UInt256.ofNat 160)) (UInt256.ofNat 1)) = w := solcAddrMask_clean hcanon
  obtain ⟨aw1, k1, C1, h1⟩ := metaMorphoV1_1_block_1191_fallthrough_packed
    (immWords := wordsOf (immStore v)) hstack (by rw [hm]; exact u256_eq_of_ne hne) rd
  simp only [metaMorphoV1_1_block_1191_fallthrough_stack, hm] at h1
  exact ⟨aw1, k1, C1, h1⟩

theorem setFeeRecipientSameRevert {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap}
    {k C : Nat} {w : UInt256} {R : List UInt256}
    (v : MetaMorphoV1_1Immutables) (hstack : R.length + 5 ≤ 1024)
    (hcanon : w.toNat < EVM.addressModulus)
    (heq : w = UInt256.shiftRight (codeOwnerStorageWord I σ ⟨18⟩) ⟨96⟩)
    (rd : RD (deployedRuntime v) I g s0 ⟨1191⟩ (w :: R) mem aw rdata σ k C) :
    RDrev (deployedRuntime v) g s0 := by
  have hm : UInt256.land w (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1)
      (UInt256.ofNat 160)) (UInt256.ofNat 1)) = w := solcAddrMask_clean hcanon
  obtain ⟨aw1, k1, C1, h1⟩ := metaMorphoV1_1_block_1191_taken_packed
    (immWords := wordsOf (immStore v)) hstack (by
      rw [hm]
      change UInt256.eq w (UInt256.shiftRight (codeOwnerStorageWord I σ ⟨18⟩) ⟨96⟩) ≠ ⟨0⟩
      rw [heq]; simp only [UInt256.eq]; decide)
    (by rw [metaMorphoV1_1PatchedValidJumpsRuntime v]; jump_dest) rd
  exact metaMorphoV1_1_block_1143 (immWords := wordsOf (immStore v))
    (by simp only [metaMorphoV1_1_block_1191_taken_stack, List.length_cons]; omega) h1

theorem setFeeRecipientReachValidity {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap}
    {k C : Nat} {old w tag : UInt256} {R : List UInt256}
    (v : MetaMorphoV1_1Immutables) (hstack : R.length + 8 ≤ 1024)
    (rd : RD (deployedRuntime v) I g s0 ⟨1218⟩
      (old :: w :: w :: tag :: R) mem aw rdata σ k C) :
    ∃ junk aw' k' C', RD (deployedRuntime v) I g s0 ⟨1226⟩
      (junk :: feeRecipientInvalidWord old w :: w :: w :: tag :: R) mem aw' rdata σ k' C' := by
  by_cases hz : w = ⟨0⟩
  · obtain ⟨aw1, k1, C1, h1⟩ := metaMorphoV1_1_block_1218_taken_packed
      (immWords := wordsOf (immStore v)) (by simp only [List.length_cons]; omega)
      (by rw [hz]; decide) (by rw [metaMorphoV1_1PatchedValidJumpsRuntime v]; jump_dest) rd
    obtain ⟨aw2, k2, C2, h2⟩ := metaMorphoV1_1_block_1317_packed
      (immWords := wordsOf (immStore v)) hstack
      (by rw [metaMorphoV1_1PatchedValidJumpsRuntime v]; jump_dest) h1
    refine ⟨tag, aw2, k2, C2, ?_⟩
    simpa only [feeRecipientInvalidWord, if_pos hz] using h2
  · obtain ⟨aw1, k1, C1, h1⟩ := metaMorphoV1_1_block_1218_fallthrough_packed
      (immWords := wordsOf (immStore v)) (by simp only [List.length_cons]; omega)
      (isZero_eq_zero_of_ne hz) rd
    refine ⟨old, aw1, k1, C1, ?_⟩
    simpa only [metaMorphoV1_1_block_1218_fallthrough_stack, isZero_eq_zero_of_ne hz,
      feeRecipientInvalidWord, if_neg hz] using h1

theorem setFeeRecipientReachAccrual {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap}
    {k C : Nat} {old w tag : UInt256} {R : List UInt256}
    (v : MetaMorphoV1_1Immutables) (hstack : R.length + 8 ≤ 1024)
    (hvalid : ¬ (w = ⟨0⟩ ∧ UInt256.land old (UInt256.ofNat (2 ^ 96 - 1)) ≠ ⟨0⟩))
    (rd : RD (deployedRuntime v) I g s0 ⟨1218⟩
      (old :: w :: w :: tag :: R) mem aw rdata σ k C) :
    ∃ aw' k' C', RD (deployedRuntime v) I g s0 ⟨14262⟩
      (⟨1239⟩ :: w :: w :: tag :: R) mem aw' rdata σ k' C' := by
  obtain ⟨junk, aw1, k1, C1, h1⟩ := setFeeRecipientReachValidity v hstack rd
  obtain ⟨aw2, k2, C2, h2⟩ := metaMorphoV1_1_block_1226_fallthrough_packed
    (immWords := wordsOf (immStore v)) (by simp only [List.length_cons]; omega)
    (feeRecipientInvalidWord_zero old w hvalid) h1
  exact metaMorphoV1_1_block_1232_packed (immWords := wordsOf (immStore v))
    (by simp only [metaMorphoV1_1_block_1226_fallthrough_stack, List.length_cons]; omega)
    (by rw [metaMorphoV1_1PatchedValidJumpsRuntime v]; jump_dest) h2

theorem setFeeRecipientInvalidRevert {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap}
    {k C : Nat} {old w tag : UInt256} {R : List UInt256}
    (v : MetaMorphoV1_1Immutables) (hstack : R.length + 8 ≤ 1024)
    (hbad : w = ⟨0⟩ ∧ UInt256.land old (UInt256.ofNat (2 ^ 96 - 1)) ≠ ⟨0⟩)
    (rd : RD (deployedRuntime v) I g s0 ⟨1218⟩
      (old :: w :: w :: tag :: R) mem aw rdata σ k C) :
    RDrev (deployedRuntime v) g s0 := by
  obtain ⟨junk, aw1, k1, C1, h1⟩ := setFeeRecipientReachValidity v hstack rd
  have hc : feeRecipientInvalidWord old w ≠ ⟨0⟩ := by
    rw [feeRecipientInvalidWord, if_pos hbad.1, isZero_eq_zero_of_ne hbad.2]
    decide
  obtain ⟨aw2, k2, C2, h2⟩ := metaMorphoV1_1_block_1226_taken_packed
    (immWords := wordsOf (immStore v)) (by simp only [List.length_cons]; omega) hc
    (by rw [metaMorphoV1_1PatchedValidJumpsRuntime v]; jump_dest) h1
  exact metaMorphoV1_1_block_1302 (immWords := wordsOf (immStore v))
    (by simp only [metaMorphoV1_1_block_1226_taken_stack, List.length_cons]; omega) h2

end Benchmarks.Morpho.MetaMorphoV1_1
