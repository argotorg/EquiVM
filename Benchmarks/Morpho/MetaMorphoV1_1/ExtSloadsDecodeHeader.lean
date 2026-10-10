import Benchmarks.Morpho.MetaMorphoV1_1.ExtSloadsDecodeABI
import Benchmarks.Morpho.MetaMorphoV1_1.AllocationRoutines
import Benchmarks.Morpho.MetaMorphoV1_1.RuntimeBlocks_064
import Benchmarks.Morpho.MetaMorphoV1_1.WordArraySizeRuntime
import Benchmarks.Morpho.MetaMorphoV1_1.RuntimeBlocks_009

/-! The compiled dynamic-return decoder's offset and length checks. -/

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables
open Benchmarks.Morpho.MetaMorphoV1_1.Immutables
open metaMorphoV1_1Blocks

namespace Benchmarks.Morpho.MetaMorphoV1_1.SourceMemory

attribute [local irreducible] metaMorphoV1_1Bytecode
set_option autoImplicit false

def extSloadsHeaderChecks (out : ByteArray) : Prop :=
  32 ≤ out.size ∧ extSloadsReturnOffset out ≤ solcMaxU64 ∧
    extSloadsReturnOffset out + 32 ≤ out.size ∧ extSloadsReturnCount out ≤ solcMaxU64

theorem extSloadsReturnChecks_header {out : ByteArray} (h : extSloadsReturnChecks out) :
    extSloadsHeaderChecks out := ⟨h.head, h.offset, h.lengthWord, h.length⟩

set_option maxRecDepth 2000 in
theorem extSloadsDecodeHeader {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem : ByteArray} {aw : UInt256} {out : ByteArray} {σ : AccountMap}
    {k C base : Nat} {R : List UInt256}
    (v : MetaMorphoV1_1Immutables) (hstack : R.length + 10 ≤ 1024)
    (hbound : base + out.size ≤ 2 ^ 200)
    (hread : ∀ off, off + 32 ≤ out.size →
      memLoad (UInt256.ofNat (base + off)) mem = calldataWord out off)
    (rd : RD (deployedRuntime v) I g s0 ⟨13221⟩
      (UInt256.ofNat base :: UInt256.ofNat (base + out.size) :: R) mem aw out σ k C) :
    (¬ extSloadsHeaderChecks out ∧ RDrev (deployedRuntime v) g s0) ∨
      (extSloadsHeaderChecks out ∧ ∃ aw' k' C',
        RD (deployedRuntime v) I g s0 ⟨13272⟩
          (UInt256.ofNat (32 + 32 * extSloadsReturnCount out) ::
            UInt256.ofNat (extSloadsReturnCount out) :: UInt256.ofNat (base + out.size) ::
            UInt256.ofNat (base + extSloadsReturnOffset out) :: R) mem aw' out σ k' C') := by
  have hsign : out.size < 2 ^ 255 := by omega
  have hfit : base + out.size < UInt256.size := by change _ < 2 ^ 256; omega
  have hsub : UInt256.sub (UInt256.ofNat (base + out.size)) (UInt256.ofNat base) =
      UInt256.ofNat out.size := by
    rw [ofNat_sub_words (by omega) hfit, Nat.add_sub_cancel_left]
  by_cases hhead : 32 ≤ out.size
  · have h1 := metaMorphoV1_1_block_13221_fallthrough
      (immWords := wordsOf (immStore v)) (by omega)
      (by rw [hsub]; exact slt_ofNat_lit_zero (by decide) hhead hsign) rd
    have hload : memLoad (UInt256.ofNat base) mem =
        UInt256.ofNat (extSloadsReturnOffset out) := by
      simpa only [Nat.add_zero, extSloadsReturnOffset, Benchmarks.EAS.Attester.returnArrayOffset,
        u256_ofNat_toNat] using hread 0 (by omega)
    have hofffit : extSloadsReturnOffset out < UInt256.size :=
      (calldataWord out 0).val.isLt
    by_cases hoff : extSloadsReturnOffset out ≤ solcMaxU64
    · have h2 := metaMorphoV1_1_block_13232_fallthrough
        (immWords := wordsOf (immStore v)) (by simp only [List.length_cons]; omega)
        (by rw [hload]; apply ugt_zero
            simpa only [UInt256.toNat_ofNat_of_lt hofffit] using hoff) h1
      simp only [metaMorphoV1_1_block_13232_fallthrough_stack, hload] at h2
      have ho : base + extSloadsReturnOffset out + 31 < 2 ^ 255 := by
        change extSloadsReturnOffset out ≤ 18446744073709551615 at hoff
        omega
      by_cases hword : extSloadsReturnOffset out + 32 ≤ out.size
      · have h3 := metaMorphoV1_1_block_13249_fallthrough
          (immWords := wordsOf (immStore v)) (by omega)
          (by
            rw [ofNat_add_words, ofNat_add_words,
              slt_ofNat_lit_one_low (by omega) (by omega)]
            decide) h2
        simp only [metaMorphoV1_1_block_13249_fallthrough_stack, ofNat_add_words] at h3
        have hlen : memLoad (UInt256.ofNat (base + extSloadsReturnOffset out)) mem =
            UInt256.ofNat (extSloadsReturnCount out) := by
          simpa only [extSloadsReturnCount, Benchmarks.EAS.Attester.returnArrayCount,
            u256_ofNat_toNat] using hread (extSloadsReturnOffset out) hword
        have hnfit : extSloadsReturnCount out < UInt256.size :=
          (calldataWord out (extSloadsReturnOffset out)).val.isLt
        have h4 := metaMorphoV1_1_block_13262
          (immWords := wordsOf (immStore v)) (by omega)
          (by rw [metaMorphoV1_1PatchedValidJumpsRuntime v]; jump_dest) h3
        simp only [metaMorphoV1_1_block_13262_stack, hlen] at h4
        by_cases hcount : extSloadsReturnCount out ≤ solcMaxU64
        · obtain ⟨k5, C5, h5⟩ := wordArraySizeReturn v
            (by simp only [List.length_cons]; omega)
            (by simpa only [UInt256.toNat_ofNat_of_lt hnfit] using hcount)
            (by rw [metaMorphoV1_1PatchedValidJumps v]; jump_dest) h4
          simp only [UInt256.toNat_ofNat_of_lt hnfit] at h5
          exact .inr ⟨⟨hhead, hoff, hword, hcount⟩, _, k5, C5, h5⟩
        · exact .inl ⟨fun hc ↦ hcount hc.2.2.2, wordArraySizeRevert v
            (by simp only [List.length_cons]; omega)
            (by simpa only [UInt256.toNat_ofNat_of_lt hnfit] using
              Nat.lt_of_not_ge hcount) h4⟩
      · have h3 := metaMorphoV1_1_block_13249_taken
          (immWords := wordsOf (immStore v)) (by omega)
          (by rw [ofNat_add_words, ofNat_add_words,
                slt_ofNat_lit_zero (by omega) (by omega) ho]
              decide)
          (by rw [metaMorphoV1_1PatchedValidJumpsRuntime v]; jump_dest) h2
        exact .inl ⟨fun hc => hword hc.2.2.1,
          metaMorphoV1_1_block_917 (immWords := wordsOf (immStore v))
            (by simp only [metaMorphoV1_1_block_13249_taken_stack, List.length_cons]; omega) h3⟩
    · have h2 := metaMorphoV1_1_block_13232_taken
        (immWords := wordsOf (immStore v)) (by simp only [List.length_cons]; omega)
        (by rw [hload, ugt_one (by
              simpa only [UInt256.toNat_ofNat_of_lt hofffit] using Nat.lt_of_not_ge hoff)]
            decide)
        (by rw [metaMorphoV1_1PatchedValidJumpsRuntime v]; jump_dest) h1
      exact .inl ⟨fun hc => hoff hc.2.1,
        metaMorphoV1_1_block_917 (immWords := wordsOf (immStore v))
          (by simp only [metaMorphoV1_1_block_13232_taken_stack, List.length_cons]; omega) h2⟩
  · have h1 := metaMorphoV1_1_block_13221_taken
      (immWords := wordsOf (immStore v)) (by omega)
      (by rw [hsub, slt_ofNat_lit_one_low (by decide) (by omega)]; decide)
      (by rw [metaMorphoV1_1PatchedValidJumpsRuntime v]; jump_dest) rd
    exact .inl ⟨fun hc => hhead hc.1,
      metaMorphoV1_1_block_917 (immWords := wordsOf (immStore v))
        (by simp only [List.length_cons]; omega) h1⟩

end Benchmarks.Morpho.MetaMorphoV1_1.SourceMemory
