import Benchmarks.Morpho.MetaMorphoV1_1.StructAllocationRoutines
import Benchmarks.Morpho.MetaMorphoV1_1.RuntimeBlocks_069
import Benchmarks.Morpho.MetaMorphoV1_1.RuntimeBlocks_070
import Benchmarks.Morpho.MetaMorphoV1_1.RuntimeBlocks_076
import Benchmarks.Morpho.MetaMorphoV1_1.RuntimeBlocks_078
import Benchmarks.Morpho.MetaMorphoV1_1.RuntimeBlocks_018
import Benchmarks.Morpho.MetaMorphoV1_1.RuntimeBlocks_009

/-! Allocation and length checks for the six-word market return value. -/

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables
open Benchmarks.Morpho.MetaMorphoV1_1.Immutables metaMorphoV1_1Blocks

namespace Benchmarks.Morpho.MetaMorphoV1_1.SourceMemory

attribute [local irreducible] metaMorphoV1_1Bytecode
set_option autoImplicit false

def marketReservedMem (mem : ByteArray) (ptr : UInt256) : ByteArray :=
  writeWord (writeWord mem 64 (nextCursor ptr ⟨192⟩)) 64
    (nextCursor (nextCursor ptr ⟨192⟩) ⟨192⟩)

set_option maxRecDepth 2000 in
theorem marketCallFailure {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem out : ByteArray} {aw : UInt256} {σ : AccountMap}
    {k C : Nat} {ptr params : UInt256} {R : List UInt256}
    (v : MetaMorphoV1_1Immutables) (hstack : R.length + 8 ≤ 1024)
    (hout : out.size < UInt256.size)
    (rd : RD (deployedRuntime v) I g s0 ⟨16953⟩ (⟨0⟩ :: params :: ptr :: R)
      mem aw out σ k C) : RDrev (deployedRuntime v) g s0 := by
  have hfail := metaMorphoV1_1_block_16953_taken
    (immWords := wordsOf (immStore v)) (by omega) (by decide)
    (by rw [metaMorphoV1_1PatchedValidJumpsRuntime v]; jump_dest) rd
  exact metaMorphoV1_1_block_2921 (immWords := wordsOf (immStore v))
    (by simp only [metaMorphoV1_1_block_16953_taken_stack, List.length_cons]; omega)
    (by change 0 + (UInt256.ofNat out.size).toNat ≤ out.size
        rw [UInt256.toNat_ofNat_of_lt hout, Nat.zero_add]) hfail

set_option maxRecDepth 2000 in
theorem marketReturnAllocation {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem out : ByteArray} {aw : UInt256} {σ : AccountMap}
    {k C : Nat} {ptr params : UInt256} {R : List UInt256}
    (v : MetaMorphoV1_1Immutables) (hstack : R.length + 12 ≤ 1024)
    (hout : out.size < UInt256.size)
    (rd : RD (deployedRuntime v) I g s0 ⟨16953⟩ (⟨1⟩ :: params :: ptr :: R)
      mem aw out σ k C) :
    (¬ (192 ≤ out.size ∧ allocationFits ptr ⟨384⟩) ∧
      RDrev (deployedRuntime v) g s0) ∨
    (192 ≤ out.size ∧ allocationFits ptr ⟨384⟩ ∧ ∃ aw' k' C',
      RD (deployedRuntime v) I g s0 ⟨14858⟩
        (ptr :: ⟨160⟩ :: ⟨14943⟩ :: nextCursor ptr ⟨192⟩ :: ⟨17648⟩ :: params :: R)
        (marketReservedMem mem ptr) aw' out σ k' C') := by
  have h1 := metaMorphoV1_1_block_16953_fallthrough
    (immWords := wordsOf (immStore v)) (by omega) (by decide) rd
  have h2 := metaMorphoV1_1_block_16960_taken
    (immWords := wordsOf (immStore v)) (by omega) (by decide)
    (by rw [metaMorphoV1_1PatchedValidJumpsRuntime v]; jump_dest) h1
  by_cases hlong : 192 ≤ out.size
  · have h3 := metaMorphoV1_1_block_17622_fallthrough
      (immWords := wordsOf (immStore v)) (by omega)
      (ugt_zero (by simpa only [UInt256.toNat_ofNat_of_lt hout] using hlong)) h2
    have h4 := metaMorphoV1_1_block_17639 (immWords := wordsOf (immStore v))
      (by simp only [List.length_cons]; omega)
      (by rw [metaMorphoV1_1PatchedValidJumpsRuntime v]; jump_dest) h3
    by_cases hfirst : allocationFits ptr ⟨192⟩
    · obtain ⟨aw5, k5, C5, h5⟩ := allocateRoundedReturn v
        (by simp only [List.length_cons]; omega) hfirst
        (by rw [metaMorphoV1_1PatchedValidJumps v]; jump_dest) h4
      have h6 := metaMorphoV1_1_block_15218 (immWords := wordsOf (immStore v))
        (by simp only [List.length_cons]; omega)
        (by rw [metaMorphoV1_1PatchedValidJumpsRuntime v]; jump_dest) h5
      have h7 := metaMorphoV1_1_block_14829_fallthrough
        (immWords := wordsOf (immStore v)) (by simp only [List.length_cons]; omega)
        (by rw [word_add_sub_left]; decide +kernel) h6
      have h8 := metaMorphoV1_1_block_14841 (immWords := wordsOf (immStore v))
        (by simp only [List.length_cons]; omega)
        (by rw [metaMorphoV1_1PatchedValidJumpsRuntime v]; jump_dest) h7
      have hfree : memLoad (UInt256.ofNat 64) (writeWord mem 64 (nextCursor ptr ⟨192⟩)) =
          nextCursor ptr ⟨192⟩ := loadedWord_of_read
        (by change 64 + 32 ≤ _; rw [writeWord_sparse_size]; omega)
        (writeWord_sparse_read_back _ _ _)
      simp only [metaMorphoV1_1_block_14841_stack, hfree] at h8
      by_cases hsecond : allocationFits (nextCursor ptr ⟨192⟩) ⟨192⟩
      · obtain ⟨aw9, k9, C9, h9⟩ := allocateStruct192Return v
          (by simp only [List.length_cons]; omega) hsecond
          (by rw [metaMorphoV1_1PatchedValidJumps v]; jump_dest) h8
        exact .inr ⟨hlong, (allocationFits_192_twice ptr).mpr ⟨hfirst, hsecond⟩,
          aw9, k9, C9, h9⟩
      · exact .inl ⟨fun hc ↦ hsecond ((allocationFits_192_twice ptr).mp hc.2).2,
          allocateStruct192Revert v (by simp only [List.length_cons]; omega) hsecond h8⟩
    · exact .inl ⟨fun hc ↦ hfirst ((allocationFits_192_twice ptr).mp hc.2).1,
        allocateRoundedRevert v (by simp only [List.length_cons]; omega) hfirst h4⟩
  · have h3 := metaMorphoV1_1_block_17622_taken
      (immWords := wordsOf (immStore v)) (by omega)
      (by rw [ugt_one (by simpa only [UInt256.toNat_ofNat_of_lt hout] using
            Nat.lt_of_not_ge hlong)]; decide)
      (by rw [metaMorphoV1_1PatchedValidJumpsRuntime v]; jump_dest) h2
    have h4 := metaMorphoV1_1_block_15234 (immWords := wordsOf (immStore v))
      (by simp only [List.length_cons]; omega)
      (by rw [metaMorphoV1_1PatchedValidJumpsRuntime v]; jump_dest) h3
    have h5 := metaMorphoV1_1_block_15208 (immWords := wordsOf (immStore v))
      (by simp only [List.length_cons]; omega)
      (by rw [metaMorphoV1_1PatchedValidJumpsRuntime v]; jump_dest) h4
    refine .inl ⟨fun hc ↦ hlong hc.1, ?_⟩
    by_cases hfirst : allocationFits ptr (UInt256.ofNat out.size)
    · obtain ⟨aw6, k6, C6, h6⟩ := allocateRoundedReturn v
        (by simp only [List.length_cons]; omega) hfirst
        (by rw [metaMorphoV1_1PatchedValidJumps v]; jump_dest) h5
      have h7 := metaMorphoV1_1_block_15218 (immWords := wordsOf (immStore v))
        (by simp only [List.length_cons]; omega)
        (by rw [metaMorphoV1_1PatchedValidJumpsRuntime v]; jump_dest) h6
      have h8 := metaMorphoV1_1_block_14829_taken
        (immWords := wordsOf (immStore v)) (by simp only [List.length_cons]; omega)
        (by rw [word_add_sub_left, slt_ofNat_lit_one_low (by decide) (by omega)]; decide)
        (by rw [metaMorphoV1_1PatchedValidJumpsRuntime v]; jump_dest) h7
      exact metaMorphoV1_1_block_917 (immWords := wordsOf (immStore v))
        (by simp only [metaMorphoV1_1_block_14829_taken_stack, List.length_cons]; omega) h8
    · exact allocateRoundedRevert v (by simp only [List.length_cons]; omega) hfirst h5

end Benchmarks.Morpho.MetaMorphoV1_1.SourceMemory
