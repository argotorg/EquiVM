import Benchmarks.Morpho.MetaMorphoV1_1.BorrowRateCall
import Benchmarks.Morpho.MetaMorphoV1_1.StructReturnMemory
import Benchmarks.Morpho.MetaMorphoV1_1.AllocationRoutines
import Benchmarks.Morpho.MetaMorphoV1_1.RuntimeBlocks_078
import Benchmarks.Morpho.MetaMorphoV1_1.RuntimeBlocks_018
import Benchmarks.Morpho.MetaMorphoV1_1.RuntimeBlocks_009

/-! Reverts and the bounded 32-byte reservation following the rate-model call. -/

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables
open Benchmarks.Morpho.MetaMorphoV1_1.Immutables metaMorphoV1_1Blocks

namespace Benchmarks.Morpho.MetaMorphoV1_1.SourceMemory

attribute [local irreducible] metaMorphoV1_1Bytecode
set_option autoImplicit false

set_option maxRecDepth 2000 in
theorem borrowRateCallFailure {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem out : ByteArray} {aw : UInt256} {σ : AccountMap}
    {k C : Nat} {ptr elapsed feePtr : UInt256} {R : List UInt256}
    (v : MetaMorphoV1_1Immutables) (hstack : R.length + 9 ≤ 1024)
    (hout : out.size < UInt256.size)
    (rd : RD (deployedRuntime v) I g s0 ⟨17226⟩ (⟨0⟩ :: elapsed :: feePtr :: ptr :: R)
      mem aw out σ k C) : RDrev (deployedRuntime v) g s0 := by
  have hfail := metaMorphoV1_1_block_17226_taken
    (immWords := wordsOf (immStore v)) (by omega) (by decide)
    (by rw [metaMorphoV1_1PatchedValidJumpsRuntime v]; jump_dest) rd
  exact metaMorphoV1_1_block_2921 (immWords := wordsOf (immStore v))
    (by simp only [metaMorphoV1_1_block_17226_taken_stack, List.length_cons]; omega)
    (by change 0 + (UInt256.ofNat out.size).toNat ≤ out.size
        rw [UInt256.toNat_ofNat_of_lt hout, Nat.zero_add]) hfail

set_option maxRecDepth 2000 in
theorem borrowRateReturnAllocation {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem out : ByteArray} {aw : UInt256} {σ : AccountMap}
    {k C : Nat} {ptr elapsed feePtr : UInt256} {R : List UInt256}
    (v : MetaMorphoV1_1Immutables) (hstack : R.length + 12 ≤ 1024)
    (hout : out.size < UInt256.size)
    (rd : RD (deployedRuntime v) I g s0 ⟨17226⟩ (⟨1⟩ :: elapsed :: feePtr :: ptr :: R)
      mem aw out σ k C) :
    (¬ (32 ≤ out.size ∧ allocationFits ptr ⟨32⟩) ∧ RDrev (deployedRuntime v) g s0) ∨
    (32 ≤ out.size ∧ allocationFits ptr ⟨32⟩ ∧ ∃ aw' k' C',
      RD (deployedRuntime v) I g s0 ⟨17560⟩ (elapsed :: feePtr :: ptr :: R)
        (writeWord mem 64 (nextCursor ptr ⟨32⟩)) aw' out σ k' C') := by
  have h1 := metaMorphoV1_1_block_17226_fallthrough
    (immWords := wordsOf (immStore v)) (by omega) (by decide) rd
  have h2 := metaMorphoV1_1_block_17233_taken
    (immWords := wordsOf (immStore v)) (by omega) (by decide)
    (by rw [metaMorphoV1_1PatchedValidJumpsRuntime v]; jump_dest) h1
  by_cases hl : 32 ≤ out.size
  · have h3 := metaMorphoV1_1_block_17524_fallthrough
      (immWords := wordsOf (immStore v)) (by omega)
      (ugt_zero (by simpa only [UInt256.toNat_ofNat_of_lt hout] using hl)) h2
    have h4 := metaMorphoV1_1_block_17538 (immWords := wordsOf (immStore v))
      (by simp only [List.length_cons]; omega)
      (by rw [metaMorphoV1_1PatchedValidJumpsRuntime v]; jump_dest) h3
    by_cases hf : allocationFits ptr ⟨32⟩
    · obtain ⟨aw5, k5, C5, h5⟩ := allocateRoundedReturn v
        (by simp only [List.length_cons]; omega) hf
        (by rw [metaMorphoV1_1PatchedValidJumps v]; jump_dest) h4
      obtain ⟨aw6, k6, C6, h6⟩ := metaMorphoV1_1_block_17551_fallthrough_packed
        (immWords := wordsOf (immStore v)) (by simp only [List.length_cons]; omega)
        (by rw [word_add_sub_left]; decide +kernel) h5
      exact .inr ⟨hl, hf, aw6, k6, C6, h6⟩
    · exact .inl ⟨fun hgood ↦ hf hgood.2,
        allocateRoundedRevert v (by simp only [List.length_cons]; omega) hf h4⟩
  · have h3 := metaMorphoV1_1_block_17524_taken
      (immWords := wordsOf (immStore v)) (by omega)
      (by rw [ugt_one (by simpa only [UInt256.toNat_ofNat_of_lt hout] using
            Nat.lt_of_not_ge hl)]; decide)
      (by rw [metaMorphoV1_1PatchedValidJumpsRuntime v]; jump_dest) h2
    have h4 := metaMorphoV1_1_block_17570 (immWords := wordsOf (immStore v))
      (by simp only [List.length_cons]; omega)
      (by rw [metaMorphoV1_1PatchedValidJumpsRuntime v]; jump_dest) h3
    have h5 := metaMorphoV1_1_block_17538 (immWords := wordsOf (immStore v))
      (by simp only [List.length_cons]; omega)
      (by rw [metaMorphoV1_1PatchedValidJumpsRuntime v]; jump_dest) h4
    refine .inl ⟨fun hgood ↦ hl hgood.1, ?_⟩
    by_cases hf : allocationFits ptr (UInt256.ofNat out.size)
    · obtain ⟨aw6, k6, C6, h6⟩ := allocateRoundedReturn v
        (by simp only [List.length_cons]; omega) hf
        (by rw [metaMorphoV1_1PatchedValidJumps v]; jump_dest) h5
      have h7 := metaMorphoV1_1_block_17551_taken
        (immWords := wordsOf (immStore v)) (by simp only [List.length_cons]; omega)
        (by rw [word_add_sub_left, slt_ofNat_lit_one_low (by decide) (by omega)]; decide)
        (by rw [metaMorphoV1_1PatchedValidJumpsRuntime v]; jump_dest) h6
      exact metaMorphoV1_1_block_917 (immWords := wordsOf (immStore v))
        (by simp only [metaMorphoV1_1_block_17551_taken_stack, List.length_cons]; omega) h7
    · exact allocateRoundedRevert v (by simp only [List.length_cons]; omega) hf h5

set_option maxRecDepth 2000 in
theorem borrowRateReadWord {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem out : ByteArray} {aw : UInt256} {σ : AccountMap}
    {k C : Nat} {ptr elapsed feePtr rate : UInt256} {R : List UInt256}
    (v : MetaMorphoV1_1Immutables) (hstack : R.length + 5 ≤ 1024)
    (hload : memLoad ptr mem = rate)
    (rd : RD (deployedRuntime v) I g s0 ⟨17560⟩ (elapsed :: feePtr :: ptr :: R)
      mem aw out σ k C) :
    ∃ aw' k' C', RD (deployedRuntime v) I g s0 ⟨17239⟩
      (⟨17338⟩ :: elapsed :: feePtr :: rate :: R) mem aw' out σ k' C' := by
  obtain ⟨aw', k', C', h⟩ := metaMorphoV1_1_block_17560_packed
    (immWords := wordsOf (immStore v)) hstack
    (by rw [metaMorphoV1_1PatchedValidJumpsRuntime v]; jump_dest) rd
  exact ⟨aw', k', C', by simpa only [metaMorphoV1_1_block_17560_stack, hload] using h⟩

end Benchmarks.Morpho.MetaMorphoV1_1.SourceMemory
