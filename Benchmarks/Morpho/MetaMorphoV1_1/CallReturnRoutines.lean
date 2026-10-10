import Benchmarks.Morpho.MetaMorphoV1_1.CallReturnAllocation
import Benchmarks.Morpho.MetaMorphoV1_1.AllocationRoutines
import Benchmarks.Morpho.MetaMorphoV1_1.RuntimeBlocks_057
import Benchmarks.Morpho.MetaMorphoV1_1.RuntimeBlocks_058
import Benchmarks.Morpho.MetaMorphoV1_1.RuntimeBlocks_071

/-! Copy the raw call's return bytes, or take either allocator panic branch. -/

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach Reasoning.Immutables
open Benchmarks.Morpho.MetaMorphoV1_1.Immutables metaMorphoV1_1Blocks

namespace Benchmarks.Morpho.MetaMorphoV1_1.SourceMemory

attribute [local irreducible] metaMorphoV1_1Bytecode
set_option autoImplicit false
set_option maxRecDepth 2000

theorem callReturnBuffer {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem out : ByteArray} {aw : UInt256} {σ : AccountMap} {k C : Nat}
    {ptr ret : UInt256} {R : List UInt256} (v : MetaMorphoV1_1Immutables)
    (hstack : R.length + 9 ≤ 1024) (hptr : ptr.toNat < 2 ^ 64)
    (hout : out.size < UInt256.size) (hfree : memLoad ⟨64⟩ mem = ptr)
    (hret : (D_J (deployedRuntime v) 0).contains ret = true)
    (rd : RD (deployedRuntime v) I g s0 ⟨15478⟩ (ret :: R) mem aw out σ k C) :
    (¬ callReturnFits ptr out ∧ RDrev (deployedRuntime v) g s0) ∨
      (callReturnFits ptr out ∧ ∃ aw' k' C',
        RD (deployedRuntime v) I g s0 ret (callReturnPointer ptr out :: R)
          (callReturnMemory mem ptr out) aw' out σ k' C') := by
  change memLoad (UInt256.ofNat 64) mem = ptr at hfree
  have ho : (UInt256.ofNat out.size).toNat = out.size := UInt256.toNat_ofNat_of_lt hout
  by_cases hz : out.size = 0
  · have h1 := metaMorphoV1_1_block_15478_taken (immWords := wordsOf (immStore v))
      (by simp only [List.length_cons]; omega) (by rw [hz]; decide)
      (by rw [metaMorphoV1_1PatchedValidJumpsRuntime v]; jump_dest) rd
    obtain ⟨aw2, k2, C2, h2⟩ := metaMorphoV1_1_block_15520_packed
      (immWords := wordsOf (immStore v)) (by omega) hret h1
    exact .inr ⟨.inl hz, aw2, k2, C2, by
      simpa only [callReturnPointer, callReturnMemory, hz, if_pos rfl,
        metaMorphoV1_1_block_15520_stack] using h2⟩
  · have hn : UInt256.ofNat out.size ≠ ⟨0⟩ := by
      intro he
      have hh := congrArg UInt256.toNat he
      rw [ho] at hh
      exact hz hh
    have h1 := metaMorphoV1_1_block_15478_fallthrough (immWords := wordsOf (immStore v))
      (by simp only [List.length_cons]; omega) (isZero_eq_zero_of_ne hn) rd
    have h2 := metaMorphoV1_1_block_15485 (immWords := wordsOf (immStore v))
      (by omega) (by rw [metaMorphoV1_1PatchedValidJumpsRuntime v]; jump_dest) h1
    by_cases hsmall : out.size < 2 ^ 64
    · have h3 := metaMorphoV1_1_block_11617_fallthrough (immWords := wordsOf (immStore v))
        (by simp only [List.length_cons]; omega)
        (ugt_zero (by rw [ho]; change out.size ≤ 2 ^ 64 - 1; omega)) h2
      have h4 := metaMorphoV1_1_block_11632 (immWords := wordsOf (immStore v))
        (by simp only [List.length_cons]; omega)
        (by rw [metaMorphoV1_1PatchedValidJumpsRuntime v]; jump_dest) h3
      simp only [metaMorphoV1_1_block_11632_stack,
        callReturnSizeWord out.size hsmall] at h4
      have h5 := metaMorphoV1_1_block_15495 (immWords := wordsOf (immStore v))
        (by omega)
        (by rw [metaMorphoV1_1PatchedValidJumpsRuntime v]; jump_dest) h4
      simp only [metaMorphoV1_1_block_15495_stack, hfree] at h5
      by_cases hf : allocationFits ptr (UInt256.ofNat (32 + out.size))
      · obtain ⟨aw6, k6, C6, h6⟩ := allocateRoundedReturn v
          (by simp only [List.length_cons]; omega)
          ((allocationFits_bytesAlloc ptr out.size hsmall).mpr hf)
          (by rw [metaMorphoV1_1PatchedValidJumps v]; jump_dest) h5
        rw [nextCursor_bytesAllocSize ptr out.size hsmall] at h6
        obtain ⟨aw7, k7, C7, h7⟩ := metaMorphoV1_1_block_15509_packed
          (immWords := wordsOf (immStore v)) (by omega)
          (by change 0 + (UInt256.ofNat out.size).toNat ≤ out.size; omega) hret h6
        have hp : (ptr + UInt256.ofNat 32).toNat = ptr.toNat + 32 :=
          uadd_word_ofNat_toNat ptr 32 (by change _ < 2 ^ 256; omega)
        exact .inr ⟨.inr ⟨hsmall, hf⟩, aw7, k7, C7, by
          simpa only [callReturnPointer, callReturnMemory, if_neg hz,
            metaMorphoV1_1_block_15509_stack, metaMorphoV1_1_block_15509_memory,
            hp, ho, show (⟨0⟩ : UInt256).toNat = 0 from rfl, bytesAllocMem,
            Reasoning.Theory.writeWord] using h7⟩
      · exact .inl ⟨fun h ↦ hf ((h.resolve_left hz).2),
          allocateRoundedRevert v (by simp only [List.length_cons]; omega)
            (fun h ↦ hf ((allocationFits_bytesAlloc ptr out.size hsmall).mp h)) h5⟩
    · have h3 := metaMorphoV1_1_block_11617_taken (immWords := wordsOf (immStore v))
        (by simp only [List.length_cons]; omega)
        (by rw [ugt_one (by rw [ho]; change 2 ^ 64 - 1 < out.size; omega)]; decide)
        (by rw [metaMorphoV1_1PatchedValidJumpsRuntime v]; jump_dest) h2
      exact .inl ⟨fun h ↦ hsmall ((h.resolve_left hz).1),
        metaMorphoV1_1_block_2690 (immWords := wordsOf (immStore v))
          (by simp only [List.length_cons]; omega) h3⟩

end Benchmarks.Morpho.MetaMorphoV1_1.SourceMemory
