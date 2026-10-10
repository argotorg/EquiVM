import Benchmarks.Morpho.MetaMorphoV1_1.MarketParamsABI
import Benchmarks.Morpho.MetaMorphoV1_1.RuntimeBlocks_074
import Benchmarks.Morpho.MetaMorphoV1_1.RuntimeBlocks_009
import Benchmarks.Morpho.MetaMorphoV1_1.RuntimeBlocks_018

/-! Both fixed-size reservations and the length guard after the market-parameter call. -/

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables
open Benchmarks.Morpho.MetaMorphoV1_1.Immutables metaMorphoV1_1Blocks

namespace Benchmarks.Morpho.MetaMorphoV1_1.SourceMemory

attribute [local irreducible] metaMorphoV1_1Bytecode
set_option autoImplicit false

def marketParamsReservedMem (mem : ByteArray) (ptr : UInt256) : ByteArray :=
  writeWord (writeWord mem 64 (nextCursor ptr ⟨160⟩)) 64
    (nextCursor (nextCursor ptr ⟨160⟩) ⟨160⟩)

set_option maxRecDepth 2000 in
theorem marketParamsCallFailure {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem out : ByteArray} {aw : UInt256} {σ : AccountMap}
    {k C : Nat} {ptr : UInt256} {R : List UInt256}
    (v : MetaMorphoV1_1Immutables) (hstack : R.length + 7 ≤ 1024)
    (hout : out.size < UInt256.size)
    (rd : RD (deployedRuntime v) I g s0 ⟨16222⟩ (⟨0⟩ :: ptr :: R)
      mem aw out σ k C) : RDrev (deployedRuntime v) g s0 := by
  have hfail := metaMorphoV1_1_block_16222_taken
    (immWords := wordsOf (immStore v)) (by omega) (by decide)
    (by rw [metaMorphoV1_1PatchedValidJumpsRuntime v]; jump_dest) rd
  exact metaMorphoV1_1_block_2921 (immWords := wordsOf (immStore v))
    (by simp only [metaMorphoV1_1_block_16222_taken_stack, List.length_cons]; omega)
    (by change 0 + (UInt256.ofNat out.size).toNat ≤ out.size
        rw [UInt256.toNat_ofNat_of_lt hout, Nat.zero_add]) hfail

set_option maxRecDepth 2000 in
theorem marketParamsReturnAllocation {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem out : ByteArray} {aw : UInt256} {σ : AccountMap}
    {k C : Nat} {ptr : UInt256} {R : List UInt256}
    (v : MetaMorphoV1_1Immutables) (hstack : R.length + 11 ≤ 1024)
    (hout : out.size < UInt256.size)
    (rd : RD (deployedRuntime v) I g s0 ⟨16222⟩ (⟨1⟩ :: ptr :: R)
      mem aw out σ k C) :
    (¬ (160 ≤ out.size ∧ allocationFits ptr ⟨320⟩) ∧
      RDrev (deployedRuntime v) g s0) ∨
    (160 ≤ out.size ∧ allocationFits ptr ⟨320⟩ ∧ ∃ aw' k' C',
      RD (deployedRuntime v) I g s0 ⟨16288⟩
        (ptr :: ⟨128⟩ :: nextCursor ptr ⟨160⟩ :: R)
        (marketParamsReservedMem mem ptr) aw' out σ k' C') := by
  have h1 := metaMorphoV1_1_block_16222_fallthrough
    (immWords := wordsOf (immStore v)) (by omega) (by decide) rd
  have h2 := metaMorphoV1_1_block_16229_taken
    (immWords := wordsOf (immStore v)) (by omega) (by decide)
    (by rw [metaMorphoV1_1PatchedValidJumpsRuntime v]; jump_dest) h1
  by_cases hlong : 160 ≤ out.size
  · have h3 := metaMorphoV1_1_block_16238_fallthrough
      (immWords := wordsOf (immStore v)) (by omega)
      (ugt_zero (by simpa only [UInt256.toNat_ofNat_of_lt hout] using hlong)) h2
    have h4 := metaMorphoV1_1_block_16252 (immWords := wordsOf (immStore v))
      (by simp only [List.length_cons]; omega)
      (by rw [metaMorphoV1_1PatchedValidJumpsRuntime v]; jump_dest) h3
    by_cases hfirst : allocationFits ptr ⟨160⟩
    · obtain ⟨aw5, k5, C5, h5⟩ := allocateRoundedReturn v
        (by simp only [List.length_cons]; omega) hfirst
        (by rw [metaMorphoV1_1PatchedValidJumps v]; jump_dest) h4
      have h6 := metaMorphoV1_1_block_16265_fallthrough
        (immWords := wordsOf (immStore v)) (by simp only [List.length_cons]; omega)
        (by rw [word_add_sub_left]; decide +kernel) h5
      have h7 := metaMorphoV1_1_block_16274 (immWords := wordsOf (immStore v))
        (by omega)
        (by rw [metaMorphoV1_1PatchedValidJumpsRuntime v]; jump_dest) h6
      have hfree : memLoad (UInt256.ofNat 64) (writeWord mem 64 (nextCursor ptr ⟨160⟩)) =
          nextCursor ptr ⟨160⟩ := loadedWord_of_read
        (by change 64 + 32 ≤ _; rw [writeWord_sparse_size]; omega)
        (writeWord_sparse_read_back _ _ _)
      simp only [metaMorphoV1_1_block_16274_stack, hfree] at h7
      by_cases hsecond : allocationFits (nextCursor ptr ⟨160⟩) ⟨160⟩
      · obtain ⟨aw8, k8, C8, h8⟩ := allocateStruct160Return v
          (by simp only [List.length_cons]; omega) hsecond
          (by rw [metaMorphoV1_1PatchedValidJumps v]; jump_dest) h7
        exact .inr ⟨hlong, (allocationFits_160_twice ptr).mpr ⟨hfirst, hsecond⟩,
          aw8, k8, C8, h8⟩
      · exact .inl ⟨fun hc ↦ hsecond ((allocationFits_160_twice ptr).mp hc.2).2,
          allocateStruct160Revert v (by simp only [List.length_cons]; omega) hsecond h7⟩
    · exact .inl ⟨fun hc ↦ hfirst ((allocationFits_160_twice ptr).mp hc.2).1,
        allocateRoundedRevert v (by simp only [List.length_cons]; omega) hfirst h4⟩
  · have h3 := metaMorphoV1_1_block_16238_taken
      (immWords := wordsOf (immStore v)) (by omega)
      (by rw [ugt_one (by simpa only [UInt256.toNat_ofNat_of_lt hout] using
            Nat.lt_of_not_ge hlong)]; decide)
      (by rw [metaMorphoV1_1PatchedValidJumpsRuntime v]; jump_dest) h2
    have h4 := metaMorphoV1_1_block_16360 (immWords := wordsOf (immStore v))
      (by simp only [List.length_cons]; omega)
      (by rw [metaMorphoV1_1PatchedValidJumpsRuntime v]; jump_dest) h3
    have h5 := metaMorphoV1_1_block_16252 (immWords := wordsOf (immStore v))
      (by simp only [List.length_cons]; omega)
      (by rw [metaMorphoV1_1PatchedValidJumpsRuntime v]; jump_dest) h4
    refine .inl ⟨fun hc ↦ hlong hc.1, ?_⟩
    by_cases hfirst : allocationFits ptr (UInt256.ofNat out.size)
    · obtain ⟨aw6, k6, C6, h6⟩ := allocateRoundedReturn v
        (by simp only [List.length_cons]; omega) hfirst
        (by rw [metaMorphoV1_1PatchedValidJumps v]; jump_dest) h5
      have h7 := metaMorphoV1_1_block_16265_taken
        (immWords := wordsOf (immStore v)) (by simp only [List.length_cons]; omega)
        (by rw [word_add_sub_left, slt_ofNat_lit_one_low (by decide) (by omega)]; decide)
        (by rw [metaMorphoV1_1PatchedValidJumpsRuntime v]; jump_dest) h6
      exact metaMorphoV1_1_block_917 (immWords := wordsOf (immStore v))
        (by simp only [metaMorphoV1_1_block_16265_taken_stack, List.length_cons]; omega) h7
    · exact allocateRoundedRevert v (by simp only [List.length_cons]; omega) hfirst h5

end Benchmarks.Morpho.MetaMorphoV1_1.SourceMemory
