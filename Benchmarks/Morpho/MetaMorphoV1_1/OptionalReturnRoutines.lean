import Benchmarks.Morpho.MetaMorphoV1_1.OptionalReturnSource
import Benchmarks.Morpho.MetaMorphoV1_1.RuntimeBlocks_085
import Benchmarks.Morpho.MetaMorphoV1_1.RuntimeBlocks_086
import Benchmarks.Morpho.MetaMorphoV1_1.RuntimeBlocks_009

/-! Runtime decoding of SafeERC20's optional Boolean result. -/

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach Reasoning.Immutables
open Benchmarks.Morpho.MetaMorphoV1_1.Immutables metaMorphoV1_1Blocks

namespace Benchmarks.Morpho.MetaMorphoV1_1.SourceMemory

attribute [local irreducible] metaMorphoV1_1Bytecode
set_option autoImplicit false
set_option maxRecDepth 2000

theorem optionalReturnFinish {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem out : ByteArray} {aw : UInt256} {σ : AccountMap} {k C : Nat}
    {x y token ret : UInt256} {R : List UInt256} (v : MetaMorphoV1_1Immutables)
    (hstack : R.length + 5 ≤ 1024)
    (hret : (D_J (deployedRuntime v) 0).contains ret = true)
    (rd : RD (deployedRuntime v) I g s0 ⟨19020⟩
      (x :: y :: ⟨0⟩ :: token :: ret :: R) mem aw out σ k C) :
    ∃ aw' k' C', RD (deployedRuntime v) I g s0 ret R mem aw' out σ k' C' := by
  have h1 := metaMorphoV1_1_block_19020_fallthrough (immWords := wordsOf (immStore v))
    (by simp only [List.length_cons]; omega) rfl rd
  exact metaMorphoV1_1_block_19027_packed (immWords := wordsOf (immStore v)) (by omega) hret h1

theorem optionalReturnReturn {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem out : ByteArray} {aw : UInt256} {σ : AccountMap} {k C : Nat}
    {ptr token ret : UInt256} {R : List UInt256} (v : MetaMorphoV1_1Immutables)
    (hstack : R.length + 8 ≤ 1024) (hout : out.size < 2 ^ 64)
    (hlen : memLoad ptr mem = UInt256.ofNat out.size)
    (hword : 32 ≤ out.size → memLoad (ptr + ⟨32⟩) mem = calldataWord out 0)
    (hvalid : optionalReturnValid out)
    (hret : (D_J (deployedRuntime v) 0).contains ret = true)
    (rd : RD (deployedRuntime v) I g s0 ⟨19007⟩ (ptr :: token :: ret :: R)
      mem aw out σ k C) :
    ∃ aw' k' C', RD (deployedRuntime v) I g s0 ret R mem aw' out σ k' C' := by
  by_cases hz : out.size = 0
  · have h1 := metaMorphoV1_1_block_19007_fallthrough (immWords := wordsOf (immStore v))
      (by simp only [List.length_cons]; omega) (by rw [hlen, hz]; decide) rd
    apply optionalReturnFinish v (by omega) hret
    simpa only [metaMorphoV1_1_block_19007_fallthrough_stack, hlen, hz,
      show UInt256.isZero (UInt256.isZero (UInt256.ofNat 0)) = (⟨0⟩ : UInt256) by decide]
      using h1
  · obtain ⟨hl, hw⟩ := hvalid.resolve_left hz
    have hnon : UInt256.ofNat out.size ≠ ⟨0⟩ := by
      intro he
      have hh := congrArg UInt256.toNat he
      rw [UInt256.toNat_ofNat_of_lt (by change _ < 2 ^ 256; omega)] at hh
      exact hz hh
    have h1 := metaMorphoV1_1_block_19007_taken (immWords := wordsOf (immStore v))
      (by simp only [List.length_cons]; omega)
      (by rw [hlen, isZero_eq_zero_of_ne hnon]; decide)
      (by rw [metaMorphoV1_1PatchedValidJumpsRuntime v]; jump_dest) rd
    have h2 := metaMorphoV1_1_block_19047_fallthrough (immWords := wordsOf (immStore v))
      (by simp only [List.length_cons]; omega)
      (by rw [hlen, word_add_sub_left, slt_ofNat_lit_zero (by decide) hl (by omega)]; rfl) h1
    have hw' : memLoad (UInt256.ofNat 32 + ptr) mem = ⟨1⟩ := by
      rw [u256_add_comm]
      exact (hword hl).trans hw
    have h3 := metaMorphoV1_1_block_19063_fallthrough (immWords := wordsOf (immStore v))
      (by simp only [List.length_cons]; omega) (by rw [hw']; decide) h2
    have h4 := metaMorphoV1_1_block_19077 (immWords := wordsOf (immStore v))
      (by change R.length + 1 + 1 + 1 + 3 ≤ 1024; omega)
      (by rw [metaMorphoV1_1PatchedValidJumpsRuntime v]; jump_dest) h3
    apply optionalReturnFinish v (by omega) hret
    simpa only [metaMorphoV1_1_block_19077_stack, metaMorphoV1_1_block_19063_fallthrough_stack,
      hw', show UInt256.isZero (⟨1⟩ : UInt256) = (⟨0⟩ : UInt256) by decide] using h4

theorem optionalReturnReverts {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem out : ByteArray} {aw : UInt256} {σ : AccountMap} {k C : Nat}
    {ptr token ret : UInt256} {R : List UInt256} (v : MetaMorphoV1_1Immutables)
    (hstack : R.length + 8 ≤ 1024) (hout : out.size < 2 ^ 64)
    (hlen : memLoad ptr mem = UInt256.ofNat out.size)
    (hword : 32 ≤ out.size → memLoad (ptr + ⟨32⟩) mem = calldataWord out 0)
    (hbad : ¬ optionalReturnValid out)
    (rd : RD (deployedRuntime v) I g s0 ⟨19007⟩ (ptr :: token :: ret :: R)
      mem aw out σ k C) : RDrev (deployedRuntime v) g s0 := by
  have hz : out.size ≠ 0 := fun h ↦ hbad (.inl h)
  have hnon : UInt256.ofNat out.size ≠ ⟨0⟩ := by
    intro he
    have hh := congrArg UInt256.toNat he
    rw [UInt256.toNat_ofNat_of_lt (by change _ < 2 ^ 256; omega)] at hh
    exact hz hh
  have h1 := metaMorphoV1_1_block_19007_taken (immWords := wordsOf (immStore v))
    (by simp only [List.length_cons]; omega)
    (by rw [hlen, isZero_eq_zero_of_ne hnon]; decide)
    (by rw [metaMorphoV1_1PatchedValidJumpsRuntime v]; jump_dest) rd
  by_cases hl : 32 ≤ out.size
  · have h2 := metaMorphoV1_1_block_19047_fallthrough (immWords := wordsOf (immStore v))
      (by simp only [List.length_cons]; omega)
      (by rw [hlen, word_add_sub_left, slt_ofNat_lit_zero (by decide) hl (by omega)]; rfl) h1
    have hw' : memLoad (UInt256.ofNat 32 + ptr) mem = calldataWord out 0 := by
      rw [u256_add_comm]
      exact hword hl
    have hne : calldataWord out 0 ≠ ⟨1⟩ := fun h ↦ hbad (.inr ⟨hl, h⟩)
    by_cases hzero : calldataWord out 0 = ⟨0⟩
    · have h3 := metaMorphoV1_1_block_19063_fallthrough (immWords := wordsOf (immStore v))
        (by simp only [List.length_cons]; omega) (by rw [hw', hzero]; decide) h2
      have h4 := metaMorphoV1_1_block_19077 (immWords := wordsOf (immStore v))
        (by change R.length + 1 + 1 + 1 + 3 ≤ 1024; omega)
        (by rw [metaMorphoV1_1PatchedValidJumpsRuntime v]; jump_dest) h3
      have h5 := metaMorphoV1_1_block_19020_taken (immWords := wordsOf (immStore v))
        (by simp only [List.length_cons]; omega) (by rw [hw', hzero]; decide)
        (by rw [metaMorphoV1_1PatchedValidJumpsRuntime v]; jump_dest) h4
      exact metaMorphoV1_1_block_19029 (immWords := wordsOf (immStore v))
        (by simp only [List.length_cons]; omega) h5
    · have h3 := metaMorphoV1_1_block_19063_taken (immWords := wordsOf (immStore v))
        (by simp only [List.length_cons]; omega)
        (by rw [hw', isZero_eq_zero_of_ne hzero]
            exact u256_sub_ne_zero_of_ne (Ne.symm hne))
        (by rw [metaMorphoV1_1PatchedValidJumpsRuntime v]; jump_dest) h2
      exact metaMorphoV1_1_block_917 (immWords := wordsOf (immStore v))
        (by simp only [metaMorphoV1_1_block_19063_taken_stack, List.length_cons]; omega) h3
  · have h2 := metaMorphoV1_1_block_19047_taken (immWords := wordsOf (immStore v))
      (by simp only [List.length_cons]; omega)
      (by rw [hlen, word_add_sub_left, slt_ofNat_lit_one_low (by decide) (by omega)]; decide)
      (by rw [metaMorphoV1_1PatchedValidJumpsRuntime v]; jump_dest) h1
    exact metaMorphoV1_1_block_917 (immWords := wordsOf (immStore v))
      (by simp only [metaMorphoV1_1_block_19047_taken_stack, List.length_cons]; omega) h2

end Benchmarks.Morpho.MetaMorphoV1_1.SourceMemory
