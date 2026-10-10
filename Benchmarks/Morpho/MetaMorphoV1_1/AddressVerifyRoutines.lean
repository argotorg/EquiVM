import Benchmarks.Morpho.MetaMorphoV1_1.Common
import Benchmarks.Morpho.MetaMorphoV1_1.RuntimeBlocks_083
import Benchmarks.Morpho.MetaMorphoV1_1.RuntimeBlocks_084

/-! Runtime checks shared by raw calls through the Address library. -/

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach Reasoning.Immutables
open Benchmarks.Morpho.MetaMorphoV1_1.Immutables metaMorphoV1_1Blocks

namespace Benchmarks.Morpho.MetaMorphoV1_1.SourceMemory

attribute [local irreducible] metaMorphoV1_1Bytecode
set_option autoImplicit false
set_option maxRecDepth 2000

theorem addressVerifyReturn {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem out : ByteArray} {aw : UInt256} {σ : AccountMap} {k C : Nat}
    {target ptr ret : UInt256} {R : List UInt256} (v : MetaMorphoV1_1Immutables)
    (hstack : R.length + 7 ≤ 1024)
    (hvalid : memLoad ptr mem ≠ ⟨0⟩ ∨ extCodeSizeWord σ target ≠ ⟨0⟩)
    (hret : (D_J (deployedRuntime v) 0).contains ret = true)
    (rd : RD (deployedRuntime v) I g s0 ⟨18567⟩
      (target :: ⟨1⟩ :: ptr :: ret :: R) mem aw out σ k C) :
    ∃ aw' k' C', RD (deployedRuntime v) I g s0 ret (ptr :: R) mem aw' out σ k' C' := by
  have h1 := metaMorphoV1_1_block_18567_taken (immWords := wordsOf (immStore v))
    (by simp only [List.length_cons]; omega) (by decide)
    (by rw [metaMorphoV1_1PatchedValidJumpsRuntime v]; jump_dest) rd
  have hfinish {aw k C} (rd : RD (deployedRuntime v) I g s0 ⟨18612⟩
      (⟨0⟩ :: target :: ptr :: ret :: R) mem aw out σ k C) :
      ∃ aw' k' C', RD (deployedRuntime v) I g s0 ret (ptr :: R) mem aw' out σ k' C' := by
    have h2 := metaMorphoV1_1_block_18612_fallthrough (immWords := wordsOf (immStore v))
      (by simp only [List.length_cons]; omega) rfl rd
    exact metaMorphoV1_1_block_18617_packed (immWords := wordsOf (immStore v))
      (by omega) hret h2
  by_cases hz : memLoad ptr mem = ⟨0⟩
  · have hc := hvalid.resolve_left (not_not_intro hz)
    have h2 := metaMorphoV1_1_block_18603_taken (immWords := wordsOf (immStore v))
      (by simp only [List.length_cons]; omega)
      (by rw [hz]; decide) (by rw [metaMorphoV1_1PatchedValidJumpsRuntime v]; jump_dest) h1
    obtain ⟨_, _, h3⟩ := metaMorphoV1_1_block_18652 (immWords := wordsOf (immStore v))
      (by simp only [List.length_cons]; omega)
      (by rw [metaMorphoV1_1PatchedValidJumpsRuntime v]; jump_dest) h2
    apply hfinish
    simpa only [metaMorphoV1_1_block_18652_stack, isZero_eq_zero_of_ne hc] using h3
  · have h2 := metaMorphoV1_1_block_18603_fallthrough (immWords := wordsOf (immStore v))
      (by simp only [List.length_cons]; omega) (isZero_eq_zero_of_ne hz) h1
    apply hfinish
    simpa only [metaMorphoV1_1_block_18603_fallthrough_stack, isZero_eq_zero_of_ne hz] using h2

theorem addressVerifyRevertCall {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem out : ByteArray} {aw : UInt256} {σ : AccountMap} {k C : Nat}
    {target ptr ret : UInt256} {R : List UInt256} (v : MetaMorphoV1_1Immutables)
    (hstack : R.length + 7 ≤ 1024)
    (rd : RD (deployedRuntime v) I g s0 ⟨18567⟩
      (target :: ⟨0⟩ :: ptr :: ret :: R) mem aw out σ k C) :
    RDrev (deployedRuntime v) g s0 := by
  have h1 := metaMorphoV1_1_block_18567_fallthrough (immWords := wordsOf (immStore v))
    (by simp only [List.length_cons]; omega) rfl rd
  by_cases hz : memLoad ptr mem = ⟨0⟩
  · have h2 := metaMorphoV1_1_block_18573_taken (immWords := wordsOf (immStore v))
      (by simp only [List.length_cons]; omega) (by rw [hz]; decide)
      (by rw [metaMorphoV1_1PatchedValidJumpsRuntime v]; jump_dest) h1
    exact metaMorphoV1_1_block_18588 (immWords := wordsOf (immStore v))
      (by simp only [metaMorphoV1_1_block_18573_taken_stack, List.length_cons]; omega) h2
  · have h2 := metaMorphoV1_1_block_18573_fallthrough (immWords := wordsOf (immStore v))
      (by simp only [List.length_cons]; omega) (isZero_eq_zero_of_ne hz) h1
    exact metaMorphoV1_1_block_18581 (immWords := wordsOf (immStore v))
      (by simp only [List.length_cons]; omega) h2

theorem addressVerifyRevertCode {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem out : ByteArray} {aw : UInt256} {σ : AccountMap} {k C : Nat}
    {target ptr ret : UInt256} {R : List UInt256} (v : MetaMorphoV1_1Immutables)
    (hstack : R.length + 8 ≤ 1024)
    (hlen : memLoad ptr mem = ⟨0⟩) (hcode : extCodeSizeWord σ target = ⟨0⟩)
    (rd : RD (deployedRuntime v) I g s0 ⟨18567⟩
      (target :: ⟨1⟩ :: ptr :: ret :: R) mem aw out σ k C) :
    RDrev (deployedRuntime v) g s0 := by
  have h1 := metaMorphoV1_1_block_18567_taken (immWords := wordsOf (immStore v))
    (by simp only [List.length_cons]; omega) (by decide)
    (by rw [metaMorphoV1_1PatchedValidJumpsRuntime v]; jump_dest) rd
  have h2 := metaMorphoV1_1_block_18603_taken (immWords := wordsOf (immStore v))
    (by simp only [List.length_cons]; omega) (by rw [hlen]; decide)
    (by rw [metaMorphoV1_1PatchedValidJumpsRuntime v]; jump_dest) h1
  obtain ⟨_, _, h3⟩ := metaMorphoV1_1_block_18652 (immWords := wordsOf (immStore v))
    (by simp only [List.length_cons]; omega)
    (by rw [metaMorphoV1_1PatchedValidJumpsRuntime v]; jump_dest) h2
  have h4 := metaMorphoV1_1_block_18612_taken (immWords := wordsOf (immStore v))
    (by simp only [List.length_cons]; omega) (by rw [hcode]; decide)
    (by rw [metaMorphoV1_1PatchedValidJumpsRuntime v]; jump_dest) h3
  exact metaMorphoV1_1_block_18620 (immWords := wordsOf (immStore v))
    (by simp only [metaMorphoV1_1_block_18612_taken_stack, List.length_cons]; omega) h4

end Benchmarks.Morpho.MetaMorphoV1_1.SourceMemory
