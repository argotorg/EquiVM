import Benchmarks.Morpho.MetaMorphoV1_1.StringHeader
import Benchmarks.Morpho.MetaMorphoV1_1.RuntimeBlocks_059

/-! Both outcomes of the compiler's storage-string length decoder at pc 11801. -/

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach Reasoning.Immutables
open Benchmarks.Morpho.MetaMorphoV1_1.Immutables metaMorphoV1_1Blocks

namespace Benchmarks.Morpho.MetaMorphoV1_1

attribute [local irreducible] metaMorphoV1_1Bytecode
set_option maxRecDepth 2000

theorem storageStringReachCheck {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap}
    {k C : Nat} {header ret : UInt256} {R : List UInt256}
    (v : MetaMorphoV1_1Immutables) (hstack : R.length + 5 ≤ 1024)
    (rd : RD (deployedRuntime v) I g s0 ⟨11801⟩ (header :: ret :: R) mem aw rdata σ k C) :
    ∃ aw' k' C', RD (deployedRuntime v) I g s0 ⟨11816⟩
      (UInt256.land header ⟨1⟩ :: ret :: storageStringLength header :: R)
      mem aw' rdata σ k' C' := by
  have hshift : UInt256.shiftRight header (UInt256.ofNat 1) = UInt256.div header ⟨2⟩ :=
    wordShiftRight_eq_div header 1 (by decide)
  by_cases hz : UInt256.land header ⟨1⟩ = ⟨0⟩
  · obtain ⟨aw1, k1, C1, h1⟩ := metaMorphoV1_1_block_11801_taken_packed
      (immWords := wordsOf (immStore v)) hstack (by
        change UInt256.isZero (UInt256.land header ⟨1⟩) ≠ ⟨0⟩
        rw [hz]; decide)
      (by rw [metaMorphoV1_1PatchedValidJumpsRuntime v]; jump_dest) rd
    obtain ⟨aw2, k2, C2, h2⟩ := metaMorphoV1_1_block_11847_packed
      (immWords := wordsOf (immStore v)) (by omega)
      (by rw [metaMorphoV1_1PatchedValidJumpsRuntime v]; jump_dest) h1
    refine ⟨aw2, k2, C2, ?_⟩
    simpa only [metaMorphoV1_1_block_11847_stack, hshift,
      u256_land_comm (UInt256.ofNat 127), storageStringLength, if_pos hz] using h2
  · obtain ⟨aw1, k1, C1, h1⟩ := metaMorphoV1_1_block_11801_fallthrough_packed
      (immWords := wordsOf (immStore v)) hstack (isZero_eq_zero_of_ne hz) rd
    refine ⟨aw1, k1, C1, ?_⟩
    simpa only [metaMorphoV1_1_block_11801_fallthrough_stack, hshift,
      storageStringLength, if_neg hz] using h1

theorem storageStringDecoderReturn {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap}
    {k C : Nat} {header ret : UInt256} {R : List UInt256}
    (v : MetaMorphoV1_1Immutables) (hstack : R.length + 5 ≤ 1024)
    (hvalid : storageStringValid header)
    (hret : (D_J (deployedRuntime v) 0).contains ret = true)
    (rd : RD (deployedRuntime v) I g s0 ⟨11801⟩ (header :: ret :: R) mem aw rdata σ k C) :
    ∃ aw' k' C', RD (deployedRuntime v) I g s0 ret (storageStringLength header :: R)
      mem aw' rdata σ k' C' := by
  obtain ⟨aw1, k1, C1, h1⟩ := storageStringReachCheck v hstack rd
  obtain ⟨aw2, k2, C2, h2⟩ := metaMorphoV1_1_block_11816_fallthrough_packed
    (immWords := wordsOf (immStore v)) hstack (u256_eq_of_ne (Ne.symm hvalid)) h1
  exact metaMorphoV1_1_block_11826_packed (immWords := wordsOf (immStore v))
    (by simp only [List.length_cons]; omega) hret h2

theorem storageStringDecoderRevert {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap}
    {k C : Nat} {header ret : UInt256} {R : List UInt256}
    (v : MetaMorphoV1_1Immutables) (hstack : R.length + 5 ≤ 1024)
    (hbad : ¬ storageStringValid header)
    (rd : RD (deployedRuntime v) I g s0 ⟨11801⟩ (header :: ret :: R) mem aw rdata σ k C) :
    RDrev (deployedRuntime v) g s0 := by
  obtain ⟨aw1, k1, C1, h1⟩ := storageStringReachCheck v hstack rd
  have he : UInt256.lt (storageStringLength header) ⟨32⟩ = UInt256.land header ⟨1⟩ :=
    (Classical.not_not.mp hbad).symm
  obtain ⟨aw2, k2, C2, h2⟩ := metaMorphoV1_1_block_11816_taken_packed
    (immWords := wordsOf (immStore v)) hstack (by
      change UInt256.eq (UInt256.lt (storageStringLength header) ⟨32⟩)
        (UInt256.land header ⟨1⟩) ≠ ⟨0⟩
      rw [he, u256_eq_refl]; decide)
    (by rw [metaMorphoV1_1PatchedValidJumpsRuntime v]; jump_dest) h1
  exact metaMorphoV1_1_block_11827 (immWords := wordsOf (immStore v))
    (by simp only [metaMorphoV1_1_block_11816_taken_stack, List.length_cons]; omega) h2

end Benchmarks.Morpho.MetaMorphoV1_1
