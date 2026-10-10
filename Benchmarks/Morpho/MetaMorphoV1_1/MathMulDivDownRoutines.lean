import Benchmarks.Morpho.MetaMorphoV1_1.FullMulDivRoutines
import Benchmarks.Morpho.MetaMorphoV1_1.RuntimeBlocks_079
import Benchmarks.Morpho.MetaMorphoV1_1.RuntimeBlocks_087

/-! Runtime execution of the mulDiv wrapper with rounding toward zero. -/

open Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach Reasoning.Immutables
open Benchmarks.Morpho.MetaMorphoV1_1.Immutables metaMorphoV1_1Blocks

namespace Benchmarks.Morpho.MetaMorphoV1_1

attribute [local irreducible] metaMorphoV1_1Bytecode
set_option autoImplicit false
set_option maxRecDepth 2000

theorem mathMulDivDownReturn {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap}
    {k C : Nat} {a b d ret : UInt256} {R : List UInt256}
    (v : MetaMorphoV1_1Immutables) (hstack : R.length + 17 ≤ 1024)
    (hfit : fullMulDivFits a b d)
    (hret : (D_J (deployedRuntime v) 0).contains ret = true)
    (rd : RD (deployedRuntime v) I g s0 ⟨17811⟩
      ([a, b, d, ⟨0⟩, ret] ++ R) mem aw rdata σ k C) :
    ∃ aw' k' C', RD (deployedRuntime v) I g s0 ret (fullMulDivWord a b d :: R)
      mem aw' rdata σ k' C' := by
  obtain ⟨aw1, k1, C1, h1⟩ := metaMorphoV1_1_block_17811_packed
    (immWords := wordsOf (immStore v))
    (by simp only [List.append, List.length_cons]; omega)
    (by rw [metaMorphoV1_1PatchedValidJumpsRuntime v]; jump_dest) rd
  obtain ⟨aw2, k2, C2, h2⟩ := fullMulDivReturn v
    (by simp only [List.append, List.length_cons]; omega) hfit
    (by rw [metaMorphoV1_1PatchedValidJumps v]; jump_dest) h1
  obtain ⟨aw3, k3, C3, h3⟩ := metaMorphoV1_1_block_17827_packed
    (immWords := wordsOf (immStore v))
    (by simp only [List.append, List.length_cons]; omega)
    (by rw [metaMorphoV1_1PatchedValidJumpsRuntime v]; jump_dest) h2
  obtain ⟨aw4, k4, C4, h4⟩ := metaMorphoV1_1_block_19213_fallthrough_packed
    (immWords := wordsOf (immStore v))
    (by simp only [List.append, List.length_cons]; omega) (by decide) h3
  obtain ⟨aw5, k5, C5, h5⟩ := metaMorphoV1_1_block_19222_packed
    (immWords := wordsOf (immStore v))
    (by simp only [List.append, List.length_cons]; omega)
    (by rw [metaMorphoV1_1PatchedValidJumpsRuntime v]; jump_dest) h4
  obtain ⟨aw6, k6, C6, h6⟩ := metaMorphoV1_1_block_17837_fallthrough_packed
    (immWords := wordsOf (immStore v))
    (by simp only [List.append, List.length_cons]; omega) (by decide) h5
  obtain ⟨aw7, k7, C7, h7⟩ := metaMorphoV1_1_block_17846_fallthrough_packed
    (immWords := wordsOf (immStore v))
    (by simp only [List.append, List.length_cons]; omega) (by decide) h6
  exact metaMorphoV1_1_block_17854_packed (immWords := wordsOf (immStore v))
    (by omega) hret h7

theorem mathMulDivDownRevert {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap}
    {k C : Nat} {a b d ret : UInt256} {R : List UInt256}
    (v : MetaMorphoV1_1Immutables) (hstack : R.length + 17 ≤ 1024)
    (hbad : ¬ fullMulDivFits a b d)
    (rd : RD (deployedRuntime v) I g s0 ⟨17811⟩
      ([a, b, d, ⟨0⟩, ret] ++ R) mem aw rdata σ k C) :
    RDrev (deployedRuntime v) g s0 := by
  obtain ⟨aw1, k1, C1, h1⟩ := metaMorphoV1_1_block_17811_packed
    (immWords := wordsOf (immStore v))
    (by simp only [List.append, List.length_cons]; omega)
    (by rw [metaMorphoV1_1PatchedValidJumpsRuntime v]; jump_dest) rd
  exact fullMulDivRevert v (by simp only [List.append, List.length_cons]; omega) hbad h1

end Benchmarks.Morpho.MetaMorphoV1_1
