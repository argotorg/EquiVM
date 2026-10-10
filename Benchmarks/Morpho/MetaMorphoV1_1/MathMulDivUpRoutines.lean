import Benchmarks.Morpho.MetaMorphoV1_1.MathMulDivUp
import Benchmarks.Morpho.MetaMorphoV1_1.FullMulDivRoutines
import Benchmarks.Morpho.MetaMorphoV1_1.RuntimeBlocks_079
import Benchmarks.Morpho.MetaMorphoV1_1.RuntimeBlocks_087

/-! Runtime execution of the upward-rounding mulDiv wrapper. -/

open Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach Reasoning.Immutables
open Benchmarks.Morpho.MetaMorphoV1_1.Immutables metaMorphoV1_1Blocks

namespace Benchmarks.Morpho.MetaMorphoV1_1

attribute [local irreducible] metaMorphoV1_1Bytecode
set_option autoImplicit false
set_option maxRecDepth 2000

theorem mathMulDivUpReachRemainder {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap}
    {k C : Nat} {a b d ret : UInt256} {R : List UInt256}
    (v : MetaMorphoV1_1Immutables) (hstack : R.length + 17 ≤ 1024)
    (hfit : fullMulDivFits a b d)
    (rd : RD (deployedRuntime v) I g s0 ⟨17811⟩
      ([a, b, d, ⟨1⟩, ret] ++ R) mem aw rdata σ k C) :
    ∃ aw' k' C', RD (deployedRuntime v) I g s0 ⟨17846⟩
      ([⟨0⟩, ⟨0⟩, ⟨0⟩, UInt256.isZero (UInt256.isZero (UInt256.mulMod a b d)),
        fullMulDivWord a b d, ret] ++ R) mem aw' rdata σ k' C' := by
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
  obtain ⟨aw6, k6, C6, h6⟩ := metaMorphoV1_1_block_17837_taken_packed
    (immWords := wordsOf (immStore v))
    (by simp only [List.append, List.length_cons]; omega) (by decide)
    (by rw [metaMorphoV1_1PatchedValidJumpsRuntime v]; jump_dest) h5
  obtain ⟨aw7, k7, C7, h7⟩ := metaMorphoV1_1_block_17870_fallthrough_packed
    (immWords := wordsOf (immStore v))
    (by simp only [List.append, List.length_cons]; omega)
    (isZero_eq_zero_of_ne hfit.1) h6
  exact metaMorphoV1_1_block_17881_packed (immWords := wordsOf (immStore v))
    (by simp only [List.append, List.length_cons]; omega)
    (by rw [metaMorphoV1_1PatchedValidJumpsRuntime v]; jump_dest) h7

theorem mathMulDivUpReturn {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap}
    {k C : Nat} {a b d ret : UInt256} {R : List UInt256}
    (v : MetaMorphoV1_1Immutables) (hstack : R.length + 17 ≤ 1024)
    (hfit : mathMulDivUpFits a b d)
    (hret : (D_J (deployedRuntime v) 0).contains ret = true)
    (rd : RD (deployedRuntime v) I g s0 ⟨17811⟩
      ([a, b, d, ⟨1⟩, ret] ++ R) mem aw rdata σ k C) :
    ∃ aw' k' C', RD (deployedRuntime v) I g s0 ret (mathMulDivUpWord a b d :: R)
      mem aw' rdata σ k' C' := by
  obtain ⟨aw1, k1, C1, h1⟩ := mathMulDivUpReachRemainder v hstack hfit.1 rd
  by_cases hr : mulDivRemainder a b d = 0
  · have hz := (mulDivRemainder_zero_iff a b d hfit.1.1).mp hr
    obtain ⟨aw2, k2, C2, h2⟩ := metaMorphoV1_1_block_17846_fallthrough_packed
      (immWords := wordsOf (immStore v))
      (by simp only [List.append, List.length_cons]; omega) (by rw [hz]; decide) h1
    simpa only [mathMulDivUpWord, if_pos hr] using
      metaMorphoV1_1_block_17854_packed (immWords := wordsOf (immStore v))
        (by change R.length + 2 ≤ 1024; omega) hret h2
  · have hz : UInt256.mulMod a b d ≠ ⟨0⟩ :=
      fun hz ↦ hr ((mulDivRemainder_zero_iff a b d hfit.1.1).mpr hz)
    obtain ⟨aw2, k2, C2, h2⟩ := metaMorphoV1_1_block_17846_taken_packed
      (immWords := wordsOf (immStore v))
      (by simp only [List.append, List.length_cons]; omega)
      (by rw [isZero_eq_zero_of_ne hz]; decide)
      (by rw [metaMorphoV1_1PatchedValidJumpsRuntime v]; jump_dest) h1
    obtain ⟨aw3, k3, C3, h3⟩ := metaMorphoV1_1_block_17856_fallthrough_packed
      (immWords := wordsOf (immStore v))
      (by simp only [List.append, List.length_cons]; omega) (by
        change UInt256.gt (fullMulDivWord a b d) (fullMulDivWord a b d + ⟨1⟩) = ⟨0⟩
        rw [u256_add_comm (fullMulDivWord a b d) ⟨1⟩]
        exact checkedAddNoOverflowGt _ ⟨1⟩ (hfit.2 hr)) h2
    simpa only [mathMulDivUpWord, if_neg hr] using
      metaMorphoV1_1_block_17868_packed (immWords := wordsOf (immStore v))
        (by change R.length + 2 ≤ 1024; omega) hret h3

theorem mathMulDivUpRevert {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap}
    {k C : Nat} {a b d ret : UInt256} {R : List UInt256}
    (v : MetaMorphoV1_1Immutables) (hstack : R.length + 17 ≤ 1024)
    (hbad : ¬ mathMulDivUpFits a b d)
    (rd : RD (deployedRuntime v) I g s0 ⟨17811⟩
      ([a, b, d, ⟨1⟩, ret] ++ R) mem aw rdata σ k C) :
    RDrev (deployedRuntime v) g s0 := by
  by_cases hf : fullMulDivFits a b d
  · obtain ⟨aw1, k1, C1, h1⟩ := mathMulDivUpReachRemainder v hstack hf rd
    have hr : mulDivRemainder a b d ≠ 0 := by
      intro hz
      exact hbad ⟨hf, fun hn ↦ False.elim (hn hz)⟩
    have hi : UInt256.size ≤ (fullMulDivWord a b d).toNat + 1 :=
      Nat.le_of_not_gt (fun hi ↦ hbad ⟨hf, fun _ ↦ hi⟩)
    have hz : UInt256.mulMod a b d ≠ ⟨0⟩ :=
      fun hz ↦ hr ((mulDivRemainder_zero_iff a b d hf.1).mpr hz)
    obtain ⟨aw2, k2, C2, h2⟩ := metaMorphoV1_1_block_17846_taken_packed
      (immWords := wordsOf (immStore v))
      (by simp only [List.append, List.length_cons]; omega)
      (by rw [isZero_eq_zero_of_ne hz]; decide)
      (by rw [metaMorphoV1_1PatchedValidJumpsRuntime v]; jump_dest) h1
    have hg : UInt256.gt (fullMulDivWord a b d) (fullMulDivWord a b d + ⟨1⟩) = ⟨1⟩ := by
      rw [u256_add_comm (fullMulDivWord a b d) ⟨1⟩]
      exact checkedAddOverflowGt _ ⟨1⟩ hi
    obtain ⟨aw3, k3, C3, h3⟩ := metaMorphoV1_1_block_17856_taken_packed
      (immWords := wordsOf (immStore v))
      (by simp only [List.append, List.length_cons]; omega)
      (by change UInt256.gt (fullMulDivWord a b d) (fullMulDivWord a b d + ⟨1⟩) ≠ ⟨0⟩
          rw [hg]; decide)
      (by rw [metaMorphoV1_1PatchedValidJumpsRuntime v]; jump_dest) h2
    exact metaMorphoV1_1_block_9453 (immWords := wordsOf (immStore v))
      (by change R.length + 2 + 2 ≤ 1024; omega) h3
  · obtain ⟨aw1, k1, C1, h1⟩ := metaMorphoV1_1_block_17811_packed
      (immWords := wordsOf (immStore v))
      (by simp only [List.append, List.length_cons]; omega)
      (by rw [metaMorphoV1_1PatchedValidJumpsRuntime v]; jump_dest) rd
    exact fullMulDivRevert v (by simp only [List.append, List.length_cons]; omega) hf h1

end Benchmarks.Morpho.MetaMorphoV1_1
