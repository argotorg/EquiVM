import Benchmarks.Morpho.MetaMorphoV1_1.FullMulNumerator
import Benchmarks.Morpho.MetaMorphoV1_1.CheckedArithmetic
import Benchmarks.Morpho.MetaMorphoV1_1.RuntimeBlocks_075
import Benchmarks.Morpho.MetaMorphoV1_1.RuntimeBlocks_058

/-! Complete runtime proof of OpenZeppelin's full-precision mulDiv routine. -/

open Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach Reasoning.Immutables
open Benchmarks.Morpho.MetaMorphoV1_1.Immutables metaMorphoV1_1Blocks

namespace Benchmarks.Morpho.MetaMorphoV1_1

attribute [local irreducible] metaMorphoV1_1Bytecode
set_option autoImplicit false
set_option maxRecDepth 2000

theorem fullMulDiv_small {a b d : UInt256} (hp : a.toNat * b.toNat < UInt256.size) :
    UInt256.div (UInt256.mul a b) d = fullMulDivWord a b d := by
  apply u256_inj
  rw [udiv_toNat, u256_mul_toNat, Nat.mod_eq_of_lt hp, fullMulDivWord,
    UInt256.toNat_ofNat_of_lt (lt_of_le_of_lt (Nat.div_le_self _ _) hp)]

theorem fullMulDivWideReturn {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap}
    {k C : Nat} {a b d ret : UInt256} {R : List UInt256}
    (v : MetaMorphoV1_1Immutables) (hstack : R.length + 10 ≤ 1024) (hd : d ≠ ⟨0⟩)
    (hret : (D_J (deployedRuntime v) 0).contains ret = true)
    (rd : RD (deployedRuntime v) I g s0 ⟨16581⟩
      ([b, a, d, UInt256.mul a b, fullProductHigh a b, ret] ++ R) mem aw rdata σ k C) :
    ∃ aw' k' C', RD (deployedRuntime v) I g s0 ret (fullMulDivWord a b d :: R)
      mem aw' rdata σ k' C' := by
  obtain ⟨aw1, k1, C1, h1⟩ := metaMorphoV1_1_block_16581_packed
    (immWords := wordsOf (immStore v))
    (by simp only [List.append, List.length_cons]; omega) rd
  change RD _ _ _ _ _
    ([UInt256.gt (UInt256.mulMod a b d) (UInt256.mul a b), fullProductHigh a b,
      fullDivTwosComplement d, UInt256.mulMod a b d, fullDivTwos d, UInt256.mul a b,
      fullDivInverse (UInt256.div d (fullDivTwos d)) 6, ret] ++ R) _ _ _ _ _ _ at h1
  obtain ⟨aw2, k2, C2, h2⟩ := metaMorphoV1_1_block_16654_packed
    (immWords := wordsOf (immStore v))
    (by simp only [List.append, List.length_cons]; omega) hret h1
  change RD _ _ _ _ _ (fullMulDivCalculated a b d :: R) _ _ _ _ _ _ at h2
  rw [fullMulDivCalculated_correct a b d hd] at h2
  exact ⟨aw2, k2, C2, h2⟩

theorem fullMulDivReturn {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap}
    {k C : Nat} {a b d ret : UInt256} {R : List UInt256}
    (v : MetaMorphoV1_1Immutables) (hstack : R.length + 10 ≤ 1024)
    (hfit : fullMulDivFits a b d)
    (hret : (D_J (deployedRuntime v) 0).contains ret = true)
    (rd : RD (deployedRuntime v) I g s0 ⟨16544⟩ ([a, b, d, ret] ++ R) mem aw rdata σ k C) :
    ∃ aw' k' C', RD (deployedRuntime v) I g s0 ret (fullMulDivWord a b d :: R)
      mem aw' rdata σ k' C' := by
  by_cases hp : a.toNat * b.toNat < UInt256.size
  · obtain ⟨aw1, k1, C1, h1⟩ := metaMorphoV1_1_block_16544_taken_packed
      (immWords := wordsOf (immStore v))
      (by simp only [List.append, List.length_cons]; omega)
      (by change fullProductGuard a b ≠ ⟨0⟩; rw [fullProductGuard_small hp]; decide)
      (by rw [metaMorphoV1_1PatchedValidJumpsRuntime v]; jump_dest) rd
    obtain ⟨aw2, k2, C2, h2⟩ := metaMorphoV1_1_block_16679_packed
      (immWords := wordsOf (immStore v))
      (by simp only [List.append, List.length_cons]; omega)
      (by rw [metaMorphoV1_1PatchedValidJumpsRuntime v]; jump_dest) h1
    obtain ⟨k3, C3, h3⟩ := checkedDivReturn v
      (by simp only [List.append, List.length_cons]; omega) hfit.1
      (by rw [metaMorphoV1_1PatchedValidJumps v]; jump_dest) h2
    obtain ⟨aw4, k4, C4, h4⟩ := metaMorphoV1_1_block_11757_packed
      (immWords := wordsOf (immStore v))
      (by simp only [List.append, List.length_cons]; omega) hret h3
    rw [fullMulDiv_small hp] at h4
    exact ⟨aw4, k4, C4, h4⟩
  · obtain ⟨aw1, k1, C1, h1⟩ := metaMorphoV1_1_block_16544_fallthrough_packed
      (immWords := wordsOf (immStore v))
      (by simp only [List.append, List.length_cons]; omega)
      (fullProductGuard_large (Nat.le_of_not_gt hp)) rd
    obtain ⟨aw2, k2, C2, h2⟩ := metaMorphoV1_1_block_16573_fallthrough_packed
      (immWords := wordsOf (immStore v))
      (by simp only [List.append, List.length_cons]; omega)
      (by
        change UInt256.isZero (UInt256.gt d (fullProductHigh a b)) = ⟨0⟩
        rw [ugt_one ((fullMulDivFits_iff a b d).mp hfit)]; rfl) h1
    exact fullMulDivWideReturn v hstack hfit.1 hret h2

theorem fullMulDivRevert {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap}
    {k C : Nat} {a b d ret : UInt256} {R : List UInt256}
    (v : MetaMorphoV1_1Immutables) (hstack : R.length + 10 ≤ 1024)
    (hbad : ¬ fullMulDivFits a b d)
    (rd : RD (deployedRuntime v) I g s0 ⟨16544⟩ ([a, b, d, ret] ++ R) mem aw rdata σ k C) :
    RDrev (deployedRuntime v) g s0 := by
  by_cases hp : a.toNat * b.toNat < UInt256.size
  · have hd : d = ⟨0⟩ := Classical.not_not.mp
      (fun hn ↦ hbad ⟨hn, lt_of_le_of_lt (Nat.div_le_self _ _) hp⟩)
    subst d
    obtain ⟨aw1, k1, C1, h1⟩ := metaMorphoV1_1_block_16544_taken_packed
      (immWords := wordsOf (immStore v))
      (by simp only [List.append, List.length_cons]; omega)
      (by change fullProductGuard a b ≠ ⟨0⟩; rw [fullProductGuard_small hp]; decide)
      (by rw [metaMorphoV1_1PatchedValidJumpsRuntime v]; jump_dest) rd
    obtain ⟨aw2, k2, C2, h2⟩ := metaMorphoV1_1_block_16679_packed
      (immWords := wordsOf (immStore v))
      (by simp only [List.append, List.length_cons]; omega)
      (by rw [metaMorphoV1_1PatchedValidJumpsRuntime v]; jump_dest) h1
    exact checkedDivRevert v (by simp only [List.append, List.length_cons]; omega) h2
  · obtain ⟨aw1, k1, C1, h1⟩ := metaMorphoV1_1_block_16544_fallthrough_packed
      (immWords := wordsOf (immStore v))
      (by simp only [List.append, List.length_cons]; omega)
      (fullProductGuard_large (Nat.le_of_not_gt hp)) rd
    have hle : d.toNat ≤ (fullProductHigh a b).toNat :=
      Nat.le_of_not_gt (fun h ↦ hbad ((fullMulDivFits_iff a b d).mpr h))
    obtain ⟨aw2, k2, C2, h2⟩ := metaMorphoV1_1_block_16573_taken_packed
      (immWords := wordsOf (immStore v))
      (by simp only [List.append, List.length_cons]; omega)
      (by
        change UInt256.isZero (UInt256.gt d (fullProductHigh a b)) ≠ ⟨0⟩
        rw [ugt_zero hle]; decide)
      (by rw [metaMorphoV1_1PatchedValidJumpsRuntime v]; jump_dest) h1
    exact metaMorphoV1_1_block_16664 (immWords := wordsOf (immStore v))
      (by simp only [List.append, List.length_cons]; omega) h2

end Benchmarks.Morpho.MetaMorphoV1_1
