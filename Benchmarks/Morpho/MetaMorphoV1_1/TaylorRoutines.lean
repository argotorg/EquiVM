import Benchmarks.Morpho.MetaMorphoV1_1.TaylorSource
import Benchmarks.Morpho.MetaMorphoV1_1.CheckedArithmetic
import Benchmarks.Morpho.MetaMorphoV1_1.RuntimeBlocks_077

/-! The compiler's three Taylor terms, checked multiplications, and final sum. -/

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables
open Benchmarks.Morpho.MetaMorphoV1_1.Immutables metaMorphoV1_1Blocks

namespace Benchmarks.Morpho.MetaMorphoV1_1

attribute [local irreducible] metaMorphoV1_1Bytecode
set_option autoImplicit false

set_option maxRecDepth 2000 in
theorem taylorTailRoutine {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap}
    {k C : Nat} {first ret : UInt256} {R : List UInt256}
    (v : MetaMorphoV1_1Immutables) (hstack : R.length + 11 ≤ 1024)
    (hret : (D_J (deployedRuntime v) 0).contains ret = true)
    (rd : RD (deployedRuntime v) I g s0 ⟨17278⟩ (first :: ret :: R) mem aw rdata σ k C) :
    (¬ taylorTailFits first ∧ RDrev (deployedRuntime v) g s0) ∨
    (taylorTailFits first ∧ ∃ k' C', RD (deployedRuntime v) I g s0 ret
      (taylorSum first :: R) mem aw rdata σ k' C') := by
  have h0 := metaMorphoV1_1_block_17278 (immWords := wordsOf (immStore v))
    (by simp only [List.length_cons]; omega)
    (by rw [metaMorphoV1_1PatchedValidJumpsRuntime v]; jump_dest) rd
  by_cases hsq : first.toNat * first.toNat < UInt256.size
  · obtain ⟨k1, C1, h1⟩ := checkedMulReturn v
      (by simp only [List.length_cons]; omega) hsq
      (by rw [metaMorphoV1_1PatchedValidJumps v]; jump_dest) h0
    have h2 := metaMorphoV1_1_block_17300 (immWords := wordsOf (immStore v))
      (by simp only [List.length_cons]; omega)
      (by rw [metaMorphoV1_1PatchedValidJumpsRuntime v]; jump_dest) h1
    by_cases hthird : (taylorSecond first).toNat * first.toNat < UInt256.size
    · obtain ⟨k3, C3, h3⟩ := checkedMulReturn v
        (by simp only [List.length_cons]; omega) hthird
        (by rw [metaMorphoV1_1PatchedValidJumps v]; jump_dest) h2
      have h4 := metaMorphoV1_1_block_17320 (immWords := wordsOf (immStore v))
        (by simp only [List.length_cons]; omega)
        (by rw [metaMorphoV1_1PatchedValidJumpsRuntime v]; jump_dest) h3
      obtain ⟨k5, C5, h5⟩ := checkedAddReturn v
        (by simp only [List.length_cons]; omega) (taylorSumsFit first hsq).1
        (by rw [metaMorphoV1_1PatchedValidJumps v]; jump_dest) h4
      have h6 := metaMorphoV1_1_block_17327 (immWords := wordsOf (immStore v))
        (by simp only [List.length_cons]; omega)
        (by rw [metaMorphoV1_1PatchedValidJumpsRuntime v]; jump_dest) h5
      obtain ⟨k7, C7, h7⟩ := checkedAddReturn v
        (by omega) (taylorSumsFit first hsq).2 hret h6
      exact .inr ⟨⟨hsq, hthird⟩, k7, C7, h7⟩
    · exact .inl ⟨fun hfit ↦ hthird hfit.2,
        checkedMulRevert v (by simp only [List.length_cons]; omega) (Nat.le_of_not_lt hthird) h2⟩
  · exact .inl ⟨fun hfit ↦ hsq hfit.1,
      checkedMulRevert v (by simp only [List.length_cons]; omega) (Nat.le_of_not_lt hsq) h0⟩

set_option maxRecDepth 2000 in
theorem taylorRoutine {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap}
    {k C : Nat} {x n ret : UInt256} {R : List UInt256}
    (v : MetaMorphoV1_1Immutables) (hstack : R.length + 11 ≤ 1024)
    (hret : (D_J (deployedRuntime v) 0).contains ret = true)
    (rd : RD (deployedRuntime v) I g s0 ⟨12002⟩ (x :: n :: ⟨17278⟩ :: ret :: R)
      mem aw rdata σ k C) :
    (¬ taylorFits x n ∧ RDrev (deployedRuntime v) g s0) ∨
    (taylorFits x n ∧ ∃ k' C', RD (deployedRuntime v) I g s0 ret
      (taylorSum (UInt256.mul x n) :: R) mem aw rdata σ k' C') := by
  by_cases hp : x.toNat * n.toNat < UInt256.size
  · obtain ⟨k1, C1, h1⟩ := checkedMulReturn v
      (by simp only [List.length_cons]; omega) hp
      (by rw [metaMorphoV1_1PatchedValidJumps v]; jump_dest) rd
    rcases taylorTailRoutine v hstack hret h1 with ⟨hbad, hrev⟩ | ⟨hfit, hdone⟩
    · exact .inl ⟨fun hfit ↦ hbad hfit.2, hrev⟩
    · exact .inr ⟨⟨hp, hfit⟩, hdone⟩
  · exact .inl ⟨fun hfit ↦ hp hfit.1,
      checkedMulRevert v (by simp only [List.length_cons]; omega) (Nat.le_of_not_lt hp) rd⟩

theorem taylorSimulation {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap}
    {k C : Nat} {x n ret : UInt256} {R : List UInt256}
    (v : MetaMorphoV1_1Immutables) (imms : Store) (evm : State)
    (hstack : R.length + 11 ≤ 1024)
    (hret : (D_J (deployedRuntime v) 0).contains ret = true)
    (rd : RD (deployedRuntime v) I g s0 ⟨12002⟩ (x :: n :: ⟨17278⟩ :: ret :: R)
      mem aw rdata σ k C) :
    (ExecFuncBody config (taylorFrame imms x n) evm taylorFunction.body .reverted ∧
      RDrev (deployedRuntime v) g s0) ∨
    (ExecFuncBody config (taylorFrame imms x n) evm taylorFunction.body
      (.returned (taylorThirdFrame imms x n) evm
        [uint256Value (taylorSum (UInt256.mul x n))]) ∧
      ∃ k' C', RD (deployedRuntime v) I g s0 ret (taylorSum (UInt256.mul x n) :: R)
        mem aw rdata σ k' C') := by
  rcases taylorRoutine v hstack hret rd with ⟨hbad, hrev⟩ | ⟨hfit, hdone⟩
  · exact .inl ⟨taylorBodyReverts imms x n evm hbad, hrev⟩
  · exact .inr ⟨taylorBody imms x n evm hfit, hdone⟩

end Benchmarks.Morpho.MetaMorphoV1_1
