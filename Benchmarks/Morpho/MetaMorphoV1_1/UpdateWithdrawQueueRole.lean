import Benchmarks.Morpho.MetaMorphoV1_1.AllocatorRoleSource
import Benchmarks.Morpho.MetaMorphoV1_1.RevocationRole
import Benchmarks.Morpho.MetaMorphoV1_1.RuntimeBlocks_034
import Benchmarks.Morpho.MetaMorphoV1_1.RuntimeBlocks_041
import Benchmarks.Morpho.MetaMorphoV1_1.RuntimeBlocks_040
import Benchmarks.Morpho.MetaMorphoV1_1.RuntimeBlocks_044

/-! Runtime authorization for withdrawal-queue replacement. -/

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables
open Benchmarks.Morpho.MetaMorphoV1_1.Immutables metaMorphoV1_1Blocks

namespace Benchmarks.Morpho.MetaMorphoV1_1

attribute [local irreducible] metaMorphoV1_1Bytecode
set_option maxRecDepth 2000

theorem updateWithdrawQueueAllocatorChoice {evm : State} {g : Sat256} {s0 : State}
    {mem out : ByteArray} {aw : UInt256} {k C : Nat} {len data : UInt256} {R : List UInt256}
    (v : MetaMorphoV1_1Immutables) (hstack : R.length + 5 ≤ 1024)
    (rd : RD (deployedRuntime v) evm.executionEnv g s0 ⟨8032⟩ (len :: data :: R)
      mem aw out evm.accountMap k C) :
    ∃ aw' k' C', RD (deployedRuntime v) evm.executionEnv g s0
      (if allocatorByte evm evm.executionEnv.source = ⟨0⟩ then ⟨8807⟩ else ⟨8056⟩)
      (UInt256.isZero (allocatorByte evm evm.executionEnv.source) :: data :: len :: R)
      (twoWordHashMem (UInt256.ofNat evm.executionEnv.source.val) ⟨11⟩ mem)
      aw' out evm.accountMap k' C' := by
  have hh : keccakWord ⟨0⟩ (UInt256.ofNat 64)
      ((UInt256.ofNat 11).toByteArray.write 0
        ((UInt256.ofNat evm.executionEnv.source.val).toByteArray.write 0 mem
          (⟨0⟩ : UInt256).toNat 32) (UInt256.ofNat 32).toNat 32) =
        allocatorSlot evm.executionEnv.source := twoWordHashMem_solcMappingSlot_any _ _ _
  by_cases ha : allocatorByte evm evm.executionEnv.source = ⟨0⟩
  · rw [if_pos ha]
    obtain ⟨aw1, k1, C1, h⟩ := metaMorphoV1_1_block_8032_taken_packed
      (immWords := wordsOf (immStore v)) hstack (by
        rw [hh]
        change UInt256.isZero (allocatorByte evm evm.executionEnv.source) ≠ ⟨0⟩
        rw [ha]; decide)
      (by rw [metaMorphoV1_1PatchedValidJumpsRuntime v]; jump_dest) rd
    simp only [metaMorphoV1_1_block_8032_taken_stack, hh] at h
    exact ⟨aw1, k1, C1, h⟩
  · rw [if_neg ha]
    obtain ⟨aw1, k1, C1, h⟩ := metaMorphoV1_1_block_8032_fallthrough_packed
      (immWords := wordsOf (immStore v)) hstack (by
        rw [hh]
        exact isZero_eq_zero_of_ne ha) rd
    simp only [metaMorphoV1_1_block_8032_fallthrough_stack, hh] at h
    exact ⟨aw1, k1, C1, h⟩

theorem updateWithdrawQueueCuratorLookup {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem out : ByteArray} {aw : UInt256} {σ : AccountMap} {k C : Nat}
    {x : UInt256} {R : List UInt256}
    (v : MetaMorphoV1_1Immutables) (hstack : R.length + 4 ≤ 1024)
    (rd : RD (deployedRuntime v) I g s0 ⟨8807⟩ (x :: R) mem aw out σ k C) :
    ∃ k' C', RD (deployedRuntime v) I g s0 ⟨8056⟩
      (storedRoleMismatch I σ ⟨10⟩ :: R) mem aw out σ k' C' :=
  metaMorphoV1_1_block_8807 (immWords := wordsOf (immStore v)) hstack
    (by rw [metaMorphoV1_1PatchedValidJumpsRuntime v]; jump_dest) rd

theorem updateWithdrawQueueOwnerLookup {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem out : ByteArray} {aw : UInt256} {σ : AccountMap} {k C : Nat}
    {x : UInt256} {R : List UInt256}
    (v : MetaMorphoV1_1Immutables) (hstack : R.length + 4 ≤ 1024)
    (hx : x ≠ ⟨0⟩)
    (rd : RD (deployedRuntime v) I g s0 ⟨8056⟩ (x :: R) mem aw out σ k C) :
    ∃ k' C', RD (deployedRuntime v) I g s0 ⟨8062⟩
      (storedRoleMismatch I σ ⟨8⟩ :: R) mem aw out σ k' C' := by
  have r1 := metaMorphoV1_1_block_8056_taken (immWords := wordsOf (immStore v))
    (by omega) hx (by rw [metaMorphoV1_1PatchedValidJumpsRuntime v]; jump_dest) rd
  exact metaMorphoV1_1_block_8786 (immWords := wordsOf (immStore v)) hstack
    (by rw [metaMorphoV1_1PatchedValidJumpsRuntime v]; jump_dest) r1

theorem updateWithdrawQueueRole {evm : State} {g : Sat256} {s0 : State}
    {mem out : ByteArray} {aw : UInt256} {k C : Nat} {len data : UInt256} {R : List UInt256}
    (v : MetaMorphoV1_1Immutables) (hstack : R.length + 6 ≤ 1024)
    (rd : RD (deployedRuntime v) evm.executionEnv g s0 ⟨8032⟩ (len :: data :: R)
      mem aw out evm.accountMap k C) :
    (¬ allocatorRoleAllowed evm ∧ RDrev (deployedRuntime v) g s0) ∨
    (allocatorRoleAllowed evm ∧ ∃ aw' k' C',
      RD (deployedRuntime v) evm.executionEnv g s0 ⟨8067⟩ (data :: len :: R)
        (twoWordHashMem (UInt256.ofNat evm.executionEnv.source.val) ⟨11⟩ mem)
        aw' out evm.accountMap k' C') := by
  obtain ⟨aw1, k1, C1, r1⟩ := updateWithdrawQueueAllocatorChoice v (by omega) rd
  have hpass {k' C' : Nat} (hrole : allocatorRoleAllowed evm)
      (h : RD (deployedRuntime v) evm.executionEnv g s0 ⟨8056⟩ (⟨0⟩ :: data :: len :: R)
        (twoWordHashMem (UInt256.ofNat evm.executionEnv.source.val) ⟨11⟩ mem)
        aw1 out evm.accountMap k' C') :
      allocatorRoleAllowed evm ∧ ∃ aw' k' C',
        RD (deployedRuntime v) evm.executionEnv g s0 ⟨8067⟩ (data :: len :: R)
          (twoWordHashMem (UInt256.ofNat evm.executionEnv.source.val) ⟨11⟩ mem)
          aw' out evm.accountMap k' C' := by
    have h1 := metaMorphoV1_1_block_8056_fallthrough (immWords := wordsOf (immStore v))
      (by simp only [List.length_cons]; omega) rfl h
    exact ⟨hrole, _, _, _, metaMorphoV1_1_block_8062_fallthrough
      (immWords := wordsOf (immStore v)) (by simp only [List.length_cons]; omega) rfl h1⟩
  by_cases ha : allocatorByte evm evm.executionEnv.source = ⟨0⟩
  case neg =>
    simp only [ha, if_false, isZero_eq_zero_of_ne ha] at r1
    exact .inr (hpass (Or.inl ha) r1)
  simp only [ha, if_true] at r1
  obtain ⟨k2, C2, r2⟩ := updateWithdrawQueueCuratorLookup v
    (by simp only [List.length_cons]; omega) r1
  by_cases hc : curatorAddress evm = evm.executionEnv.source
  case pos =>
    rw [storedRoleMismatch_match evm.executionEnv evm.accountMap ⟨10⟩ hc] at r2
    exact .inr (hpass (Or.inr (Or.inl hc)) r2)
  obtain ⟨k3, C3, r3⟩ := updateWithdrawQueueOwnerLookup v (by simp only [List.length_cons]; omega)
    (storedRoleMismatch_ne evm.executionEnv evm.accountMap ⟨10⟩ hc) r2
  by_cases ho : ownerAddress evm = evm.executionEnv.source
  · have h := metaMorphoV1_1_block_8062_fallthrough (immWords := wordsOf (immStore v))
      (by simp only [List.length_cons]; omega)
      (storedRoleMismatch_match evm.executionEnv evm.accountMap ⟨8⟩ ho) r3
    exact .inr ⟨Or.inr (Or.inr ho), _, _, _, h⟩
  · have h := metaMorphoV1_1_block_8062_taken (immWords := wordsOf (immStore v))
      (by simp only [List.length_cons]; omega)
      (storedRoleMismatch_ne evm.executionEnv evm.accountMap ⟨8⟩ ho)
      (by rw [metaMorphoV1_1PatchedValidJumpsRuntime v]; jump_dest) r3
    refine .inl ⟨?_, metaMorphoV1_1_block_6812 (immWords := wordsOf (immStore v))
      (by simp only [metaMorphoV1_1_block_8062_taken_stack, List.length_cons]; omega) h⟩
    rintro (ha' | hc' | ho')
    · exact ha' ha
    · exact hc hc'
    · exact ho ho'

end Benchmarks.Morpho.MetaMorphoV1_1
