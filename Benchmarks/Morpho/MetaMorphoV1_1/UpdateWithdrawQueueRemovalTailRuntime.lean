import Benchmarks.Morpho.MetaMorphoV1_1.UpdateWithdrawQueueRemovalTailSource
import Benchmarks.Morpho.MetaMorphoV1_1.UpdateWithdrawQueueHeap
import Benchmarks.Morpho.MetaMorphoV1_1.RuntimeBlocks_043

/-! Runtime timelock checks after the supply-share reader returns. -/

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables
open Benchmarks.Morpho.MetaMorphoV1_1.Immutables metaMorphoV1_1Blocks

namespace Benchmarks.Morpho.MetaMorphoV1_1

attribute [local irreducible] metaMorphoV1_1Bytecode
set_option maxRecDepth 2000

theorem updateWithdrawQueueRemovalTailRuntime {evm s0 : State} {g : Sat256}
    {mem out : ByteArray} {aw : UInt256} {k C curr len : Nat}
    {seen : List Bool} {queue : List UInt256} {cursor shares id : UInt256} {R : List UInt256}
    (v : MetaMorphoV1_1Immutables) (hstack : R.length + 3 ≤ 1024)
    (hheap : UpdateWithdrawQueueHeap mem curr len seen queue cursor)
    (rd : RD (deployedRuntime v) evm.executionEnv g s0 ⟨8568⟩
      (shares :: id :: R) mem aw out evm.accountMap k C) :
    (¬ updateWithdrawQueueRemovalAllowed evm id shares ∧ RDrev (deployedRuntime v) g s0) ∨
    (updateWithdrawQueueRemovalAllowed evm id shares ∧ ∃ mem',
      UpdateWithdrawQueueHeap mem' curr len seen queue cursor ∧ ∃ aw' k' C',
        RD (deployedRuntime v) evm.executionEnv g s0 ⟨8573⟩
          (id :: R) mem' aw' out evm.accountMap k' C') := by
  by_cases hz : shares = ⟨0⟩
  · have r1 := metaMorphoV1_1_block_8568_fallthrough (immWords := wordsOf (immStore v))
      (by simp only [List.length_cons]; omega) hz rd
    exact .inr ⟨.inl hz, mem, hheap, _, _, _, r1⟩
  have r1 := metaMorphoV1_1_block_8568_taken (immWords := wordsOf (immStore v))
    (by simp only [List.length_cons]; omega) hz
    (by rw [metaMorphoV1_1PatchedValidJumpsRuntime v]; jump_dest) rd
  have hh (m : ByteArray) :
      keccakWord ⟨0⟩ (UInt256.ofNat 64)
        ((UInt256.ofNat 13).toByteArray.write 0
          (id.toByteArray.write 0 m (⟨0⟩ : UInt256).toNat 32) (UInt256.ofNat 32).toNat 32) =
        solcMappingSlot ⟨13⟩ id := twoWordHashMem_solcMappingSlot_any _ _ _
  by_cases hnz : marketRemovalRemovableAt evm id ≠ ⟨0⟩
  case neg =>
    have heq : marketRemovalRemovableAt evm id = ⟨0⟩ := not_ne_iff.mp hnz
    obtain ⟨aw2, k2, C2, r2⟩ := metaMorphoV1_1_block_8592_taken_packed
      (immWords := wordsOf (immStore v)) hstack
      (by rw [hh]
          change UInt256.isZero (marketRemovalRemovableAt evm id) ≠ ⟨0⟩
          rw [heq]; decide)
      (by rw [metaMorphoV1_1PatchedValidJumpsRuntime v]; jump_dest) r1
    exact .inl ⟨fun h ↦ h.elim hz (fun h ↦ hnz h.1),
      metaMorphoV1_1_block_8654 (immWords := wordsOf (immStore v)) hstack r2⟩
  obtain ⟨aw2, k2, C2, r2⟩ := metaMorphoV1_1_block_8592_fallthrough_packed
    (immWords := wordsOf (immStore v)) hstack
    (by rw [hh]; exact isZero_eq_zero_of_ne hnz) r1
  by_cases ht : (marketRemovalRemovableAt evm id).toNat ≤
      (UInt256.ofNat evm.executionEnv.header.timestamp).toNat
  · obtain ⟨aw3, k3, C3, r3⟩ := metaMorphoV1_1_block_8614_taken_packed
      (immWords := wordsOf (immStore v)) hstack
      (by rw [hh]
          change UInt256.isZero (UInt256.lt _ (marketRemovalRemovableAt evm id)) ≠ ⟨0⟩
          rw [ult_zero ht]; decide)
      (by rw [metaMorphoV1_1PatchedValidJumpsRuntime v]; jump_dest) r2
    exact .inr ⟨.inr ⟨hnz, ht⟩, _,
      (hheap.mappingScratch id ⟨13⟩).mappingScratch id ⟨13⟩, aw3, k3, C3, r3⟩
  · obtain ⟨aw3, k3, C3, r3⟩ := metaMorphoV1_1_block_8614_fallthrough_packed
      (immWords := wordsOf (immStore v)) hstack
      (by rw [hh]
          change UInt256.isZero (UInt256.lt _ (marketRemovalRemovableAt evm id)) = ⟨0⟩
          rw [ult_one (Nat.lt_of_not_ge ht)]; rfl) r2
    exact .inl ⟨fun h ↦ h.elim hz (fun h ↦ ht h.2),
      metaMorphoV1_1_block_8637 (immWords := wordsOf (immStore v)) hstack r3⟩

end Benchmarks.Morpho.MetaMorphoV1_1
