import Benchmarks.Morpho.MetaMorphoV1_1.WordArrayIndexRuntime
import Benchmarks.Morpho.MetaMorphoV1_1.MarketRemovalStorage
import Benchmarks.Morpho.MetaMorphoV1_1.RuntimeBlocks_029
import Benchmarks.Morpho.MetaMorphoV1_1.RuntimeBlocks_042
import Benchmarks.Morpho.MetaMorphoV1_1.RuntimeBlocks_043

/-! Fresh queue bounds and the two storage guards preceding an omitted-market reader call. -/

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables
open Benchmarks.Morpho.MetaMorphoV1_1.Immutables metaMorphoV1_1Blocks

namespace Benchmarks.Morpho.MetaMorphoV1_1

attribute [local irreducible] metaMorphoV1_1Bytecode
set_option maxRecDepth 2000

theorem updateWithdrawQueueOmittedIndex {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem out : ByteArray} {aw : UInt256} {σ : AccountMap} {k C : Nat}
    {i : UInt256} {R : List UInt256}
    (v : MetaMorphoV1_1Immutables) (hstack : R.length + 5 ≤ 1024)
    (rd : RD (deployedRuntime v) I g s0 ⟨8460⟩ (i :: R) mem aw out σ k C) :
    ((codeOwnerStorageWord I σ ⟨21⟩).toNat ≤ i.toNat ∧ RDrev (deployedRuntime v) g s0) ∨
    (i.toNat < (codeOwnerStorageWord I σ ⟨21⟩).toNat ∧ ∃ aw' k' C',
      RD (deployedRuntime v) I g s0 ⟨8469⟩
        (⟨0⟩ :: (uInt256OfByteArray (KEC (UInt256.toByteArray ⟨21⟩)) + i) :: i :: R)
        (wordAt0Mem ⟨21⟩ mem) aw' out σ k' C') := by
  have r1 := metaMorphoV1_1_block_8460 (immWords := wordsOf (immStore v)) (by omega)
    (by rw [metaMorphoV1_1PatchedValidJumpsRuntime v]; jump_dest) rd
  by_cases hi : i.toNat < (codeOwnerStorageWord I σ ⟨21⟩).toNat
  · obtain ⟨k2, C2, r2⟩ := withdrawQueueIndex v
      (by simp only [List.length_cons]; omega) hi
      (by rw [metaMorphoV1_1PatchedValidJumps v]; jump_dest) r1
    exact .inr ⟨hi, _, k2, C2, r2⟩
  · exact .inl ⟨by omega, withdrawQueueIndexRevert v
      (by simp only [List.length_cons]; omega) (by omega) r1⟩

theorem updateWithdrawQueueBeforeCallRuntime {evm s0 : State} {g : Sat256}
    {mem out : ByteArray} {aw : UInt256} {k C : Nat} {slot id : UInt256} {R : List UInt256}
    (v : MetaMorphoV1_1Immutables) (hstack : R.length + 5 ≤ 1024)
    (hid : codeOwnerStorageWord evm.executionEnv evm.accountMap slot = id)
    (rd : RD (deployedRuntime v) evm.executionEnv g s0 ⟨8469⟩
      (⟨0⟩ :: slot :: R) mem aw out evm.accountMap k C) :
    (¬ (marketRemovalCap evm id = ⟨0⟩ ∧ marketRemovalPendingAt evm id = ⟨0⟩) ∧
      RDrev (deployedRuntime v) g s0) ∨
    (marketRemovalCap evm id = ⟨0⟩ ∧ marketRemovalPendingAt evm id = ⟨0⟩ ∧
      ∃ aw' k' C', RD (deployedRuntime v) evm.executionEnv g s0 ⟨8526⟩ (id :: R)
        (twoWordHashMem id ⟨16⟩ (twoWordHashMem id ⟨13⟩ mem)) aw' out evm.accountMap k' C') := by
  have hs : UInt256.shiftLeft (⟨0⟩ : UInt256) (UInt256.ofNat 3) = ⟨0⟩ := rfl
  have hv : UInt256.shiftRight
      (evm.accountMap.get? evm.executionEnv.codeOwner |>.option (⟨0⟩ : UInt256)
        (fun ac ↦ ac.storage.getD slot ⟨0⟩)) ⟨0⟩ = id := by
    rw [wordShiftRight_zero]
    exact hid
  have hh (m : ByteArray) (base : UInt256) :
      keccakWord ⟨0⟩ (UInt256.ofNat 64)
        (base.toByteArray.write 0 (id.toByteArray.write 0 m (⟨0⟩ : UInt256).toNat 32)
          (UInt256.ofNat 32).toNat 32) = solcMappingSlot base id :=
    twoWordHashMem_solcMappingSlot_any _ _ _
  have hmask : UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 184))
      (UInt256.ofNat 1) = UInt256.ofNat (2 ^ 184 - 1) := rfl
  by_cases hcap : marketRemovalCap evm id = ⟨0⟩
  case neg =>
    obtain ⟨aw1, k1, C1, r1⟩ := metaMorphoV1_1_block_8469_taken_packed
      (immWords := wordsOf (immStore v)) hstack
      (by rw [hs, hv, hh, hmask, u256_land_comm]; exact hcap)
      (by rw [metaMorphoV1_1PatchedValidJumpsRuntime v]; jump_dest) rd
    exact .inl ⟨fun h ↦ hcap h.1,
      metaMorphoV1_1_block_8672 (immWords := wordsOf (immStore v)) (by omega) r1⟩
  obtain ⟨aw1, k1, C1, r1⟩ := metaMorphoV1_1_block_8469_fallthrough_packed
    (immWords := wordsOf (immStore v)) hstack
    (by rw [hs, hv, hh, hmask, u256_land_comm]; exact hcap) rd
  simp only [metaMorphoV1_1_block_8469_fallthrough_stack,
    metaMorphoV1_1_block_8469_fallthrough_memory, hs, hv] at r1
  by_cases htime : marketRemovalPendingAt evm id = ⟨0⟩
  case neg =>
    obtain ⟨aw2, k2, C2, r2⟩ := metaMorphoV1_1_block_8506_taken_packed
      (immWords := wordsOf (immStore v)) (by omega) (by rw [hh]; exact htime)
      (by rw [metaMorphoV1_1PatchedValidJumpsRuntime v]; jump_dest) r1
    exact .inl ⟨fun h ↦ htime h.2,
      metaMorphoV1_1_block_5453 (immWords := wordsOf (immStore v)) (by omega) r2⟩
  obtain ⟨aw2, k2, C2, r2⟩ := metaMorphoV1_1_block_8506_fallthrough_packed
    (immWords := wordsOf (immStore v)) (by omega) (by rw [hh]; exact htime) r1
  exact .inr ⟨hcap, htime, aw2, k2, C2, r2⟩

end Benchmarks.Morpho.MetaMorphoV1_1
