import Benchmarks.Morpho.MetaMorphoV1_1.MaxDepositQueueSource
import Benchmarks.Morpho.MetaMorphoV1_1.ArrayRoutines
import Benchmarks.Morpho.MetaMorphoV1_1.RuntimeBlocks_066
import Benchmarks.Morpho.MetaMorphoV1_1.RuntimeBlocks_067

/-! Queue indexing, packed capacity reads, and loop-control blocks for maxDeposit. -/

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables
open Benchmarks.Morpho.MetaMorphoV1_1.Immutables metaMorphoV1_1Blocks

namespace Benchmarks.Morpho.MetaMorphoV1_1.SourceMemory

attribute [local irreducible] metaMorphoV1_1Bytecode
set_option autoImplicit false
set_option maxRecDepth 2000

def maxDepositQueueMemory (mem : ByteArray) (id : UInt256) : ByteArray :=
  twoWordHashMem id ⟨13⟩ (wordAt0Mem ⟨20⟩ mem)

theorem maxDepositQueueMemory_size {mem : ByteArray} (id : UInt256) (hm : 96 ≤ mem.size) :
    (maxDepositQueueMemory mem id).size = mem.size := by
  change (writeWord (writeWord (writeWord mem 0 ⟨20⟩) 0 id) 32 ⟨13⟩).size = mem.size
  rw [writeWord_sparse_size, writeWord_sparse_size, writeWord_sparse_size]
  omega

theorem maxDepositQueueMemory_free {mem : ByteArray} (id : UInt256) (hm : 96 ≤ mem.size) :
    memLoad ⟨64⟩ (maxDepositQueueMemory mem id) = memLoad ⟨64⟩ mem := by
  change memLoad ⟨64⟩ (writeWord (writeWord (writeWord mem 0 ⟨20⟩) 0 id) 32 ⟨13⟩) = _
  have hw (m : ByteArray) (off : Nat) (w : UInt256) (hm : 96 ≤ m.size)
      (hoff : off + 32 ≤ 64) : memLoad ⟨64⟩ (writeWord m off w) = memLoad ⟨64⟩ m :=
    memLoad_write_disjoint _ _ _ _ hm (.inr hoff)
  rw [hw _ _ _
    (by rw [writeWord_sparse_size, writeWord_sparse_size]; omega) (by decide),
    hw _ _ _ (by rw [writeWord_sparse_size]; omega) (by decide),
    hw _ _ _ hm (by decide)]

theorem maxDepositQueueRoutine {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap}
    {k C : Nat} {morpho len ret i total : UInt256} {R : List UInt256}
    (v : MetaMorphoV1_1Immutables) (hstack : R.length + 10 ≤ 1024)
    (hbound : i.toNat < (codeOwnerStorageWord I σ ⟨20⟩).toNat)
    (rd : RD (deployedRuntime v) I g s0 ⟨13946⟩
      ([morpho, len, i, ret, total] ++ R) mem aw rdata σ k C) :
    ∃ aw' k' C', RD (deployedRuntime v) I g s0
      (if maxDepositCapWord I σ (maxDepositIdWord I σ i) = ⟨0⟩ then ⟨14067⟩ else ⟨13998⟩)
      ([maxDepositIdWord I σ i, maxDepositCapWord I σ (maxDepositIdWord I σ i),
        total, morpho, len, ret, i] ++ R)
      (maxDepositQueueMemory mem (maxDepositIdWord I σ i)) aw' rdata σ k' C' := by
  obtain ⟨aw1, k1, C1, h1⟩ := metaMorphoV1_1_block_13946_packed
    (immWords := wordsOf (immStore v)) (by simp only [List.append, List.length_cons]; omega)
    (by rw [metaMorphoV1_1PatchedValidJumpsRuntime v]; jump_dest) rd
  obtain ⟨k2, C2, h2⟩ := supplyQueueIndex v
    (by simp only [List.append, List.length_cons]; omega) hbound
    (by rw [metaMorphoV1_1PatchedValidJumps v]; jump_dest) h1
  have hshift : UInt256.shiftRight
      (codeOwnerStorageWord I σ (maxDepositQueueSlot i))
        (UInt256.shiftLeft ⟨0⟩ (UInt256.ofNat 3)) =
      maxDepositIdWord I σ i := wordShiftRight_zero _
  dsimp only [codeOwnerStorageWord, maxDepositQueueSlot] at hshift
  have hhash : keccakWord ⟨0⟩ ⟨64⟩ (maxDepositQueueMemory mem (maxDepositIdWord I σ i)) =
      solcMappingSlot ⟨13⟩ (maxDepositIdWord I σ i) :=
    twoWordHashMem_solcMappingSlot_any _ _ _
  have hmask : UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 184))
      (UInt256.ofNat 1) =
      UInt256.ofNat (2 ^ 184 - 1) := rfl
  by_cases hz : maxDepositCapWord I σ (maxDepositIdWord I σ i) = ⟨0⟩
  · obtain ⟨aw3, k3, C3, h3⟩ := metaMorphoV1_1_block_13958_taken_packed
      (immWords := wordsOf (immStore v)) (by simp only [List.append, List.length_cons]; omega)
      (by rw [hshift]
          change UInt256.isZero (UInt256.land _
            (codeOwnerStorageWord I σ (keccakWord ⟨0⟩ ⟨64⟩
              (maxDepositQueueMemory mem (maxDepositIdWord I σ i))))) ≠ ⟨0⟩
          rw [hhash, hmask, u256_land_comm]
          change UInt256.isZero (maxDepositCapWord I σ (maxDepositIdWord I σ i)) ≠ ⟨0⟩
          rw [hz]; decide)
      (by rw [metaMorphoV1_1PatchedValidJumpsRuntime v]; jump_dest) h2
    refine ⟨aw3, k3, C3, ?_⟩
    simp only [metaMorphoV1_1_block_13958_taken_stack,
      metaMorphoV1_1_block_13958_taken_memory, hshift] at h3
    change RD _ _ _ _ _
      (maxDepositIdWord I σ i :: UInt256.land _
        (codeOwnerStorageWord I σ (keccakWord ⟨0⟩ ⟨64⟩
          (maxDepositQueueMemory mem (maxDepositIdWord I σ i)))) :: _) _ _ _ _ _ _ at h3
    rw [hhash, hmask, u256_land_comm] at h3
    simpa only [if_pos hz] using h3
  · obtain ⟨aw3, k3, C3, h3⟩ := metaMorphoV1_1_block_13958_fallthrough_packed
      (immWords := wordsOf (immStore v)) (by simp only [List.append, List.length_cons]; omega)
      (by rw [hshift]
          change UInt256.isZero (UInt256.land _
            (codeOwnerStorageWord I σ (keccakWord ⟨0⟩ ⟨64⟩
              (maxDepositQueueMemory mem (maxDepositIdWord I σ i))))) = ⟨0⟩
          rw [hhash, hmask, u256_land_comm]
          exact isZero_eq_zero_of_ne hz) h2
    refine ⟨aw3, k3, C3, ?_⟩
    simp only [metaMorphoV1_1_block_13958_fallthrough_stack,
      metaMorphoV1_1_block_13958_fallthrough_memory, hshift] at h3
    change RD _ _ _ _ _
      (maxDepositIdWord I σ i :: UInt256.land _
        (codeOwnerStorageWord I σ (keccakWord ⟨0⟩ ⟨64⟩
          (maxDepositQueueMemory mem (maxDepositIdWord I σ i)))) :: _) _ _ _ _ _ _ at h3
    rw [hhash, hmask, u256_land_comm] at h3
    simpa only [if_neg hz] using h3

end Benchmarks.Morpho.MetaMorphoV1_1.SourceMemory
