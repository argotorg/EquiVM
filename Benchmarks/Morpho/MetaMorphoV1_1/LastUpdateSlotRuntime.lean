import Benchmarks.Morpho.MetaMorphoV1_1.LastUpdateSlotSource
import Benchmarks.Morpho.MetaMorphoV1_1.MorphoSlotAllocation
import Benchmarks.Morpho.MetaMorphoV1_1.RuntimeBlocks_045
import Benchmarks.Morpho.MetaMorphoV1_1.RuntimeBlocks_046

/-! The packed last-update hash, its checked offset, and the singleton slot array. -/

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables
open Benchmarks.Morpho.MetaMorphoV1_1.Immutables metaMorphoV1_1Blocks

namespace Benchmarks.Morpho.MetaMorphoV1_1

open SourceMemory

attribute [local irreducible] metaMorphoV1_1Bytecode
set_option maxRecDepth 2000

theorem lastUpdateReachHash {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap}
    {k C : Nat} {ptr cap params id : UInt256} {R : List UInt256}
    (v : MetaMorphoV1_1Immutables) (hstack : R.length + 12 ≤ 1024)
    (hfree : memLoad ⟨64⟩ mem = ptr) (hfit : ptr.toNat + 96 < 2 ^ 64)
    (rd : RD (deployedRuntime v) I g s0 ⟨8980⟩ (cap :: params :: id :: R)
      mem aw rdata σ k C) :
    ∃ aw' k' C', RD (deployedRuntime v) I g s0 ⟨9012⟩
      (ptr :: (ptr + ⟨32⟩) :: cap :: params :: id :: R)
      (packedPairAllocMem mem ptr id ⟨3⟩) aw' rdata σ k' C' := by
  have hf : memLoad (UInt256.ofNat 64) mem = ptr := hfree
  have hm : metaMorphoV1_1_block_8980_memory (mem := mem) (x2 := id) =
      packedPairMem mem ptr id ⟨3⟩ := by
    unfold metaMorphoV1_1_block_8980_memory
    rw [hf]
    rfl
  obtain ⟨aw1, k1, C1, r1⟩ := metaMorphoV1_1_block_8980_packed
    (immWords := wordsOf (immStore v)) (by omega)
    (by rw [metaMorphoV1_1PatchedValidJumpsRuntime v]; jump_dest) rd
  simp only [metaMorphoV1_1_block_8980_stack, hf, hm] at r1
  exact allocateReturn v (by simp only [List.length_cons]; omega) (by decide) hfit
    (by rw [metaMorphoV1_1PatchedValidJumps v]; jump_dest) r1

theorem lastUpdateHashOffset {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap}
    {k C : Nat} {ptr id : UInt256} {R : List UInt256}
    (v : MetaMorphoV1_1Immutables) (hstack : R.length + 3 ≤ 1024)
    (hlo : 96 ≤ ptr.toNat) (hfit : ptr.toNat + 64 < UInt256.size)
    (rd : RD (deployedRuntime v) I g s0 ⟨9012⟩ (ptr :: (ptr + ⟨32⟩) :: R)
      (packedPairAllocMem mem ptr id ⟨3⟩) aw rdata σ k C) :
    (UInt256.size ≤ (solcMappingSlot ⟨3⟩ id).toNat + 2 ∧
      RDrev (deployedRuntime v) g s0) ∨
    ((solcMappingSlot ⟨3⟩ id).toNat + 2 < UInt256.size ∧ ∃ aw' k' C',
      RD (deployedRuntime v) I g s0 ⟨9027⟩ (lastUpdateSlot id :: R)
        (packedPairAllocMem mem ptr id ⟨3⟩) aw' rdata σ k' C') := by
  have hlen := packedPairAllocMem_length mem ptr id ⟨3⟩ hlo hfit
  have hhash := packedPairAllocMem_hash mem ptr id ⟨3⟩ hlo hfit
  by_cases hs : (solcMappingSlot ⟨3⟩ id).toNat + 2 < UInt256.size
  · obtain ⟨aw1, k1, C1, r1⟩ := metaMorphoV1_1_block_9012_fallthrough_packed
      (immWords := wordsOf (immStore v)) hstack
      (by rw [hlen, hhash, u256_add_comm]; exact checkedAddNoOverflowGt _ _ hs) rd
    exact .inr ⟨hs, aw1, k1, C1, by
      simpa only [metaMorphoV1_1_block_9012_fallthrough_stack, hlen, hhash] using r1⟩
  · obtain ⟨_, _, _, r1⟩ := metaMorphoV1_1_block_9012_taken_packed
      (immWords := wordsOf (immStore v)) hstack
      (by
        rw [hlen, hhash, u256_add_comm, checkedAddOverflowGt _ _
          (by change UInt256.size ≤ (solcMappingSlot ⟨3⟩ id).toNat + 2; omega)]
        decide)
      (by rw [metaMorphoV1_1PatchedValidJumpsRuntime v]; jump_dest) rd
    exact .inl ⟨by omega,
      metaMorphoV1_1_block_9453 (immWords := wordsOf (immStore v))
        (by simp only [metaMorphoV1_1_block_9012_taken_stack, List.length_cons]; omega) r1⟩

def lastUpdateArrayMem (mem calldata : ByteArray) (ptr id : UInt256) : ByteArray :=
  morphoArrayMem (packedPairAllocMem mem ptr id ⟨3⟩) calldata (ptr + ⟨96⟩) (lastUpdateSlot id)

theorem lastUpdateReachArray {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap}
    {k C : Nat} {ptr id : UInt256} {R : List UInt256}
    (v : MetaMorphoV1_1Immutables) (hstack : R.length + 11 ≤ 1024)
    (hcalldata : I.calldata.size < UInt256.size) (hfit : ptr.toNat + 160 < 2 ^ 64)
    (rd : RD (deployedRuntime v) I g s0 ⟨9027⟩ (lastUpdateSlot id :: R)
      (packedPairAllocMem mem ptr id ⟨3⟩) aw rdata σ k C) :
    ∃ aw' k' C', RD (deployedRuntime v) I g s0 ⟨9039⟩
      ((ptr + ⟨96⟩) :: ⟨0⟩ :: ⟨9065⟩ :: R)
      (lastUpdateArrayMem mem I.calldata ptr id) aw' rdata σ k' C' := by
  have r1 := metaMorphoV1_1_block_9027 (immWords := wordsOf (immStore v)) (by omega)
    (by rw [metaMorphoV1_1PatchedValidJumpsRuntime v]; jump_dest) rd
  have h96 : (ptr + ⟨96⟩).toNat = ptr.toNat + 96 :=
    uadd_word_ofNat_toNat ptr 96
      (lt_trans (by omega : ptr.toNat + 96 < 2 ^ 64) (by decide))
  exact morphoArrayReturn v (by simp only [List.length_cons]; omega) hcalldata
    (packedPairAllocMem_free mem ptr id ⟨3⟩)
    (by rw [h96]; omega)
    (by rw [metaMorphoV1_1PatchedValidJumps v]; jump_dest) r1

end Benchmarks.Morpho.MetaMorphoV1_1
