import Benchmarks.CompoundIII.Comet.UserBasicLoadEvm
import Benchmarks.CompoundIII.Comet.MemoryAllocate
import Benchmarks.CompoundIII.Comet.WordStructAllocation
import Benchmarks.CompoundIII.Comet.RuntimeBlocks_039

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach Reasoning.Immutables
open Benchmarks.CompoundIII.Comet.Immutables cometWithExtendedAssetListBlocks

namespace Benchmarks.CompoundIII.Comet

set_option maxRecDepth 2000

def userBasicAllocatedMemory (mem : ByteArray) (ptr word : UInt256) : ByteArray :=
  userBasicMemoryOf (writeWord mem 64 (ptr + ⟨160⟩)) ptr word

theorem userBasicAllocatedMemory_size (mem : ByteArray) (ptr word : UInt256)
    (hlo : 96 ≤ ptr.toNat) (hb : ptr.toNat + 160 < UInt256.size) :
    (userBasicAllocatedMemory mem ptr word).size = max mem.size (ptr.toNat + 160) :=
  allocatedWordStruct_size (mem := mem) (ptr := ptr) (n := 5)
    (words := userBasicMemWord (userBasicData word)) (by decide) hlo hb

theorem userBasicAllocatedMemory_free (mem : ByteArray) (ptr word : UInt256)
    (hlo : 96 ≤ ptr.toNat) (hb : ptr.toNat + 160 < UInt256.size) :
    memLoad (UInt256.ofNat 64) (userBasicAllocatedMemory mem ptr word) = ptr + ⟨160⟩ :=
  allocatedWordStruct_free (mem := mem) (ptr := ptr) (n := 5)
    (words := userBasicMemWord (userBasicData word)) (by decide) hlo hb

theorem userBasicAllocatedMemory_prefix (mem : ByteArray) (ptr word : UInt256)
    (hb : ptr.toNat + 160 < UInt256.size) :
    MemoryPrefix mem (userBasicAllocatedMemory mem ptr word) ptr.toNat :=
  allocatedWordStruct_prefix (mem := mem) (ptr := ptr) (n := 5)
    (words := userBasicMemWord (userBasicData word)) hb

theorem userBasicInlineLoad_memory (ee : ExecutionEnv) (σ : AccountMap)
    (mem : ByteArray) (ptr slot : UInt256) :
    cometWithExtendedAssetList_block_7670_memory
      (ee := ee) (σ := σ) (mem := mem) (x0 := ptr) (x2 := slot) =
      userBasicMemoryOf mem ptr (solcSlotWordAt slot σ ee) := by
  have he : cometWithExtendedAssetList_block_7670_memory
      (ee := ee) (σ := σ) (mem := mem) (x0 := ptr) (x2 := slot) =
      cometWithExtendedAssetList_block_5353_memory
        (ee := ee) (σ := σ) (mem := mem) (x0 := slot) (x2 := ptr) := by
    unfold cometWithExtendedAssetList_block_7670_memory cometWithExtendedAssetList_block_5353_memory
    rw [u256_land_comm (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1)
      (UInt256.ofNat 64)) (UInt256.ofNat 1))]
  exact he.trans (userBasicLoad_memory ee σ mem ptr slot)

theorem cometAllocateUserBasic {v : CometWithExtendedAssetListImmutables}
    {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem rdata : ByteArray} {aw : UInt256}
    {σ : AccountMap} {k C : Nat} {ptr slot ret : UInt256} {R : List UInt256}
    (hstack : R.length + 9 ≤ 1024) (hfree : memLoad (UInt256.ofNat 64) mem = ptr)
    (hb : ptr.toNat + 160 < 2^64)
    (hret : (D_J (deployedRuntime v) 0).contains ret = true)
    (h : RD (deployedRuntime v) ee g s0 ⟨7655⟩ (slot :: ret :: R) mem aw rdata σ k C) :
    ∃ aw' k' C',
      UserBasicMemory (userBasicAllocatedMemory mem ptr (solcSlotWordAt slot σ ee)) ptr
        (userBasicData (solcSlotWordAt slot σ ee)) ∧
      RD (deployedRuntime v) ee g s0 ret (ptr :: R)
        (userBasicAllocatedMemory mem ptr (solcSlotWordAt slot σ ee)) aw' rdata σ k' C' := by
  have r1 := cometWithExtendedAssetList_block_7655
    (immWords := wordsOf (immStore v)) (by omega)
    (by rw [cometWithExtendedAssetListPatchedValidJumpsRuntime v]; jump_dest) h
  simp only [cometWithExtendedAssetList_block_7655_stack, hfree] at r1
  obtain ⟨aw2, k2, C2, r2⟩ := cometAllocate160 (v := v)
    (by change R.length + 3 + 6 ≤ 1024; omega) (by decide) hb
    (by rw [cometWithExtendedAssetListPatchedValidJumps v]; jump_dest) r1
  obtain ⟨k3, C3, r3⟩ := cometWithExtendedAssetList_block_7670
    (immWords := wordsOf (immStore v)) hstack hret r2
  rw [userBasicInlineLoad_memory, show allocationEnd ptr (UInt256.ofNat 160) =
    ptr + ⟨160⟩ from allocationEnd_160 ptr] at r3
  refine ⟨_, k3, C3, ?_, r3⟩
  apply userBasicMemoryOf_correct
  change ptr.toNat + 160 < 2^256
  omega

end Benchmarks.CompoundIII.Comet
