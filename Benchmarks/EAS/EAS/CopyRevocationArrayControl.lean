import Benchmarks.EAS.EAS.ArrayAllocationHead
import Benchmarks.EAS.EAS.FixedAllocate
import Benchmarks.EAS.EAS.RuntimeBlocks_023
import Benchmarks.EAS.EAS.RuntimeBlocks_024

variable {fork : Ethereum.Fork}
open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables Benchmarks.EAS.EAS.Immutables
namespace Benchmarks.EAS.EAS
set_option maxRecDepth 10000

theorem easCopyRevocationArrayReserve {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : Nat}
    {offset len stop heap ret : UInt256} {R : List UInt256} (v : EASImmutables) (hstack : R.length+12 ≤ 1024)
    (hheap : memLoad (UInt256.ofNat 64) mem = heap) (hlen : len.toNat ≤ 2^64-1)
    (rd : RD fork (deployedRuntime v) ee g s0 ⟨5924⟩ (offset::len::stop::ret::R) mem aw rdata σ k C) :
    if allocateNext heap.toNat (32+32*len.toNat) ≤ 2^64-1 ∧ heap.toNat ≤ allocateNext heap.toNat (32+32*len.toNat) then
      ∃ aw' k' C', RD fork (deployedRuntime v) ee g s0 ⟨5950⟩ (stop::offset::len::ret::heap::R)
        (Reasoning.Theory.writeWord mem 64 (UInt256.ofNat (allocateNext heap.toNat (32+32*len.toNat)))) aw' rdata σ k' C'
    else RDrev fork (deployedRuntime v) g s0 := by
  obtain ⟨a1,k1,C1,r1⟩ := easBlocks.eas_block_5924_packed (immWords := wordsOf (immStore v))
    (by omega) (by rw [easPatchedValidJumpsRuntime v]; jump_dest) rd
  simp only [easBlocks.eas_block_5924_stack] at r1
  have hsize := easArrayAllocationSize v (by simp only [List.length_cons]; omega)
    (by rw [easPatchedValidJumps v]; jump_dest) r1
  rw [if_pos hlen] at hsize
  obtain ⟨a2,k2,C2,r2⟩ := hsize
  obtain ⟨a3,k3,C3,r3⟩ := easBlocks.eas_block_5936_packed (immWords := wordsOf (immStore v))
    (by omega) (by rw [easPatchedValidJumpsRuntime v]; jump_dest) r2
  simp only [easBlocks.eas_block_5936_stack,hheap] at r3
  have hn : (UInt256.ofNat (32+32*len.toNat)).toNat = 32+32*len.toNat :=
    ulit_toNat' _ (by change _ < 2^256; omega)
  split
  · rename_i hg
    obtain ⟨a4,k4,C4,r4⟩ := easAllocate_ok v (by simp only [List.length_cons]; omega)
      (by simpa only [hn] using hg) (by rw [easPatchedValidJumps v]; jump_dest) r3
    rw [hn] at r4
    exact ⟨a4,k4,C4,r4⟩
  · rename_i hg
    exact easAllocate_revert v (by simp only [List.length_cons]; omega) (by simpa only [hn] using hg) r3

theorem easCopyRevocationArrayHead {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : Nat}
    {offset len stop heap ret : UInt256} {R : List UInt256} (v : EASImmutables) (hstack : R.length+12 ≤ 1024)
    (hheap : memLoad (UInt256.ofNat 64) mem = heap) (hlen : len.toNat ≤ 2^64-1)
    (he : UInt256.gt (offset+UInt256.shiftLeft len (UInt256.ofNat 6)) stop = ⟨0⟩)
    (rd : RD fork (deployedRuntime v) ee g s0 ⟨5924⟩ (offset::len::stop::ret::R) mem aw rdata σ k C) :
    if allocateNext heap.toNat (32+32*len.toNat) ≤ 2^64-1 ∧ heap.toNat ≤ allocateNext heap.toNat (32+32*len.toNat) then
      ∃ aw' k' C', RD fork (deployedRuntime v) ee g s0 ⟨5973⟩
        ((heap+UInt256.ofNat 32)::stop::(offset+UInt256.shiftLeft len (UInt256.ofNat 6))::offset::ret::heap::R)
        (arrayAllocationHeaderMemory mem heap len.toNat) aw' rdata σ k' C'
    else RDrev fork (deployedRuntime v) g s0 := by
  have h := easCopyRevocationArrayReserve v hstack hheap hlen rd
  split <;> rename_i hg
  · rw [if_pos hg] at h
    obtain ⟨a4,k4,C4,r4⟩ := h
    obtain ⟨a5,k5,C5,r5⟩ := easBlocks.eas_block_5950_fallthrough_packed (immWords := wordsOf (immStore v))
      (by omega) he r4
    obtain ⟨a6,k6,C6,r6⟩ := easBlocks.eas_block_5972_packed (immWords := wordsOf (immStore v))
      (by simp only [List.length_cons]; omega) r5
    refine ⟨a6,k6,C6,?_⟩
    simpa only [easBlocks.eas_block_5972_stack,easBlocks.eas_block_5950_fallthrough_stack,
      easBlocks.eas_block_5950_fallthrough_memory,arrayAllocationHeaderMemory,Reasoning.Theory.writeWord,u256_ofNat_toNat] using r6
  · simpa only [if_neg hg] using h

theorem easCopyRevocationArrayReject {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : Nat}
    {offset len stop heap ret : UInt256} {R : List UInt256} (v : EASImmutables) (hstack : R.length+12 ≤ 1024)
    (hheap : memLoad (UInt256.ofNat 64) mem = heap) (hlen : len.toNat ≤ 2^64-1)
    (he : UInt256.gt (offset+UInt256.shiftLeft len (UInt256.ofNat 6)) stop ≠ ⟨0⟩)
    (rd : RD fork (deployedRuntime v) ee g s0 ⟨5924⟩ (offset::len::stop::ret::R) mem aw rdata σ k C) :
    RDrev fork (deployedRuntime v) g s0 := by
  have h := easCopyRevocationArrayReserve v hstack hheap hlen rd
  split at h
  · obtain ⟨a1,k1,C1,r1⟩ := h
    obtain ⟨a2,k2,C2,r2⟩ := easBlocks.eas_block_5950_taken_packed (immWords := wordsOf (immStore v))
      (by omega) he (by rw [easPatchedValidJumpsRuntime v]; jump_dest) r1
    exact easBlocks.eas_block_402 (immWords := wordsOf (immStore v))
      (by simp only [easBlocks.eas_block_5950_taken_stack,List.length_cons]; omega) r2
  · exact h

theorem easCopyRevocationArrayDone {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : Nat}
    {dst src stop ret array : UInt256} {R : List UInt256} (v : EASImmutables)
    (hstack : R.length+8 ≤ 1024) (hret : (D_J (deployedRuntime v) 0).contains ret = true)
    (rd : RD fork (deployedRuntime v) ee g s0 ⟨5973⟩ (dst::stop::src::src::ret::array::R) mem aw rdata σ k C) :
    ∃ aw' k' C', RD fork (deployedRuntime v) ee g s0 ret (array::R) mem aw' rdata σ k' C' := by
  obtain ⟨a1,k1,C1,r1⟩ := easBlocks.eas_block_5973_fallthrough_packed (immWords := wordsOf (immStore v))
    (by simp only [List.length_cons]; omega) (ult_zero (le_refl _)) rd
  exact easBlocks.eas_block_5981_packed (immWords := wordsOf (immStore v))
    (by simp only [List.length_cons]; omega) hret r1

def revocationArrayCopyMemory (mem : ByteArray) (cd : ByteArray) (src dst heap : UInt256) : ByteArray :=
  Reasoning.Theory.writeWord
    (Reasoning.Theory.writeWord
      (Reasoning.Theory.writeWord
        (Reasoning.Theory.writeWord mem 64 (UInt256.ofNat (heap.toNat+64)))
        heap.toNat (calldataWord cd src.toNat))
      (heap+UInt256.ofNat 32).toNat (calldataWord cd (src+UInt256.ofNat 32).toNat)) dst.toNat heap

theorem easCopyRevocationArrayStep {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : Nat}
    {dst src limit heap : UInt256} {R : List UInt256} (v : EASImmutables) (hstack : R.length+13 ≤ 1024)
    (hi : src.toNat < limit.toNat) (he : src.toNat+64 ≤ ee.calldata.size)
    (hsize : ee.calldata.size < 2^255) (hh : heap.toNat ≤ 2^64-1)
    (hheap : memLoad (UInt256.ofNat 64) mem = heap)
    (rd : RD fork (deployedRuntime v) ee g s0 ⟨5973⟩
      (dst::UInt256.ofNat ee.calldata.size::limit::src::R) mem aw rdata σ k C) :
    if heap.toNat+64 ≤ 2^64-1 then
      ∃ aw' k' C', RD fork (deployedRuntime v) ee g s0 ⟨5973⟩
        ((dst+UInt256.ofNat 32)::UInt256.ofNat ee.calldata.size::limit::(src+UInt256.ofNat 64)::R)
        (revocationArrayCopyMemory mem ee.calldata src dst heap) aw' rdata σ k' C'
    else RDrev fork (deployedRuntime v) g s0 := by
  obtain ⟨a1,k1,C1,r1⟩ := easBlocks.eas_block_5973_taken_packed (immWords := wordsOf (immStore v))
    (by omega) (by rw [ult_one hi]; decide) (by rw [easPatchedValidJumpsRuntime v]; jump_dest) rd
  obtain ⟨a2,k2,C2,r2⟩ := easBlocks.eas_block_5986_fallthrough_packed (immWords := wordsOf (immStore v))
    (by omega) (solcDecodeLenCheckOk (head := src) (need := ⟨64⟩) he (by omega)
      (by change ee.calldata.size < 2^256; omega) (by decide)) r1
  obtain ⟨a3,k3,C3,r3⟩ := easBlocks.eas_block_5999_packed (immWords := wordsOf (immStore v))
    (by simp only [List.length_cons]; omega) (by rw [easPatchedValidJumpsRuntime v]; jump_dest) r2
  simp only [easBlocks.eas_block_5999_stack,easBlocks.eas_block_5986_fallthrough_stack,hheap] at r3
  have hn : allocateNext heap.toNat FixedAllocationSite.bytes64.size = heap.toNat+64 := fixedAllocation_next .bytes64 hh
  split
  · rename_i hg
    obtain ⟨a4,k4,C4,r4⟩ := easFixedAllocate_ok v .bytes64 (by simp only [List.length_cons]; omega)
      (by rw [hn]; exact ⟨hg,by omega⟩) (by rw [easPatchedValidJumps v]; jump_dest) r3
    rw [hn] at r4
    obtain ⟨a5,k5,C5,r5⟩ := easBlocks.eas_block_6015_packed (immWords := wordsOf (immStore v))
      (by omega) (by rw [easPatchedValidJumpsRuntime v]; jump_dest) r4
    exact ⟨a5,k5,C5,r5⟩
  · rename_i hg
    exact easFixedAllocate_revert v .bytes64 (by simp only [List.length_cons]; omega)
      (by rw [hn]; omega) r3

end Benchmarks.EAS.EAS
