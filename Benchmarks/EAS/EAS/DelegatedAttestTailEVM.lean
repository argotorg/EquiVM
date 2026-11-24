import Benchmarks.EAS.EAS.OneRequestResult
import Benchmarks.EAS.EAS.DelegatedAttestPrepare
import Benchmarks.EAS.EAS.AttestControl

variable {fork : Ethereum.Fork}
open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables Benchmarks.EAS.EAS.Immutables
namespace Benchmarks.EAS.EAS
set_option maxRecDepth 10000

theorem easDelegatedAttestTailAllocate {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : Nat}
    {root heap : UInt256} {R : List UInt256} (v : EASImmutables) (hstack : R.length+23 ≤ 1024)
    (hlo : 96 ≤ heap.toNat) (hh : heap.toNat ≤ 2^64-1) (hf : memLoad (UInt256.ofNat 64) mem = heap)
    (hr : requestReferenceValid ee.calldata root (root+UInt256.ofNat 32))
    (rd : RD fork (deployedRuntime v) ee g s0 ⟨2122⟩ (delegatedAttestSavedStack ee.calldata root R).tail mem aw rdata σ k C) :
    if heap.toNat+256 ≤ 2^64-1 then
      ∃ aw' k' C', RD fork (deployedRuntime v) ee g s0 ⟨5344⟩
        (delegatedAttestData ee.calldata root::UInt256.ofNat ee.calldata.size::UInt256.ofNat 2141::
          (root+UInt256.ofNat 160)::UInt256.ofNat 2166::heap::calldataWord ee.calldata root.toNat::
          UInt256.ofNat 587::UInt256.ofNat 32::UInt256.ofNat 594::UInt256.ofNat 32::R)
        (oneRequestArrayMemory mem heap) aw' rdata σ k' C'
    else RDrev fork (deployedRuntime v) g s0 := by
  obtain ⟨a1,k1,C1,r1⟩ := easBlocks.eas_block_2122_packed (immWords := wordsOf (immStore v))
    (by simp only [delegatedAttestSavedStack,List.tail_cons,List.length_cons]; omega)
    (by rw [easPatchedValidJumpsRuntime v]; jump_dest) rd
  simp only [easBlocks.eas_block_2122_stack,delegatedAttestSavedStack,List.tail_cons] at r1
  by_cases hg : heap.toNat+256 ≤ 2^64-1
  · rw [if_pos hg]
    obtain ⟨a2,k2,C2,r2⟩ := easOneRequestAllocate v (by simp only [List.length_cons]; omega)
      hlo hg hf (by rw [easPatchedValidJumps v]; jump_dest) r1
    obtain ⟨a3,k3,C3,r3⟩ := easBlocks.eas_block_2133_packed (immWords := wordsOf (immStore v))
      (by simp only [List.length_cons]; omega) (by rw [easPatchedValidJumpsRuntime v]; jump_dest) r2
    simp only [easBlocks.eas_block_2133_stack] at r3
    have href := easRequestReference v (by simp only [List.length_cons]; omega)
      (by rw [easPatchedValidJumps v]; jump_dest) r3
    rw [if_pos hr] at href
    obtain ⟨a4,k4,C4,r4⟩ := href
    exact easBlocks.eas_block_552_packed (immWords := wordsOf (immStore v))
      (by simp only [List.length_cons]; omega) (by rw [easPatchedValidJumpsRuntime v]; jump_dest) r4
  · rw [if_neg hg]
    exact easOneRequestAllocate_revert v (by simp only [List.length_cons]; omega) hlo hh hg hf r1

theorem easDelegatedAttestTailSet {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : Nat}
    {array ptr head schema : UInt256} {R : List UInt256} (v : EASImmutables) (hstack : R.length+10 ≤ 1024)
    (hfit : array.toNat+32 < UInt256.size) (hc : array.toNat+32 ≤ mem.size)
    (hn : memLoad array mem ≠ ⟨0⟩)
    (ha : (calldataWord ee.calldata head.toNat).toNat < EVM.addressModulus)
    (rd : RD fork (deployedRuntime v) ee g s0 ⟨2141⟩
      (ptr::head::UInt256.ofNat 2166::array::schema::R) mem aw rdata σ k C) :
    ∃ aw' k' C', RD fork (deployedRuntime v) ee g s0 ⟨7650⟩
      (schema::array::calldataWord ee.calldata head.toNat::ee.weiValue::R)
      (Reasoning.Theory.writeWord mem (array.toNat+32) ptr) aw' rdata σ k' C' := by
  obtain ⟨a1,k1,C1,r1⟩ := easBlocks.eas_block_2141_packed (immWords := wordsOf (immStore v))
    (by simp only [List.length_cons]; omega) (by rw [easPatchedValidJumpsRuntime v]; jump_dest) rd
  simp only [easBlocks.eas_block_2141_stack] at r1
  obtain ⟨a2,k2,C2,r2⟩ := easMemoryArrayFirst v (by simp only [List.length_cons]; omega) hn
    (by rw [easPatchedValidJumps v]; jump_dest) r1
  obtain ⟨a3,k3,C3,r3⟩ := easBlocks.eas_block_2150_packed (immWords := wordsOf (immStore v))
    (by simp only [List.length_cons]; omega) (by rw [easPatchedValidJumpsRuntime v]; jump_dest) r2
  simp only [easBlocks.eas_block_2150_stack,easBlocks.eas_block_2150_memory,ulit_toNat' _ hfit,← writeWord_as_write] at r3
  have hn' : memLoad array (Reasoning.Theory.writeWord mem (array.toNat+32) ptr) ≠ ⟨0⟩ := by
    rw [memLoad_write_below _ _ _ _ (le_refl _) hc]; exact hn
  obtain ⟨a4,k4,C4,r4⟩ := easMemoryArrayFirst v (by simp only [List.length_cons]; omega) hn'
    (by rw [easPatchedValidJumps v]; jump_dest) r3
  obtain ⟨a5,k5,C5,r5⟩ := easBlocks.eas_block_2160_packed (immWords := wordsOf (immStore v))
    (by simp only [List.length_cons]; omega) (by rw [easPatchedValidJumpsRuntime v]; jump_dest) r4
  simp only [easBlocks.eas_block_2160_stack] at r5
  obtain ⟨a6,k6,C6,r6⟩ := easBlocks.eas_block_6240_fallthrough_packed (immWords := wordsOf (immStore v))
    (by simp only [List.length_cons]; omega) (by
      change UInt256.sub (calldataWord ee.calldata head.toNat) (UInt256.land (calldataWord ee.calldata head.toNat) solcAddrMask) = ⟨0⟩
      rw [solcAddrMask_clean ha,u256_sub_self]) r5
  obtain ⟨a7,k7,C7,r7⟩ := easBlocks.eas_block_6271_packed (immWords := wordsOf (immStore v))
    (by simp only [List.length_cons]; omega) (by rw [easPatchedValidJumpsRuntime v]; jump_dest) r6
  exact easBlocks.eas_block_2166_packed (immWords := wordsOf (immStore v))
    (by omega) (by rw [easPatchedValidJumpsRuntime v]; jump_dest) r7

end Benchmarks.EAS.EAS
