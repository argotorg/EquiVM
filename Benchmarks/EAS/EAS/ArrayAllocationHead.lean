import Benchmarks.EAS.EAS.ArrayAllocationSize
import Benchmarks.EAS.EAS.RuntimeBlocks_027
import Benchmarks.EAS.EAS.RuntimeBlocks_028

variable {fork : Ethereum.Fork}
open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables Benchmarks.EAS.EAS.Immutables
namespace Benchmarks.EAS.EAS
set_option maxRecDepth 10000

inductive ArrayAllocationKind where
  | words | records | arrays
def ArrayAllocationKind.pc : ArrayAllocationKind → UInt256
  | .words => ⟨7240⟩ | .records => ⟨7541⟩ | .arrays => ⟨5093⟩
def ArrayAllocationKind.afterSize : ArrayAllocationKind → UInt256
  | .words => ⟨7250⟩ | .records => ⟨7551⟩ | .arrays => ⟨5103⟩
def ArrayAllocationKind.afterReserve : ArrayAllocationKind → UInt256
  | .words => ⟨7263⟩ | .records => ⟨7564⟩ | .arrays => ⟨5116⟩
def ArrayAllocationKind.initialized : ArrayAllocationKind → UInt256
  | .words => ⟨7309⟩ | .records => ⟨7610⟩ | .arrays => ⟨5162⟩

def arrayAllocationHeaderMemory (mem : ByteArray) (heap : UInt256) (len : Nat) : ByteArray :=
  Reasoning.Theory.writeWord
    (Reasoning.Theory.writeWord mem 64 (UInt256.ofNat (allocateNext heap.toNat (32+32*len))))
    heap.toNat (UInt256.ofNat len)

theorem easArrayAllocationHead {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : Nat}
    {heap len ret : UInt256} {R : List UInt256} (v : EASImmutables) (kind : ArrayAllocationKind)
    (hstack : R.length+10 ≤ 1024) (hheap : memLoad (UInt256.ofNat 64) mem = heap)
    (rd : RD fork (deployedRuntime v) ee g s0 kind.pc (len::ret::R) mem aw rdata σ k C) :
    if len.toNat ≤ 2^64-1 then
      if allocateNext heap.toNat (32+32*len.toNat) ≤ 2^64-1 ∧ heap.toNat ≤ allocateNext heap.toNat (32+32*len.toNat) then
        ∃ aw' k' C', RD fork (deployedRuntime v) ee g s0 kind.initialized
          (UInt256.ofNat (32+32*len.toNat)::
            UInt256.ofNat 115792089237316195423570985008687907853269984665640564039457584007913129639904::heap::ret::heap::R)
          (arrayAllocationHeaderMemory mem heap len.toNat) aw' rdata σ k' C'
      else RDrev fork (deployedRuntime v) g s0
    else RDrev fork (deployedRuntime v) g s0 := by
  have hstart : ∃ a j D, RD fork (deployedRuntime v) ee g s0 ⟨5069⟩
      (len::kind.afterSize::ret::len::R) mem a rdata σ j D := by
    have hd : (D_J (deployedRuntime v) 0).contains (UInt256.ofNat 5069) = true := by rw [easPatchedValidJumps v]; jump_dest
    cases kind with
    | words => exact easBlocks.eas_block_7240_packed (immWords := wordsOf (immStore v)) (by omega) hd rd
    | records => exact easBlocks.eas_block_7541_packed (immWords := wordsOf (immStore v)) (by omega) hd rd
    | arrays => exact easBlocks.eas_block_5093_packed (immWords := wordsOf (immStore v)) (by omega) hd rd
  obtain ⟨a1,k1,C1,r1⟩ := hstart
  have hsize := easArrayAllocationSize v (by simp only [List.length_cons]; omega)
    (by cases kind <;> simp only [ArrayAllocationKind.afterSize] <;> rw [easPatchedValidJumps v] <;> jump_dest) r1
  by_cases hl : len.toNat ≤ 2^64-1
  · rw [if_pos hl] at hsize ⊢
    obtain ⟨a2,k2,C2,r2⟩ := hsize
    have hreserve : ∃ a j D, RD fork (deployedRuntime v) ee g s0 ⟨4883⟩
        (heap::UInt256.ofNat (32+32*len.toNat)::kind.afterReserve::heap::ret::len::R) mem a rdata σ j D := by
      have hd : (D_J (deployedRuntime v) 0).contains (UInt256.ofNat 4883) = true := by rw [easPatchedValidJumps v]; jump_dest
      cases kind with
      | words =>
        obtain ⟨a,j,D,h⟩ := easBlocks.eas_block_7250_packed (immWords := wordsOf (immStore v)) (by simp only [List.length_cons]; omega) hd r2
        exact ⟨a,j,D,by simpa only [easBlocks.eas_block_7250_stack,hheap] using h⟩
      | records =>
        obtain ⟨a,j,D,h⟩ := easBlocks.eas_block_7551_packed (immWords := wordsOf (immStore v)) (by simp only [List.length_cons]; omega) hd r2
        exact ⟨a,j,D,by simpa only [easBlocks.eas_block_7551_stack,hheap] using h⟩
      | arrays =>
        obtain ⟨a,j,D,h⟩ := easBlocks.eas_block_5103_packed (immWords := wordsOf (immStore v)) (by simp only [List.length_cons]; omega) hd r2
        exact ⟨a,j,D,by simpa only [easBlocks.eas_block_5103_stack,hheap] using h⟩
    obtain ⟨a3,k3,C3,r3⟩ := hreserve
    have hn : (UInt256.ofNat (32+32*len.toNat)).toNat = 32+32*len.toNat :=
      ulit_toNat' _ (by change 32+32*len.toNat < 2^256; omega)
    by_cases hg : allocateNext heap.toNat (32+32*len.toNat) ≤ 2^64-1 ∧ heap.toNat ≤ allocateNext heap.toNat (32+32*len.toNat)
    · rw [if_pos hg]
      obtain ⟨a4,k4,C4,r4⟩ := easAllocate_ok v (by simp only [List.length_cons]; omega)
        (by simpa only [hn] using hg)
        (by cases kind <;> simp only [ArrayAllocationKind.afterReserve] <;> rw [easPatchedValidJumps v] <;> jump_dest) r3
      rw [hn] at r4
      have hheader : ∃ a j D, RD fork (deployedRuntime v) ee g s0 ⟨5069⟩
          (len::kind.initialized::UInt256.ofNat 115792089237316195423570985008687907853269984665640564039457584007913129639904::heap::ret::heap::R)
          (arrayAllocationHeaderMemory mem heap len.toNat) a rdata σ j D := by
        have hd : (D_J (deployedRuntime v) 0).contains (UInt256.ofNat 5069) = true := by rw [easPatchedValidJumps v]; jump_dest
        cases kind with
        | words =>
          obtain ⟨a,j,D,h⟩ := easBlocks.eas_block_7263_packed (immWords := wordsOf (immStore v)) (by omega) hd r4
          exact ⟨a,j,D,by simpa only [arrayAllocationHeaderMemory,easBlocks.eas_block_7263_stack,easBlocks.eas_block_7263_memory,
            Reasoning.Theory.writeWord,u256_ofNat_toNat] using h⟩
        | records =>
          obtain ⟨a,j,D,h⟩ := easBlocks.eas_block_7564_packed (immWords := wordsOf (immStore v)) (by omega) hd r4
          exact ⟨a,j,D,by simpa only [arrayAllocationHeaderMemory,easBlocks.eas_block_7564_stack,easBlocks.eas_block_7564_memory,
            Reasoning.Theory.writeWord,u256_ofNat_toNat] using h⟩
        | arrays =>
          obtain ⟨a,j,D,h⟩ := easBlocks.eas_block_5116_packed (immWords := wordsOf (immStore v)) (by omega) hd r4
          exact ⟨a,j,D,by simpa only [arrayAllocationHeaderMemory,easBlocks.eas_block_5116_stack,easBlocks.eas_block_5116_memory,
            Reasoning.Theory.writeWord,u256_ofNat_toNat] using h⟩
      obtain ⟨a5,k5,C5,r5⟩ := hheader
      have hsize2 := easArrayAllocationSize v (by simp only [List.length_cons]; omega)
        (by cases kind <;> simp only [ArrayAllocationKind.initialized] <;> rw [easPatchedValidJumps v] <;> jump_dest) r5
      simpa only [if_pos hl] using hsize2
    · rw [if_neg hg]
      exact easAllocate_revert v (by simp only [List.length_cons]; omega) (by simpa only [hn] using hg) r3
  · rw [if_neg hl] at hsize ⊢
    exact hsize

end Benchmarks.EAS.EAS
