import Benchmarks.EAS.EAS.DefaultArrayFill
import Benchmarks.EAS.EAS.WordArrayAllocationView

variable {fork : Ethereum.Fork}
open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables Benchmarks.EAS.EAS.Immutables
namespace Benchmarks.EAS.EAS
set_option maxRecDepth 10000

theorem allocateNext_recordArray {heap len : Nat} (hh : heap ≤ 2^64-1) (hl : len ≤ 2^64-1) :
    allocateNext heap (32+352*len) = heap+32+352*len := by
  rw [allocateNext_small hh (by omega)]
  omega

def defaultArrayMemory (mem : ByteArray) (heap : UInt256) (len : Nat) : ByteArray :=
  structSlotsMemory (arrayAllocationHeaderMemory mem heap len) (heap.toNat+32+32*len)
    (heap.toNat+32) defaultAttestationWords len

theorem easDefaultArrayAllocate {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : Nat}
    {heap len ret : UInt256} {R : List UInt256} (v : EASImmutables) (hstack : R.length+14 ≤ 1024)
    (hlo : 96 ≤ heap.toNat) (hh : heap.toNat ≤ 2^64-1) (hheap : memLoad (UInt256.ofNat 64) mem = heap)
    (hret : (D_J (deployedRuntime v) 0).contains ret = true)
    (rd : RD fork (deployedRuntime v) ee g s0 ⟨7541⟩ (len::ret::R) mem aw rdata σ k C) :
    if len.toNat ≤ 2^64-1 then
      if allocateNext heap.toNat (32+352*len.toNat) ≤ 2^64-1 ∧ heap.toNat ≤ allocateNext heap.toNat (32+352*len.toNat) then
        ∃ aw' k' C', RD fork (deployedRuntime v) ee g s0 ret (heap::R)
          (defaultArrayMemory mem heap len.toNat) aw' rdata σ k' C'
      else RDrev fork (deployedRuntime v) g s0
    else RDrev fork (deployedRuntime v) g s0 := by
  have hhead := easArrayAllocationHead v .records (by omega) hheap rd
  by_cases hl : len.toNat ≤ 2^64-1
  · rw [if_pos hl] at hhead ⊢
    have hsmall := allocateNext_wordArray hh hl
    have hfull := allocateNext_recordArray hh hl
    by_cases hg : allocateNext heap.toNat (32+32*len.toNat) ≤ 2^64-1 ∧ heap.toNat ≤ allocateNext heap.toNat (32+32*len.toNat)
    · rw [if_pos hg] at hhead
      obtain ⟨a1,k1,C1,r1⟩ := hhead
      obtain ⟨a2,k2,C2,r2⟩ := easBlocks.eas_block_7610_packed (immWords := wordsOf (immStore v))
        (by simp only [List.length_cons]; omega) r1
      have hr : RD fork (deployedRuntime v) ee g s0 ⟨7615⟩
          (UInt256.ofNat (32*0)::heap::UInt256.ofNat (32*(0+len.toNat))::ret::heap::R)
          (arrayAllocationHeaderMemory mem heap len.toNat) a2 rdata σ k2 C2 := by
        simpa only [easBlocks.eas_block_7610_stack,wordArraySize_sub32,Nat.mul_zero,Nat.zero_add] using r2
      have hf : memLoad (UInt256.ofNat 64) (arrayAllocationHeaderMemory mem heap len.toNat) =
          UInt256.ofNat (heap.toNat+32+32*len.toNat) := by
        change memLoad (UInt256.ofNat 64)
          (writeWordSequence (Reasoning.Theory.writeWord mem 64
            (UInt256.ofNat (allocateNext heap.toNat (32+32*len.toNat)))) heap.toNat [UInt256.ofNat len.toNat]) = _
        rw [writeWordSequence_setFree_load64 _ _ _ _ hlo,hsmall]
      have hfill := easDefaultArrayFill v hstack (heap.toNat+32+32*len.toNat) 0 len.toNat hlo
        (by rw [hsmall] at hg; exact hg.1) (by simp only [Nat.zero_add]; exact le_refl _) hf hret hr
      have htotal : heap.toNat+32+32*len.toNat+320*len.toNat = heap.toNat+32+352*len.toNat := by omega
      have hbound : heap.toNat ≤ heap.toNat+32+352*len.toNat := by omega
      simpa only [hfull,hbound,and_true,htotal,defaultArrayMemory,Nat.mul_zero,Nat.add_zero] using hfill
    · rw [if_neg hg] at hhead
      rw [if_neg (by
        intro h
        apply hg
        rw [hsmall]
        rw [hfull] at h
        constructor <;> omega)]
      exact hhead
  · simpa only [if_neg hl] using hhead

end Benchmarks.EAS.EAS
