import Benchmarks.EAS.EAS.WordArrayAllocationView
import Benchmarks.EAS.EAS.WordSequence

variable {fork : Ethereum.Fork}
open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables Benchmarks.EAS.EAS.Immutables
namespace Benchmarks.EAS.EAS
set_option maxRecDepth 10000

def arrayTableAllocationMemory (mem : ByteArray) (heap : UInt256) (len : Nat) : ByteArray :=
  writeWordSequence (arrayAllocationHeaderMemory mem heap len) (heap.toNat+32)
    (List.replicate len (UInt256.ofNat 96))

theorem easArrayTableFill {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : Nat}
    {base ret : UInt256} {R : List UInt256} (v : EASImmutables) (hstack : R.length+10 ≤ 1024)
    (i n : Nat) (hspace : base.toNat+32+32*(i+n) < UInt256.size)
    (hret : (D_J (deployedRuntime v) 0).contains ret = true)
    (rd : RD fork (deployedRuntime v) ee g s0 ⟨5167⟩
      (UInt256.ofNat (32*i)::base::UInt256.ofNat (32*(i+n))::ret::base::R) mem aw rdata σ k C) :
    ∃ aw' k' C', RD fork (deployedRuntime v) ee g s0 ret (base::R)
      (writeWordSequence mem (base.toNat+32+32*i) (List.replicate n (UInt256.ofNat 96))) aw' rdata σ k' C' := by
  induction n generalizing i mem aw k C with
  | zero =>
    simp only [Nat.add_zero,List.replicate_zero,writeWordSequence] at rd ⊢
    obtain ⟨a1,k1,C1,r1⟩ := easBlocks.eas_block_5167_fallthrough_packed (immWords := wordsOf (immStore v))
      (by simp only [List.length_cons]; omega) (ult_zero (le_refl _)) rd
    exact easBlocks.eas_block_5175_packed (immWords := wordsOf (immStore v))
      (by simp only [List.length_cons]; omega) hret r1
  | succ n ih =>
    have hn : (UInt256.ofNat (32*(i+(n+1)))).toNat = 32*(i+(n+1)) := ulit_toNat' _ (by omega)
    have hi : (UInt256.ofNat (32*i)).toNat = 32*i := ulit_toNat' _ (by omega)
    obtain ⟨a1,k1,C1,r1⟩ := easBlocks.eas_block_5167_taken_packed (immWords := wordsOf (immStore v))
      (by simp only [List.length_cons]; omega) (by rw [ult_one (by rw [hi,hn]; omega)]; decide)
      (by rw [easPatchedValidJumpsRuntime v]; jump_dest) rd
    obtain ⟨a2,k2,C2,r2⟩ := easBlocks.eas_block_5179_packed (immWords := wordsOf (immStore v))
      (by simp only [List.length_cons]; omega) (by rw [easPatchedValidJumpsRuntime v]; jump_dest) r1
    have hslot : ((base+UInt256.ofNat (32*i))+UInt256.ofNat 32).toNat = base.toNat+32+32*i := by
      have hadd := uadd_word_ofNat_toNat base (32*i) (by omega)
      rw [uadd_word_ofNat_toNat _ 32 (by rw [hadd]; omega),hadd]
      omega
    have hindex : UInt256.ofNat (32*i)+UInt256.ofNat 32 = UInt256.ofNat (32*(i+1)) := by
      simpa only [Nat.mul_add,Nat.mul_one] using (u256_add_comm (UInt256.ofNat (32*i)) (⟨32⟩ : UInt256)).trans (u256_32_add_ofNat (32*i))
    have hend : i+(n+1) = (i+1)+n := by omega
    have rnext : RD fork (deployedRuntime v) ee g s0 ⟨5167⟩
        (UInt256.ofNat (32*(i+1))::base::UInt256.ofNat (32*((i+1)+n))::ret::base::R)
        (Reasoning.Theory.writeWord mem (base.toNat+32+32*i) (UInt256.ofNat 96)) a2 rdata σ k2 C2 := by
      simpa only [easBlocks.eas_block_5179_stack,easBlocks.eas_block_5179_memory,
        Reasoning.Theory.writeWord,hslot,hindex,hend] using r2
    have hrest := ih (i+1) (by omega) rnext
    simpa only [List.replicate_succ,writeWordSequence,
      show base.toNat+32+32*i+32 = base.toNat+32+32*(i+1) by omega] using hrest

theorem easArrayTableAllocate {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : Nat}
    {heap len ret : UInt256} {R : List UInt256} (v : EASImmutables) (hstack : R.length+10 ≤ 1024)
    (hh : heap.toNat ≤ 2^64-1) (hheap : memLoad (UInt256.ofNat 64) mem = heap)
    (hret : (D_J (deployedRuntime v) 0).contains ret = true)
    (rd : RD fork (deployedRuntime v) ee g s0 ⟨5093⟩ (len::ret::R) mem aw rdata σ k C) :
    if len.toNat ≤ 2^64-1 then
      if allocateNext heap.toNat (32+32*len.toNat) ≤ 2^64-1 ∧ heap.toNat ≤ allocateNext heap.toNat (32+32*len.toNat) then
        ∃ aw' k' C', RD fork (deployedRuntime v) ee g s0 ret (heap::R)
          (arrayTableAllocationMemory mem heap len.toNat) aw' rdata σ k' C'
      else RDrev fork (deployedRuntime v) g s0
    else RDrev fork (deployedRuntime v) g s0 := by
  have hhead := easArrayAllocationHead v .arrays hstack hheap rd
  by_cases hl : len.toNat ≤ 2^64-1
  · rw [if_pos hl] at hhead ⊢
    by_cases hg : allocateNext heap.toNat (32+32*len.toNat) ≤ 2^64-1 ∧ heap.toNat ≤ allocateNext heap.toNat (32+32*len.toNat)
    · rw [if_pos hg] at hhead ⊢
      obtain ⟨a1,k1,C1,r1⟩ := hhead
      obtain ⟨a2,k2,C2,r2⟩ := easBlocks.eas_block_5162_packed (immWords := wordsOf (immStore v))
        (by simp only [List.length_cons]; omega) r1
      have hfill := easArrayTableFill v hstack 0 len.toNat
        (by simp only [Nat.zero_add]; change heap.toNat+32+32*len.toNat < 2^256; omega) hret
        (by simpa only [easBlocks.eas_block_5162_stack,wordArraySize_sub32,Nat.mul_zero,Nat.zero_add] using r2)
      simpa only [arrayTableAllocationMemory,Nat.mul_zero,Nat.add_zero] using hfill
    · simpa only [if_neg hg] using hhead
  · simpa only [if_neg hl] using hhead

end Benchmarks.EAS.EAS
