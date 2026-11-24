import Benchmarks.EAS.EAS.StructAllocate
import Benchmarks.EAS.EAS.RuntimeBlocks_029
import Benchmarks.EAS.Attester.StructAllocMemory

variable {fork : Ethereum.Fork}
open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables Benchmarks.EAS.EAS.Immutables
namespace Benchmarks.EAS.EAS
set_option maxRecDepth 10000

theorem defaultAttestationSlotMemory_eq (mem : ByteArray) (free slot : Nat) (hh : free ≤ 2^64-1) :
    Reasoning.Theory.writeWord (defaultAttestationMemory mem (UInt256.ofNat free)) slot (UInt256.ofNat free) =
      structSlotMemory mem free slot defaultAttestationWords := by
  unfold defaultAttestationMemory
  have hn : allocateNext free 320 = free+320 := fixedAllocation_next .bytes320 hh
  rw [ulit_toNat' _ (by change free < 2^256; omega),hn]
  rfl

theorem easDefaultArrayFill {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : Nat}
    {base ret : UInt256} {R : List UInt256} (v : EASImmutables) (hstack : R.length+14 ≤ 1024)
    (free i n : Nat) (hbase : 96 ≤ base.toNat) (hh : free ≤ 2^64-1)
    (hspace : base.toNat+32+32*(i+n) ≤ free)
    (hheap : memLoad (UInt256.ofNat 64) mem = UInt256.ofNat free)
    (hret : (D_J (deployedRuntime v) 0).contains ret = true)
    (rd : RD fork (deployedRuntime v) ee g s0 ⟨7615⟩
      (UInt256.ofNat (32*i)::base::UInt256.ofNat (32*(i+n))::ret::base::R) mem aw rdata σ k C) :
    if free+320*n ≤ 2^64-1 then
      ∃ aw' k' C', RD fork (deployedRuntime v) ee g s0 ret (base::R)
        (structSlotsMemory mem free (base.toNat+32+32*i) defaultAttestationWords n) aw' rdata σ k' C'
    else RDrev fork (deployedRuntime v) g s0 := by
  induction n generalizing free i mem aw k C with
  | zero =>
    simp only [Nat.mul_zero,Nat.add_zero,if_pos hh,structSlotsMemory] at rd ⊢
    obtain ⟨a1,k1,C1,r1⟩ := easBlocks.eas_block_7615_fallthrough_packed (immWords := wordsOf (immStore v))
      (by simp only [List.length_cons]; omega) (ult_zero (le_refl _)) rd
    exact easBlocks.eas_block_7623_packed (immWords := wordsOf (immStore v))
      (by simp only [List.length_cons]; omega) hret r1
  | succ n ih =>
    have hn : (UInt256.ofNat (32*(i+(n+1)))).toNat = 32*(i+(n+1)) :=
      ulit_toNat' _ (by change 32*(i+(n+1)) < 2^256; omega)
    have hi : (UInt256.ofNat (32*i)).toNat = 32*i := ulit_toNat' _ (by change 32*i < 2^256; omega)
    obtain ⟨a1,k1,C1,r1⟩ := easBlocks.eas_block_7615_taken_packed (immWords := wordsOf (immStore v))
      (by simp only [List.length_cons]; omega) (by rw [ult_one (by rw [hi,hn]; omega)]; decide)
      (by rw [easPatchedValidJumpsRuntime v]; jump_dest) rd
    obtain ⟨a2,k2,C2,r2⟩ := easBlocks.eas_block_7627_packed (immWords := wordsOf (immStore v))
      (by simp only [List.length_cons]; omega) (by rw [easPatchedValidJumpsRuntime v]; jump_dest) r1
    have hf : (UInt256.ofNat free).toNat = free := ulit_toNat' _ (by change free < 2^256; omega)
    have hnext : allocateNext free 320 = free+320 := fixedAllocation_next .bytes320 hh
    by_cases hg : free+320 ≤ 2^64-1
    · obtain ⟨a3,k3,C3,r3⟩ := easDefaultAttestation_ok (heap := UInt256.ofNat free) v
        (by simp only [List.length_cons]; omega) hheap
        (by rw [hf,hnext]; exact ⟨hg,by omega⟩) (by rw [easPatchedValidJumps v]; jump_dest) r2
      obtain ⟨a4,k4,C4,r4⟩ := easBlocks.eas_block_7638_packed (immWords := wordsOf (immStore v))
        (by simp only [List.length_cons]; omega) (by rw [easPatchedValidJumpsRuntime v]; jump_dest) r3
      have hslot : ((base+UInt256.ofNat (32*i))+UInt256.ofNat 32).toNat = base.toNat+32+32*i := by
        have hadd := uadd_word_ofNat_toNat base (32*i) (by change base.toNat+32*i < 2^256; omega)
        rw [uadd_word_ofNat_toNat _ 32 (by rw [hadd]; change base.toNat+32*i+32 < 2^256; omega),hadd]
        omega
      have hindex : UInt256.ofNat (32*i)+UInt256.ofNat 32 = UInt256.ofNat (32*(i+1)) := by
        simpa only [Nat.mul_add,Nat.mul_one] using ofNat_add_words (32*i) 32
      have hend : i+(n+1) = (i+1)+n := by omega
      have rnext : RD fork (deployedRuntime v) ee g s0 ⟨7615⟩
          (UInt256.ofNat (32*(i+1))::base::UInt256.ofNat (32*((i+1)+n))::ret::base::R)
          (structSlotMemory mem free (base.toNat+32+32*i) defaultAttestationWords) a4 rdata σ k4 C4 := by
        have hm := defaultAttestationSlotMemory_eq mem free (base.toNat+32+32*i) hh
        unfold Reasoning.Theory.writeWord at hm
        simpa only [easBlocks.eas_block_7638_stack,easBlocks.eas_block_7638_memory,hslot,hindex,hend,
          hm] using r4
      have hrest := ih (free+320) (i+1) hg (by omega)
        (by simpa only [defaultAttestationWords,List.length_cons,List.length_nil] using
          (structSlotMemory_freePtr (mem := mem) (fields := defaultAttestationWords)
            (slot := base.toNat+32+32*i) (by omega) (by omega))) rnext
      have hs : base.toNat+32+32*i+32 = base.toNat+32+32*(i+1) := by omega
      simpa only [structSlotsMemory,defaultAttestationWords,List.length_cons,List.length_nil,hs,
        show free+320*(n+1) = free+320+320*n by omega] using hrest
    · rw [if_neg (by omega)]
      exact easDefaultAttestation_revert (heap := UInt256.ofNat free) v
        (by simp only [List.length_cons]; omega) hheap (by rw [hf,hnext]; intro h; exact hg h.1) r2

end Benchmarks.EAS.EAS
