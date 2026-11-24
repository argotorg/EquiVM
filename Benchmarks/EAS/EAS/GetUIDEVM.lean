import Benchmarks.EAS.EAS.UIDTail
import Benchmarks.EAS.EAS.UIDHash

variable {fork : Ethereum.Fork}
open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables Benchmarks.EAS.EAS.Immutables
namespace Benchmarks.EAS.EAS
set_option maxRecDepth 10000

def getUIDMemory (mem : ByteArray) (heap dataPtr : UInt256) (a : AttestationRecord) (bump : UInt256) : ByteArray :=
  Reasoning.Theory.writeWord (uidMemory mem heap dataPtr a bump) 64
    (UInt256.ofNat (allocateNext heap.toNat (157+a.data.size)))

theorem easGetUID {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : Nat}
    {src heap dataPtr bump : UInt256} {a : AttestationRecord} {R : List UInt256} (v : EASImmutables) (site : UIDSite)
    (hstack : R.length+30 ≤ 1024) (hview : AttestationMemoryView mem src dataPtr a)
    (hh : heap.toNat ≤ 2^64-1) (hheap : memLoad (UInt256.ofNat 64) mem = heap)
    (hdisj : dataPtr.toNat+32+32*((a.data.size+31)/32) ≤ heap.toNat)
    (rd : RD fork (deployedRuntime v) ee g s0 (uidStartPC site) (bump::uidSaved site src R) mem aw rdata σ k C) :
    if allocateNext heap.toNat (157+a.data.size) ≤ 2^64-1 ∧ heap.toNat ≤ allocateNext heap.toNat (157+a.data.size) then
      ∃ aw' k' C', RD fork (deployedRuntime v) ee g s0 (uidDonePC site)
        (getUIDWord a bump::bump::uidSaved site src R) (getUIDMemory mem heap dataPtr a bump) aw' rdata σ k' C' ∧
        MemoryPrefix mem (getUIDMemory mem heap dataPtr a bump) heap.toNat ∧
        memLoad (UInt256.ofNat 64) (getUIDMemory mem heap dataPtr a bump) = UInt256.ofNat (allocateNext heap.toNat (157+a.data.size))
    else RDrev fork (deployedRuntime v) g s0 := by
  have hlen : a.data.size < 2^64 := by have hd := hview.dataLow; omega
  have hs : (UInt256.ofNat (157+a.data.size)).toNat = 157+a.data.size := ulit_toNat' _ (by change 157+a.data.size < 2^256; omega)
  have hsaved : (uidSaved site src R).length ≤ R.length+9 := by cases site <;> simp only [uidSaved,List.length_cons] <;> omega
  obtain ⟨aw1,k1,C1,rd1⟩ := easUIDFirst v site (by omega) hview hh hheap rd
  obtain ⟨aw2,k2,C2,rd2⟩ := easUIDSecond v site (by simp only [List.length_cons]; omega) hview hh (by omega) rd1
  obtain ⟨aw3,k3,C3,rd3⟩ := easUIDCopy v site (by simp only [List.length_cons]; omega) hh hlen rd2
  obtain ⟨aw4,k4,C4,rd4⟩ := easUIDTail v site (by omega) hh hlen rd3
  by_cases hg : allocateNext heap.toNat (157+a.data.size) ≤ 2^64-1 ∧ heap.toNat ≤ allocateNext heap.toNat (157+a.data.size)
  · rw [if_pos hg]
    obtain ⟨aw5,k5,C5,rd5⟩ := easAllocate_ok v (by simp only [List.length_cons]; omega)
      (by simpa only [hs] using hg)
      (by cases site <;> rw [easPatchedValidJumps v] <;> simp only [uidHashPC] <;> jump_dest) rd4
    simp only [hs] at rd5
    obtain ⟨aw6,k6,C6,rd6⟩ := easUIDHash v site (by simp only [List.length_cons]; omega) rd5
    rw [uidMemory_hash mem heap dataPtr _ a bump hh hview.dataLow hdisj hview.dataCovered hview.payload] at rd6
    refine ⟨aw6,k6,C6,rd6,?_,?_⟩
    · exact (uidMemory_prefix mem heap dataPtr a bump (by change heap.toNat+153+32*((a.data.size+31)/32) < 2^256; omega)).trans
        (memoryPrefix_sparse_writeWord _ 64 heap.toNat _ (Or.inr (by decide)))
    · apply mloadWordValue_of_readWithPadding
      · change 64 < (getUIDMemory mem heap dataPtr a bump).size
        simp only [getUIDMemory,writeWord_sparse_size]; omega
      · exact writeWord_sparse_read_back _ _ _
  · rw [if_neg hg]
    exact easAllocate_revert v (by simp only [List.length_cons]; omega) (by simpa only [hs] using hg) rd4

end Benchmarks.EAS.EAS
