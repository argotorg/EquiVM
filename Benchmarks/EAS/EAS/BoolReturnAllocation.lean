import Benchmarks.EAS.EAS.BoolMemory
import Benchmarks.EAS.EAS.ResolverCallSource

variable {fork : Ethereum.Fork}
open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables Benchmarks.EAS.EAS.Immutables
namespace Benchmarks.EAS.EAS
set_option maxRecDepth 10000

def resolverReturnMemory (mem : ByteArray) (ptr : UInt256) (out : ByteArray) : ByteArray :=
  Reasoning.Theory.writeWord mem 64 (UInt256.ofNat (allocateNext ptr.toNat (min out.size 32)))


theorem resolverReturnMemory_heap (mem : ByteArray) (ptr : UInt256) (out : ByteArray) :
    memLoad (UInt256.ofNat 64) (resolverReturnMemory mem ptr out) =
      UInt256.ofNat (allocateNext ptr.toNat (min out.size 32)) := by
  apply mloadWordValue_of_readWithPadding
  · change 64 < (resolverReturnMemory mem ptr out).size
    rw [resolverReturnMemory, writeWord_sparse_size]
    omega
  · exact writeWord_sparse_read_back _ _ _


-- Shared allocator/boolean-decoder proof, with a continuation for the caller's stack layout.
theorem boolReturnAtAllocation {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem : ByteArray} {aw : UInt256} {out : ByteArray} {σ : AccountMap} {k C : Nat}
    {ptr lengthPC decodedPC : UInt256} {lengthStack R : List UInt256} (v : EASImmutables)
    (hstack : lengthStack.length+5 ≤ 1024) (hdecodeStack : R.length+4 ≤ 1024)
    (hlo : 96 ≤ ptr.toNat) (hin : ptr.toNat+32 ≤ mem.size)
    (hword : 32 ≤ out.size → memLoad ptr mem = calldataWord out 0)
    (hvalidLength : (D_J (deployedRuntime v) 0).contains lengthPC = true)
    (hvalidDecoded : (D_J (deployedRuntime v) 0).contains decodedPC = true)
    (hdecode : ∀ {mem' aw' k' C'},
      RD fork (deployedRuntime v) ee g s0 lengthPC lengthStack mem' aw' out σ k' C' →
      if 32 ≤ out.size then ∃ aw'' k'' C'',
        RD fork (deployedRuntime v) ee g s0 ⟨7319⟩ (ptr::decodedPC::R) mem' aw'' out σ k'' C''
      else RDrev fork (deployedRuntime v) g s0)
    (rd : RD fork (deployedRuntime v) ee g s0 ⟨4883⟩
      (ptr::UInt256.ofNat (min out.size 32)::lengthPC::lengthStack) mem aw out σ k C) :
    if resolverCallValid ptr.toNat true out then
      ∃ aw' k' C', RD fork (deployedRuntime v) ee g s0 decodedPC (calldataWord out 0::R)
        (resolverReturnMemory mem ptr out) aw' out σ k' C'
    else RDrev fork (deployedRuntime v) g s0 := by
  have hlen : (UInt256.ofNat (min out.size 32)).toNat = min out.size 32 :=
    ulit_toNat' _ (by change min out.size 32 < 2^256; omega)
  by_cases hg : allocateNext ptr.toNat (min out.size 32) ≤ 2^64-1 ∧ ptr.toNat ≤ allocateNext ptr.toNat (min out.size 32)
  · obtain ⟨aw1,k1,C1,rd1⟩ := easAllocate_ok v hstack (by simpa only [hlen] using hg) hvalidLength rd
    simp only [hlen] at rd1
    have hd := hdecode rd1
    by_cases hl : 32 ≤ out.size
    · rw [if_pos hl] at hd
      obtain ⟨aw2,k2,C2,rd2⟩ := hd
      have hm : memLoad ptr (resolverReturnMemory mem ptr out) = calldataWord out 0 := by
        have hp : MemoryPrefix mem (resolverReturnMemory mem ptr out) (ptr.toNat+32) :=
          memoryPrefix_sparse_writeWord mem 64 (ptr.toNat+32) _ (Or.inr (by decide))
        exact (memLoad_of_prefix hp ptr hlo (le_refl _) hin).trans (hword hl)
      have hb := easDecodeBoolMemory v hdecodeStack hvalidDecoded rd2
      change (if memLoad ptr (resolverReturnMemory mem ptr out) = ⟨0⟩ ∨
          memLoad ptr (resolverReturnMemory mem ptr out) = ⟨1⟩ then
        ∃ aw' k' C', RD fork (deployedRuntime v) ee g s0 decodedPC
          (memLoad ptr (resolverReturnMemory mem ptr out)::R) (resolverReturnMemory mem ptr out) aw' out σ k' C'
        else RDrev fork (deployedRuntime v) g s0) at hb
      rw [hm] at hb
      by_cases hc : calldataWord out 0 = ⟨0⟩ ∨ calldataWord out 0 = ⟨1⟩
      · have hv : resolverCallValid ptr.toNat true out := ⟨rfl,hg,hl,hc⟩
        rw [if_pos hv]
        simpa only [if_pos hc] using hb
      · have hv : ¬ resolverCallValid ptr.toNat true out := fun h => hc h.2.2.2
        rw [if_neg hv]
        simpa only [if_neg hc] using hb
    · have hv : ¬ resolverCallValid ptr.toNat true out := fun h => hl h.2.2.1
      rw [if_neg hv]
      simpa only [if_neg hl] using hd
  · have hv : ¬ resolverCallValid ptr.toNat true out := fun h => hg h.2.1
    rw [if_neg hv]
    exact easAllocate_revert v (by simp only [List.length_cons]; omega) (by simpa only [hlen] using hg) rd


end Benchmarks.EAS.EAS
