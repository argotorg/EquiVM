import Benchmarks.EAS.EAS.UIDLoopLocals
import Benchmarks.EAS.EAS.GetAttestationEVM
import Reasoning.ExternalCall

variable {fork : Ethereum.Fork}
open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables Benchmarks.EAS.EAS.Immutables
namespace Benchmarks.EAS.EAS
set_option maxRecDepth 10000

theorem uidIterationRun {L : Store} {evm : EVM.State} {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : Nat}
    {src heap dataPtr bump : UInt256} {a : AttestationRecord} {R : List UInt256} (v : EASImmutables) (site : UIDSite)
    (hstack : R.length+30 ≤ 1024) (hf : UIDLoopLocals L a bump heap.toNat) (hs : SourceState s0 ee σ evm)
    (hview : AttestationMemoryView mem src dataPtr a) (hh : heap.toNat ≤ 2^64-1)
    (hheap : memLoad (UInt256.ofNat 64) mem = heap)
    (hdisj : dataPtr.toNat+32+32*((a.data.size+31)/32) ≤ heap.toNat) (hbump : bump.toNat < 2^32)
    (rd : RD fork (deployedRuntime v) ee g s0 (uidStartPC site) (bump::uidSaved site src R) mem aw rdata σ k C) :
    let next := allocateNext heap.toNat (157+a.data.size)
    let word := getUIDWord a bump
    (∃ (mem' : ByteArray) (aw' : UInt256) (k' C' : Nat),
      heap.toNat+160 ≤ next ∧ next ≤ 2^64-1 ∧ MemoryPrefix mem mem' heap.toNat ∧
      memLoad (UInt256.ofNat 64) mem' = UInt256.ofNat next ∧
      ((dbUIDWord evm word = ⟨0⟩ ∧
        ExecBlock fork config {contract := contract,locals := L,immutables := immStore v} evm uidIteration
          (.break {contract := contract,locals := uidComputeLocals L word next,immutables := immStore v} evm) ∧
        RD fork (deployedRuntime v) ee g s0 (uidAvailablePC site) (word::bump::uidSaved site src R) mem' aw' rdata σ k' C') ∨
       (dbUIDWord evm word ≠ ⟨0⟩ ∧
        ExecBlock fork config {contract := contract,locals := L,immutables := immStore v} evm uidIteration
          (.ok {contract := contract,locals := uidNextLocals L word bump next,immutables := immStore v} evm) ∧
        RD fork (deployedRuntime v) ee g s0 (uidStartPC site) (nextUIDBump bump::uidSaved site src R) mem' aw' rdata σ k' C'))) ∨
    (ExecBlock fork config {contract := contract,locals := L,immutables := immStore v} evm uidIteration .reverted ∧
      RDrev fork (deployedRuntime v) g s0) := by
  dsimp only
  let word := getUIDWord a bump
  let next := allocateNext heap.toNat (157+a.data.size)
  have hgrowth : heap.toNat+160 ≤ next := uidHeap_grows heap.toNat a.data.size hh (by have h := hview.dataLow; omega)
  have hargs : evalExprs? config {contract := contract,locals := L,immutables := immStore v} evm
      [.var "attestation",.var "bump",.var "$EAS.freeMemory"] =
      .ok [a.value,.int (Int.ofNat bump.toNat),.int (Int.ofNat heap.toNat)] := by
    simp only [evalExprs?,evalExpr?,hf.attestation,hf.bump,hf.heap,EvalResult.ofOption,EvalResult.bind,bind,pure]
  have hr := getUIDCallRun (retVar := "__c3$allocation") v site hargs hstack hview hh hheap hdisj hbump rd
  rcases hr with ⟨mem',aw1,k1,C1,hmono,hcap,hprefix,hfree,hcall,rd1⟩ | ⟨hcall,hr⟩
  · have hp : MemoryPrefix mem' (twoWordHashMem word ⟨1⟩ mem') heap.toNat :=
      (memoryPrefix_sparse_writeWord mem' 0 heap.toNat word (Or.inr (by decide))).trans
        (memoryPrefix_sparse_writeWord _ 32 heap.toNat (⟨1⟩ : UInt256) (Or.inr (by decide)))
    have hsize : 96 ≤ mem'.size := by have h := hview.dataCovered; have h' := hview.dataLow; have h'' := hprefix.size; omega
    have hfree' := twoWordHashMem_heap word ⟨1⟩ (UInt256.ofNat next) mem' hsize hfree
    obtain ⟨old,hu⟩ := hf.uid
    have hcompute := uidComputeSource hf.heap hu hcall
    have hbranch := easUIDAvailable v site (by cases site <;> simp only [uidSaved,List.length_cons] <;> omega) rd1
    have heq : dbUIDWord evm word = solcSlotWord σ ee (dbSlot word) := hs.storageRead _
    by_cases hz : dbUIDWord evm word = ⟨0⟩
    · have hz' : solcSlotWord σ ee (dbSlot word) = ⟨0⟩ := heq.symm.trans hz
      rw [if_pos hz'] at hbranch
      obtain ⟨aw2,k2,C2,rd2⟩ := hbranch
      exact Or.inl ⟨twoWordHashMem word ⟨1⟩ mem',aw2,k2,C2,hgrowth,hcap,hprefix.trans hp,hfree',
        Or.inl ⟨hz,uidIteration_break hf hz hcompute,rd2⟩⟩
    · have hz' : solcSlotWord σ ee (dbSlot word) ≠ ⟨0⟩ := by rw [← heq]; exact hz
      rw [if_neg hz'] at hbranch
      obtain ⟨aw2,k2,C2,rd2⟩ := hbranch
      obtain ⟨aw3,k3,C3,rd3⟩ := easUIDAgain v site (by cases site <;> simp only [uidSaved,List.length_cons] <;> omega) rd2
      exact Or.inl ⟨twoWordHashMem word ⟨1⟩ mem',aw3,k3,C3,hgrowth,hcap,hprefix.trans hp,hfree',
        Or.inr ⟨hz,uidIteration_next hf hz hbump hcompute,rd3⟩⟩
  · exact Or.inr ⟨ExecBlock.consRevert hcall,hr⟩

end Benchmarks.EAS.EAS
