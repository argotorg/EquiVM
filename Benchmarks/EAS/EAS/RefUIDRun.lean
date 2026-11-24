import Benchmarks.EAS.EAS.RefUIDRead
import Benchmarks.EAS.EAS.RefUIDSource
import Benchmarks.EAS.EAS.GetAttestationEVM
import Reasoning.ExternalCall

variable {fork : Ethereum.Fork}
open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables Benchmarks.EAS.EAS.Immutables
namespace Benchmarks.EAS.EAS

theorem refUIDRun {L : Store} {evm : EVM.State} {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C heap : Nat}
    {word src t1 t2 t3 t4 : UInt256} {r : AttestationRequestRecord} {R : List UInt256}
    (v : EASImmutables) (site : UIDSite) (hstack : R.length+21 ≤ 1024) (hs : SourceState s0 ee σ evm)
    (hmem : 96 ≤ mem.size) (hrequest : L.get? "request" = some r.struct)
    (hh : L.get? "$EAS.freeMemory" = some (.int (Int.ofNat heap)))
    (hload : memLoad (refUIDPtr site t3+UInt256.ofNat 96) mem = r.refUID)
    (rd : RD fork (deployedRuntime v) ee g s0 (bytesWrittenPC site)
      (bytesWriteSaved site word src t1 t2 t3 t4 R) mem aw rdata σ k C) :
    if r.refUID = ⟨0⟩ ∨ dbUIDWord evm r.refUID ≠ ⟨0⟩ then
      ∃ mem' dummy aw' k' C', (∀ limit, MemoryPrefix mem mem' limit) ∧
        memLoad (UInt256.ofNat 64) mem' = memLoad (UInt256.ofNat 64) mem ∧
        ExecStmt fork config {contract := contract,locals := L,immutables := immStore v} evm refUIDStmt
          (.ok {contract := contract,locals := refUIDLocals L r.refUID (dbUIDWord evm r.refUID) heap,immutables := immStore v} evm) ∧
        RD fork (deployedRuntime v) ee g s0 (refUIDReadyPC site)
          (refUIDReadyStack site dummy word src t1 t2 t3 t4 R) mem' aw' rdata σ k' C'
    else ExecStmt fork config {contract := contract,locals := L,immutables := immStore v} evm refUIDStmt .reverted ∧
      RDrev fork (deployedRuntime v) g s0 := by
  have hsol := refUIDSource (fork := fork) (imms := immStore v) (evm := evm) hrequest hh
  obtain ⟨aw1,k1,C1,hr1⟩ := easRefUIDDispatch v site hstack hload rd
  by_cases hz : r.refUID = ⟨0⟩
  · rw [if_pos hz] at hr1
    rw [if_pos (Or.inl hz)] at hsol ⊢
    exact ⟨mem,r.refUID,aw1,k1,C1,MemoryPrefix.refl mem,rfl,hsol,hr1⟩
  · rw [if_neg hz] at hr1
    obtain ⟨aw2,k2,C2,hr2⟩ := easRefUIDRead v site hstack hr1
    have hw : dbUIDWord evm r.refUID = solcSlotWord σ ee (dbSlot r.refUID) := hs.storageRead _
    rw [← hw] at hr2
    have hreq := easRefUIDRequire v site
      (by cases site <;> simp only [refUIDReadSaved,List.length_cons] <;> omega) hr2
    by_cases hv : dbUIDWord evm r.refUID = ⟨0⟩
    · rw [if_pos hv] at hreq
      rw [if_neg (by tauto)] at hsol ⊢
      exact ⟨hsol,hreq⟩
    · rw [if_neg hv] at hreq
      rw [if_pos (Or.inr hv)] at hsol ⊢
      obtain ⟨aw3,k3,C3,hr3⟩ := hreq
      obtain ⟨dummy,aw4,k4,C4,hr4⟩ := easRefUIDFinish v site hstack hr3
      refine ⟨twoWordHashMem r.refUID ⟨1⟩ mem,dummy,aw4,k4,C4,?_,?_,hsol,hr4⟩
      · intro limit
        exact (memoryPrefix_sparse_writeWord mem 0 limit r.refUID (Or.inr (by decide))).trans
          (memoryPrefix_sparse_writeWord _ 32 limit (⟨1⟩ : UInt256) (Or.inr (by decide)))
      · exact twoWordHashMem_heap r.refUID ⟨1⟩ (memLoad (UInt256.ofNat 64) mem) mem hmem rfl

end Benchmarks.EAS.EAS
