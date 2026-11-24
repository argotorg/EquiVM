import Benchmarks.EAS.EAS.NewRecordRunSource
import Benchmarks.EAS.EAS.RecordPrepare
import Benchmarks.EAS.EAS.StructAllocate
import Reasoning.ExternalCall
import Benchmarks.EAS.EAS.RecordPadding

variable {fork : Ethereum.Fork}
open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables Benchmarks.EAS.EAS.Immutables
namespace Benchmarks.EAS.EAS

set_option maxRecDepth 10000 in
theorem newRecordRun {L : Store} {evm : EVM.State} {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : Nat}
    {heap dataPtr schema idx t3 t4 : UInt256} {r : AttestationRequestRecord} {attester : AccountAddress} {R : List UInt256}
    (v : EASImmutables) (site : UIDSite) (hstack : R.length+26 ≤ 1024) (hs : SourceState s0 ee σ evm)
    (hr : L.get? "request" = some r.struct) (hsch : L.get? "schema" = some (wordBytes32Value schema))
    (ha : L.get? "attester" = some (.address attester)) (hh : L.get? "$EAS.freeMemory" = some (.int (Int.ofNat heap.toNat)))
    (hd : L.get? "_db" = none) (hv : AttestationRequestMemoryView mem (refUIDPtr site t3) dataPtr r)
    (hlo : 192 ≤ heap.toNat) (hmem : 192 ≤ mem.size)
    (hrend : (refUIDPtr site t3).toNat+192 ≤ heap.toNat)
    (hdend : dataPtr.toNat+32+32*((r.data.size+31)/32) ≤ heap.toNat)
    (hat : recordCreateAttester site mem = UInt256.ofNat attester.val)
    (hheap : memLoad (UInt256.ofNat 64) mem = heap)
    (rd : RD fork (deployedRuntime v) ee g s0 (recordPreparePC site)
      (uidSaved site (refUIDPtr site t3+UInt256.ofNat 32) (schema::idx::t3::t4::R)) mem aw rdata σ k C) :
    let a := newAttestation r schema (easTimeWord ee) attester
    let next := allocateNext heap.toNat 320
    if next ≤ 2^64-1 ∧ heap.toNat ≤ next then
      ∃ mem' aw' k' C',
        ExecBlock fork config {contract := contract,locals := L,immutables := immStore v} evm newRecordBody
          (.ok {contract := contract,locals := newRecordLocals L r schema (easTimeWord ee) attester heap.toNat,immutables := immStore v} evm) ∧
        UIDLoopLocals (newRecordLocals L r schema (easTimeWord ee) attester heap.toNat) a ⟨0⟩ next ∧
        MemoryPrefix mem mem' heap.toNat ∧ MemoryPrefix (recordPadding mem heap.toNat) mem' heap.toNat ∧ AttestationMemoryView mem' heap dataPtr a ∧
        memLoad (UInt256.ofNat 64) mem' = UInt256.ofNat next ∧
        RD fork (deployedRuntime v) ee g s0 (uidStartPC site) (⟨0⟩::uidSaved site heap (schema::idx::t3::t4::R)) mem' aw' rdata σ k' C'
    else ExecBlock fork config {contract := contract,locals := L,immutables := immStore v} evm newRecordBody .reverted ∧
      RDrev fork (deployedRuntime v) g s0 := by
  dsimp only
  have hsol := newRecordSource (fork := fork) (imms := immStore v) (evm := evm) hr hsch ha hh
  rw [hs.env] at hsol
  obtain ⟨aw1,k1,C1,hr1⟩ := easRecordPrepare v site hstack hv hheap rd
  by_cases hg : allocateNext heap.toNat 320 ≤ 2^64-1 ∧ heap.toNat ≤ allocateNext heap.toNat 320
  · rw [if_pos hg] at hsol ⊢
    have hb : heap.toNat+320 < UInt256.size := by have := (allocate320_bounds hg).2; change heap.toNat+320 < 2^256; omega
    obtain ⟨aw2,k2,C2,hr2⟩ := easAllocate320_ok v
      (by cases site <;> simp only [recordCreateStack,List.length_cons] <;> omega) hg
      (by cases site <;> simp only [recordCreatePC] <;> rw [easPatchedValidJumps v] <;> jump_dest) hr1
    let allocated := Reasoning.Theory.writeWord mem 64 (UInt256.ofNat (allocateNext heap.toNat 320))
    have hp : MemoryPrefix mem allocated heap.toNat := memoryPrefix_sparse_writeWord _ _ _ _ (Or.inr (by decide))
    have hv1 := hv.preserve hp hrend hdend heap.val.isLt
    have hat1 : recordCreateAttester site allocated = UInt256.ofNat attester.val := by
      cases site with
      | single _ _ _ _ _ _ _ _ => exact hat
      | many _ _ _ _ _ _ =>
        dsimp only [recordCreateAttester] at hat ⊢
        rw [memLoad_write_above mem 64 (UInt256.ofNat 160)
          (UInt256.ofNat (allocateNext heap.toNat 320)) (by decide) hmem]
        exact hat
    obtain ⟨aw3,k3,C3,hr3⟩ := easRecordCreate v site (by omega) hlo (by rw [writeWord_sparse_size]; omega) hb hat1 hr2
    have ht : (easTimeWord ee).toNat < 2^64 := u256LandMaskToNatLtOfToNat _ _ (by decide)
    have he : r.expirationTime.toNat < 2^64 := by
      rw [← hv.expiration,u256_land_comm]
      exact u256LandMaskToNatLtOfToNat _ _ (by decide)
    have hav := recordCreateMemory_view (a := newAttestation r schema (easTimeWord ee) attester)
      (by omega) hv1.dataLow hdend hv1.dataCovered hv1.length hv1.payload ht he (by change 0 < 2^64; decide) hb
    refine ⟨_,aw3,k3,C3,hsol,?_,hp.trans (writeWordSequence_prefix _ _ _ _ (le_refl _)),
      recordCreateMemory_padding_prefix mem heap dataPtr _ rfl,hav,?_,hr3⟩
    · apply newAttestationLocals_uid
      · exact store_get_self _ _ _
      · simpa (disch := decide) only [allocateBlockLocals_get,readTimeLocals,heapResultLocals_get] using hd
    · exact writeWordSequence_setFree_load64 mem heap.toNat _ _ (by omega)
  · rw [if_neg hg] at hsol ⊢
    exact ⟨hsol,easAllocate320_revert v
      (by cases site <;> simp only [recordCreateStack,List.length_cons] <;> omega) hg hr1⟩

end Benchmarks.EAS.EAS
