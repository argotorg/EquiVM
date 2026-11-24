import Benchmarks.EAS.EAS.RequestTimeRun
import Benchmarks.EAS.EAS.RequestRevocableControl
import Benchmarks.EAS.EAS.RequestGuards
import Benchmarks.EAS.EAS.ReadTimeBlock
import Benchmarks.EAS.EAS.SchemaMemory
import Reasoning.ExternalCall

variable {fork : Ethereum.Fork}
open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables Benchmarks.EAS.EAS.Immutables
namespace Benchmarks.EAS.EAS

theorem easRequestGuards {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : Nat}
    {cell schema idx t3 t4 dataPtr : UInt256} {R : List UInt256} {r : AttestationRequestRecord} {s : SchemaRecord}
    (v : EASImmutables) (site : UIDSite) (hstack : R.length+17 ≤ 1024)
    (hp : memLoad cell mem = refUIDPtr site t3)
    (hv : AttestationRequestMemoryView mem (refUIDPtr site t3) dataPtr r)
    (hs : SchemaMemoryView mem (requestSchemaPtr site) s)
    (rd : RD fork (deployedRuntime v) ee g s0 (requestTimePC site) (requestTimeStack site cell schema idx t3 t4 R) mem aw rdata σ k C) :
    if (r.expirationTime.toNat = 0 ∨ (easTimeWord ee).toNat < r.expirationTime.toNat) ∧ (s.revocable || !r.revocable) = true then
      ∃ aw' k' C', RD fork (deployedRuntime v) ee g s0 (recordPreparePC site)
        (uidSaved site (refUIDPtr site t3+UInt256.ofNat 32) (schema::idx::t3::t4::R)) mem aw' rdata σ k' C'
    else RDrev fork (deployedRuntime v) g s0 := by
  have ht := easRequestTimeRun v site hstack hp ((u256_land_comm _ _).trans hv.expiration) rd
  by_cases htime : r.expirationTime.toNat = 0 ∨ (easTimeWord ee).toNat < r.expirationTime.toNat
  · rw [if_pos htime] at ht
    obtain ⟨aw1,k1,C1,h1⟩ := ht
    obtain ⟨aw2,k2,C2,h2⟩ := easRequestRevocableCheck v site (by omega) hs.revocable hv.revocable h1
    have h3 := easRequestRevocableRequire v site
      (by cases site <;> simp only [uidSaved,List.length_cons] <;> omega) h2
    have hb : ((!s.revocable && r.revocable).toUInt256 = (⟨0⟩ : UInt256)) ↔ (s.revocable || !r.revocable) = true := by
      cases s.revocable <;> cases r.revocable <;> decide
    by_cases hg : (s.revocable || !r.revocable) = true
    · rw [if_pos ⟨htime,hg⟩]
      simpa only [if_pos (hb.mpr hg)] using h3
    · rw [if_neg (by tauto)]
      simpa only [if_neg (fun h => hg (hb.mp h))] using h3
  · rw [if_neg (by tauto)]
    simpa only [if_neg htime] using ht

def requestGuardsBody : Body := readTimeBlock "__c1$allocation" "__c1" ++ attestRequestGuards

theorem requestGuardsRun {L : Store} {evm : EVM.State} {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : Nat}
    {cell schema idx t3 t4 dataPtr : UInt256} {heap : Nat} {R : List UInt256} {r : AttestationRequestRecord} {s : SchemaRecord}
    (v : EASImmutables) (site : UIDSite) (hstack : R.length+17 ≤ 1024) (hstate : SourceState s0 ee σ evm)
    (hr : L.get? "request" = some r.struct) (hs : L.get? "schemaRecord" = some s.value)
    (hh : L.get? "$EAS.freeMemory" = some (.int (Int.ofNat heap)))
    (hp : memLoad cell mem = refUIDPtr site t3)
    (hv : AttestationRequestMemoryView mem (refUIDPtr site t3) dataPtr r)
    (hsv : SchemaMemoryView mem (requestSchemaPtr site) s)
    (rd : RD fork (deployedRuntime v) ee g s0 (requestTimePC site) (requestTimeStack site cell schema idx t3 t4 R) mem aw rdata σ k C) :
    let L' := readTimeLocals L "__c1$allocation" "__c1" (easTimeWord ee) heap
    if (r.expirationTime.toNat = 0 ∨ (easTimeWord ee).toNat < r.expirationTime.toNat) ∧ (s.revocable || !r.revocable) = true then
      ExecBlock fork config {contract := contract,locals := L,immutables := immStore v} evm requestGuardsBody
        (.ok {contract := contract,locals := L',immutables := immStore v} evm) ∧
      ∃ aw' k' C', RD fork (deployedRuntime v) ee g s0 (recordPreparePC site)
        (uidSaved site (refUIDPtr site t3+UInt256.ofNat 32) (schema::idx::t3::t4::R)) mem aw' rdata σ k' C'
    else ExecBlock fork config {contract := contract,locals := L,immutables := immStore v} evm requestGuardsBody .reverted ∧
      RDrev fork (deployedRuntime v) g s0 := by
  dsimp only
  have ht := readTimeBlock_source (fork := fork) (cfg := config) (imms := immStore v) (evm := evm) "__c1$allocation" "__c1" hh
    (by decide : ("__c1$allocation" == "$EAS.freeMemory") = false)
    (by decide : ("__c1" == "__c1$allocation") = false) (by decide : ("__c1" == "$EAS.freeMemory") = false)
  rw [hstate.env] at ht
  have hg := attestRequestGuards_source (fork := fork) (imms := immStore v) (evm := evm)
    (L := readTimeLocals L "__c1$allocation" "__c1" (easTimeWord ee) heap)
    (by simpa (disch := decide) only [readTimeLocals,heapResultLocals_get] using hr)
    (by simpa (disch := decide) only [readTimeLocals,heapResultLocals_get] using hs)
    (heapResultLocals_result _ _ _ _ _ _ (by decide))
  have he := easRequestGuards v site hstack hp hv hsv rd
  by_cases hok : (r.expirationTime.toNat = 0 ∨ (easTimeWord ee).toNat < r.expirationTime.toNat) ∧ (s.revocable || !r.revocable) = true
  · rw [if_pos hok] at hg he ⊢
    exact ⟨execBlock_append ht hg,he⟩
  · rw [if_neg hok] at hg he ⊢
    exact ⟨execBlock_append ht hg,he⟩

end Benchmarks.EAS.EAS
