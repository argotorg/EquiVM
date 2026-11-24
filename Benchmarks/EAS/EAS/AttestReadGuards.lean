import Benchmarks.EAS.EAS.AttestIterationSource
import Benchmarks.EAS.EAS.AttestLoopControl
import Benchmarks.EAS.EAS.RequestGuardsRun
import Benchmarks.EAS.EAS.RecordProcessLocals

variable {fork : Ethereum.Fork}
open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables Benchmarks.EAS.EAS.Immutables
namespace Benchmarks.EAS.EAS

def attestReadGuardsBody : Body := attestReadRequest ++ requestGuardsBody
def attestReadGuardsLocals (L : Store) (r : AttestationRequestRecord) (time : UInt256) (heap : Nat) : Store :=
  readTimeLocals (attestRequestLocals L r heap) "__c1$allocation" "__c1" time heap

theorem attestReadGuardsLocals_get (L : Store) (r : AttestationRequestRecord) (time : UInt256) (heap : Nat) (name : Ident)
    (hn : name ∉ ["request$allocation","request","__c1$allocation","__c1","$EAS.freeMemory"]) :
    (attestReadGuardsLocals L r time heap).get? name = L.get? name := by
  have hne (key : Ident) (hk : key ∈ ["request$allocation","request","__c1$allocation","__c1","$EAS.freeMemory"]) :
      (key == name) = false := beq_false_of_mem_not_mem hn hk
  simp (disch := apply hne; decide) only [attestReadGuardsLocals,readTimeLocals,attestRequestLocals,heapResultLocals_get]

theorem attestReadGuardsLocals_request (L : Store) (r : AttestationRequestRecord) (time : UInt256) (heap : Nat) :
    (attestReadGuardsLocals L r time heap).get? "request" = some r.struct := by
  unfold attestReadGuardsLocals readTimeLocals
  rw [heapResultLocals_get _ _ _ _ _ _ _ (by decide) (by decide) (by decide)]
  exact heapResultLocals_result _ _ _ _ _ _ (by decide)

theorem attestReadGuardsLocals_heap (L : Store) (r : AttestationRequestRecord) (time : UInt256) (heap : Nat) :
    (attestReadGuardsLocals L r time heap).get? "$EAS.freeMemory" = some (.int (Int.ofNat heap)) :=
  heapResultLocals_heap _ _ _ _ _ _

theorem attestReadGuardsRun {L : Store} {evm : EVM.State} {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C i heap : Nat}
    {schema t3 t4 dataPtr : UInt256} {R : List UInt256} {rs : List AttestationRequestRecord} {s : SchemaRecord}
    (v : EASImmutables) (site : UIDSite) (hstack : R.length+17 ≤ 1024) (hstate : SourceState s0 ee σ evm)
    (hd : L.get? "data" = some (.array (rs.map AttestationRequestRecord.tuple)))
    (hi : L.get? "i" = some (.int (Int.ofNat i))) (hs : L.get? "schemaRecord" = some s.value)
    (hh : L.get? "$EAS.freeMemory" = some (.int (Int.ofNat heap))) (hb : i < rs.length)
    (harray : (attestRequestArrayPtr site mem).toNat+32+32*rs.length < UInt256.size)
    (hl : memLoad (attestRequestArrayPtr site mem) mem = UInt256.ofNat rs.length)
    (hp : memLoad (UInt256.ofNat ((attestRequestArrayPtr site mem).toNat+32+32*i)) mem = refUIDPtr site t3)
    (hv : AttestationRequestMemoryView mem (refUIDPtr site t3) dataPtr rs[i])
    (hsv : SchemaMemoryView mem (requestSchemaPtr site) s)
    (rd : RD fork (deployedRuntime v) ee g s0 (requestReadPC site)
      (recordNextStack site schema (UInt256.ofNat i) t3 t4 R) mem aw rdata σ k C) :
    if (rs[i].expirationTime.toNat = 0 ∨ (easTimeWord ee).toNat < rs[i].expirationTime.toNat) ∧ (s.revocable || !rs[i].revocable) = true then
      ExecBlock fork config {contract := contract,locals := L,immutables := immStore v} evm attestReadGuardsBody
        (.ok {contract := contract,locals := attestReadGuardsLocals L rs[i] (easTimeWord ee) heap,immutables := immStore v} evm) ∧
      ∃ aw' k' C', RD fork (deployedRuntime v) ee g s0 (recordPreparePC site)
        (uidSaved site (refUIDPtr site t3+UInt256.ofNat 32) (schema::UInt256.ofNat i::t3::t4::R)) mem aw' rdata σ k' C'
    else ExecBlock fork config {contract := contract,locals := L,immutables := immStore v} evm attestReadGuardsBody .reverted ∧
      RDrev fork (deployedRuntime v) g s0 := by
  have hread := attestReadRequest_source (fork := fork) (imms := immStore v) (evm := evm) hd hi hb hh
  obtain ⟨aw1,k1,C1,hr1⟩ := easAttestRequestRead v site (by omega) hb harray hl rd
  have hg := requestGuardsRun (L := attestRequestLocals L rs[i] heap) v site hstack hstate
    (heapResultLocals_result _ _ _ _ _ _ (by decide))
    ((heapResultLocals_get _ _ _ _ _ _ _ (by decide) (by decide) (by decide)).trans hs)
    (heapResultLocals_heap _ _ _ _ _ _) hp hv hsv hr1
  by_cases hok : (rs[i].expirationTime.toNat = 0 ∨ (easTimeWord ee).toNat < rs[i].expirationTime.toNat) ∧ (s.revocable || !rs[i].revocable) = true
  · rw [if_pos hok] at hg ⊢
    exact ⟨execBlock_append hread hg.1,hg.2⟩
  · rw [if_neg hok] at hg ⊢
    exact ⟨execBlock_append hread hg.1,hg.2⟩

end Benchmarks.EAS.EAS
