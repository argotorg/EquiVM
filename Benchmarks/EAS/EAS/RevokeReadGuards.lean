import Benchmarks.EAS.EAS.RevokeLoopLocals
import Benchmarks.EAS.EAS.RevokeLoopControl
import Benchmarks.EAS.EAS.RevokeGuardsRun
import Benchmarks.EAS.EAS.RevocationRequestMemory

variable {fork : Ethereum.Fork}
open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables Benchmarks.EAS.EAS.Immutables
namespace Benchmarks.EAS.EAS

def revokeReadGuardsBody : Body := revokeReadRequest ++ ([revokeBindAlias] ++ revokeGuards)

theorem revokeIteration_parts : revokeIteration = revokeReadGuardsBody ++ (revokeStoreCopyBody ++ revokeUpdateBody) := by
  simp only [revokeIteration,revokeReadGuardsBody,revokeStoreCopyBody,List.append_assoc]

theorem revokeReadGuardsRun {L : Store} {evm : EVM.State} {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C i heap : Nat} {request : UInt256}
    {rs : List RevocationRequestRecord} {s : SchemaRecord} {ats : List AttestationRecord} {values R : List UInt256}
    (v : EASImmutables) (site : RevokeSite) (hstack : R.length+19 ≤ 1024) (hs : SourceState s0 ee σ evm)
    (hf : RevokeLoopLocals L site rs s ats values i heap) (hi : i < rs.length) (hlen : rs.length = site.length)
    (hb : site.data.toNat+32+32*rs.length < UInt256.size) (hl : memLoad site.data mem = UInt256.ofNat rs.length)
    (hp : memLoad (UInt256.ofNat (site.data.toNat+32+32*i)) mem = request)
    (hv : RevocationRequestMemoryView mem request rs[i])
    (rd : RD fork (deployedRuntime v) ee g s0 site.kind.readPC
      (revokeLoopStack site ee (UInt256.ofNat i) R) mem aw rdata σ k C) :
    if revokeGuardsValid (storedAttestationRecord evm rs[i].uid) site.schema site.revoker then
      ExecBlock fork config {contract := contract,locals := L,immutables := immStore v} evm revokeReadGuardsBody
        (.ok {contract := contract,locals := revokeReadLocals L rs[i] heap,immutables := immStore v} evm) ∧
      ∃ aw' k' C', RD fork (deployedRuntime v) ee g s0 site.kind.writePC
        (revokeWriteStack site.kind request (UInt256.ofNat i) (dbSlot rs[i].uid) site.schema
          (UInt256.ofNat site.revoker.val) (revokeGuardRest site ee R))
        (twoWordHashMem rs[i].uid ⟨1⟩ mem) aw' rdata σ k' C'
    else ExecBlock fork config {contract := contract,locals := L,immutables := immStore v} evm revokeReadGuardsBody .reverted ∧
      RDrev fork (deployedRuntime v) g s0 := by
  have hread := revokeReadRequest_source (fork := fork) (imms := immStore v) (evm := evm) hf.data hf.index hi hf.heap
  have hbind := revokeBindAlias_source (fork := fork) (imms := immStore v) (evm := evm) (r := rs[i])
    ((heapResultLocals_get _ _ _ _ _ _ _ (by decide) (by decide) (by decide)).trans hf.db)
    (heapResultLocals_result L "request$allocation" "request" "$EAS.freeMemory" rs[i].struct heap (by decide))
  have hg := revokeGuards_source (fork := fork) (evm := evm) (imms := immStore v) (revokeReadLocals_alias L rs[i] heap)
    ((revokeReadLocals_get L rs[i] heap "schema" (by decide)).trans hf.schema)
    ((revokeReadLocals_get L rs[i] heap "revoker" (by decide)).trans hf.revoker)
  obtain ⟨aw1,k1,C1,rd1⟩ := easRevokeRequestRead v site (by omega) (by omega)
    (by simpa only [← hlen] using hb) (by simpa only [← hlen] using hl) rd
  have hr := easRevokeGuards v site.kind
    (by cases hk : site.kind <;> simp only [revokeGuardRest,hk,List.length_append,List.length_cons,List.length_nil] <;> omega)
    hs hp hv.uid rd1
  by_cases hok : revokeGuardsValid (storedAttestationRecord evm rs[i].uid) site.schema site.revoker
  · rw [if_pos hok] at hg hr ⊢
    exact ⟨execBlock_append hread (ExecBlock.consNormal hbind hg),hr⟩
  · rw [if_neg hok] at hg hr ⊢
    exact ⟨execBlock_append hread (ExecBlock.consNormal hbind hg),hr⟩

end Benchmarks.EAS.EAS
