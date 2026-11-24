import Benchmarks.EAS.EAS.RevokeSchemaControl
import Benchmarks.EAS.EAS.RevokeArgs
import Benchmarks.EAS.EAS.RevokeArraysRun
import Benchmarks.EAS.EAS.RevokeLoopFinishRun

variable {fork : Ethereum.Fork}
open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables Benchmarks.EAS.EAS.Immutables
namespace Benchmarks.EAS.EAS
set_option maxRecDepth 10000

def revokeFromSchemaBody : Body := [schemaUIDStmt,revokeLengthDecl] ++ (attestArraysBody ++ ([revokeLoop] ++ revokeFinish))

theorem revokeFromSchemaRun {L : Store} {evm : EVM.State} {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : Nat}
    {rs : List RevocationRequestRecord} {s : SchemaRecord} {R : List UInt256}
    (v : EASImmutables) (site : RevokeSite) (hstack : R.length+37 ≤ 1024) (hs : SourceState s0 ee σ evm)
    (hf : RevokeSetupLocals (L.insert "length" (.int (Int.ofNat rs.length))) site rs s site.records.toNat)
    (hm : RevokeSetupMemory mem site rs s) (hlen : rs.length = site.length)
    (hh : site.records.toNat ≤ 2^64-1) (hheap : memLoad (UInt256.ofNat 64) mem = site.records)
    (hcd : ee.calldata.size < UInt256.size) (hv : site.values = UInt256.ofNat (allocateNext site.records.toNat (32+352*rs.length)))
    (hlast : site.kind = .single → site.last = true) (hret : (D_J (deployedRuntime v) 0).contains site.ret = true)
    (rd : RD fork (deployedRuntime v) ee g s0 (schemaDonePC site.kind.schemaSite)
      (schemaDoneStack v site.kind.schemaSite site.schemaPtr
        (revokeSchemaSaved site.kind site.schema site.data (UInt256.ofNat site.revoker.val) site.available site.last.toUInt256 site.ret R))
      mem aw rdata σ k C) :
    ∃ used : UInt256, HeapReturnPostOrStatic fork (used.toNat ≤ site.available.toNat)
      config (deployedRuntime v) ee g s0 {contract := contract,locals := L,immutables := immStore v} evm
      revokeFromSchemaBody (.int (Int.ofNat used.toNat)) site.ret (used::R) mem site.records.toNat := by
  have hschema : L.get? "schemaRecord" = some s.value := by
    simpa only [store_get_ne _ _ (by decide : ("length" == "schemaRecord") = false)] using hf.schemaRecord
  have hdata : L.get? "data" = some (.array (rs.map RevocationRequestRecord.tuple)) := by
    simpa only [store_get_ne _ _ (by decide : ("length" == "data") = false)] using hf.data
  have hsource := schemaUIDSource (fork := fork) (cfg := config) (imms := immStore v) (evm := evm) hschema
  have hcheck := easSchemaUIDCheck v site.kind.schemaSite
    (by cases hk : site.kind <;> simp only [revokeSchemaSaved,hk,List.length_cons] <;> omega) hm.schemaView.uid rd
  by_cases hz : s.uid ≠ ⟨0⟩
  · rw [if_pos hz] at hsource hcheck
    obtain ⟨a1,k1,C1,r1⟩ := hcheck
    have hr : RD fork (deployedRuntime v) ee g s0 site.kind.arraysPC (revokeArraysStack site R) mem a1 rdata σ k1 C1 := by
      cases hk : site.kind <;> simpa only [hk,RevokeKind.schemaSite,schemaUIDAfterPC,schemaUIDStack,
        revokeSchemaSaved,RevokeKind.arraysPC,revokeArraysStack] using r1
    have hfront := ExecBlock.consNormal hsource (ExecBlock.consNormal (revokeLengthSource (cfg := config) (evm := evm) hdata) ExecBlock.nil)
    have hrun := revokeArraysRun (evm := evm) v site (by omega) hf hm hlen hh hheap hcd hv hr
    dsimp only at hrun
    rcases hrun with ⟨hlo,hhi,hpre,hm1,hf1,hsrc,a2,k2,C2,r2⟩ | ⟨hsrc,hrev⟩
    · let next := allocateNext (allocateNext site.records.toNat (32+352*rs.length)) (32+32*rs.length)
      have hn : (UInt256.ofNat next).toNat = next := ulit_toNat' _ (by change next < 2^256; omega)
      obtain ⟨used,hfinish⟩ := revokeLoopFinishRun (heap := UInt256.ofNat next) v site hstack hs
        (by simpa only [hn] using hf1) (by simpa only [hn] using hm1) (by rw [hn]; exact hhi) hlast hret r2
      exact ⟨used,(hfinish.prepend hsrc hpre (le_refl _)).prepend hfront (.refl _ _) (le_refl _)⟩
    · refine ⟨⟨0⟩,?_⟩
      exact (HeapReturnPostOrStatic.of_revert_prefix (suffix := [revokeLoop] ++ revokeFinish) hsrc hrev).prepend
        hfront (.refl _ _) (le_refl _)
  · rw [if_neg hz] at hsource hcheck
    exact ⟨⟨0⟩,HeapReturnPostOrStatic.of_revert_prefix (ExecBlock.consRevert hsource) hcheck⟩

end Benchmarks.EAS.EAS
