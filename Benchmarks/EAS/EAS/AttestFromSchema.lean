import Benchmarks.EAS.EAS.AttestAfterSchema
import Benchmarks.EAS.EAS.AttestReturnRun
import Benchmarks.EAS.EAS.SchemaUIDCheck

variable {fork : Ethereum.Fork}
open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables Benchmarks.EAS.EAS.Immutables
namespace Benchmarks.EAS.EAS
set_option maxRecDepth 10000

def attestFromSchemaBody : Body := [schemaUIDStmt] ++ attestAfterSchemaBody

theorem attestFromSchemaBody_eq : attestFunction.body.drop 14 = attestFromSchemaBody := by native_decide

def attestSchemaSite (site : UIDSite) (schema : UInt256) : SchemaCallSite :=
  match site with
  | .single len _ _ _ _ _ _ _ => .at7795 schema len
  | .many av last ret _ len _ => .at10016 len schema av last ret

def attestSchemaSaved (site : UIDSite) (R : List UInt256) : List UInt256 :=
  match site with
  | .single _ _ av ret data _ result attester => attester::data::av::result::ret::R
  | .many .. => R

theorem attestFromSchemaRun {L : Store} {evm : EVM.State} {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : Nat}
    {schema available heap t3 t4 uidPtr : UInt256} {attester : AccountAddress} {last : Bool}
    {rs : List AttestationRequestRecord} {s : SchemaRecord} {R : List UInt256}
    (v : EASImmutables) (site : UIDSite) (hstack : R.length+38 ≤ 1024) (hs : SourceState s0 ee σ evm)
    (hf : AttestSetupLocals L rs s schema attester available last heap.toNat)
    (hm : AttestSetupMemory mem site uidPtr rs s attester heap.toNat)
    (hlen : attestLoopLength site = UInt256.ofNat rs.length)
    (hh : heap.toNat ≤ 2^64-1) (hheap : memLoad (UInt256.ofNat 64) mem = heap)
    (hcd : ee.calldata.size < UInt256.size) (ha : recordArrayPtr site t3 t4 = heap)
    (hv : recordValuesPtr site t4 = UInt256.ofNat (allocateNext heap.toNat (32+352*rs.length)))
    (hav : attestAvailableWord site = available) (hlast : attestLastWord site = last.toUInt256)
    (hresult : 160 ≤ (recordResultPtr site mem).toNat)
    (hret : (D_J (deployedRuntime v) 0).contains (attestReturnPC site) = true)
    (rd : RD fork (deployedRuntime v) ee g s0 (schemaDonePC (attestSchemaSite site schema))
      (schemaDoneStack v (attestSchemaSite site schema) (requestSchemaPtr site) (attestSchemaSaved site R)) mem aw rdata σ k C) :
    AttestReturnRun fork v ee g s0 L evm attestFromSchemaBody (recordResultPtr site mem) uidPtr available rs.length
      (attestReturnPC site) R mem (recordResultPtr site mem).toNat heap.toNat := by
  have hsource := schemaUIDSource (fork := fork) (cfg := config) (imms := immStore v) (evm := evm) hf.schemaRecord
  have hcheck := easSchemaUIDCheck v (attestSchemaSite site schema)
    (by cases site <;> simp only [attestSchemaSaved,List.length_cons] <;> omega) hm.schemaView.uid rd
  by_cases hz : s.uid ≠ ⟨0⟩
  · rw [if_pos hz] at hsource hcheck
    obtain ⟨a1,k1,C1,r1⟩ := hcheck
    have hr : RD fork (deployedRuntime v) ee g s0 (attestArraysStartPC site)
        (attestArraysStartStack site schema R) mem a1 rdata σ k1 C1 := by
      cases site <;> exact r1
    have hrun : AttestReturnRun fork v ee g s0 L evm attestAfterSchemaBody (recordResultPtr site mem) uidPtr available rs.length
        (attestReturnPC site) R mem (recordResultPtr site mem).toNat heap.toNat :=
      attestAfterSchemaRun v site hstack hs hf hm hlen hh hheap hcd ha hv hav hlast hresult hret hr
    exact hrun.prepend (ExecBlock.consNormal hsource ExecBlock.nil) (.refl _ _) (le_refl _) (le_refl _)
  · rw [if_neg hz] at hsource hcheck
    exact AttestReturnRun.of_revert_prefix (ExecBlock.consRevert hsource) hcheck

end Benchmarks.EAS.EAS
