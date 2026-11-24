import Benchmarks.EAS.EAS.AttestLoopLocals
import Benchmarks.EAS.EAS.AttestRecordRun
import Benchmarks.EAS.EAS.RecordTailRecord

variable {fork : Ethereum.Fork}
open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables Benchmarks.EAS.EAS.Immutables
namespace Benchmarks.EAS.EAS

theorem attestIteration_parts : attestIteration = attestReadGuardsBody ++ attestRecordBody := by
  rw [attestIteration_eq]
  simp only [attestReadGuardsBody,requestGuardsBody,attestRecordBody,recordProcessBody,List.append_assoc]

theorem attestIterationRun {L : Store} {evm : EVM.State} {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C i : Nat}
    {heap dataPtr schema t3 t4 uidPtr available used : UInt256} {attester : AccountAddress} {last : Bool}
    {rs : List AttestationRequestRecord} {s : SchemaRecord} {ats : List AttestationRecord} {ptrs values uids R : List UInt256}
    (v : EASImmutables) (site : UIDSite) (hstack : R.length+34 ≤ 1024) (hs : SourceState s0 ee σ evm)
    (hf : AttestLoopLocals L rs s schema attester available last ats values uids used i heap.toNat)
    (hi : i < rs.length) (hlo : 192 ≤ heap.toNat) (hmem : 192 ≤ mem.size) (hdata : rs[i].data.size < 2^64)
    (harray : (attestRequestArrayPtr site mem).toNat+32+32*rs.length < UInt256.size)
    (hl : memLoad (attestRequestArrayPtr site mem) mem = UInt256.ofNat rs.length)
    (hp : memLoad (UInt256.ofNat ((attestRequestArrayPtr site mem).toNat+32+32*i)) mem = refUIDPtr site t3)
    (hv : AttestationRequestMemoryView mem (refUIDPtr site t3) dataPtr rs[i])
    (hsv : SchemaMemoryView mem (requestSchemaPtr site) s)
    (hdataend : dataPtr.toNat+32+32*((rs[i].data.size+31)/32) ≤ uidPtr.toNat)
    (hat : recordCreateAttester site mem = UInt256.ofNat attester.val)
    (hheap : memLoad (UInt256.ofNat 64) mem = heap)
    (hm : RecordTailMemoryView mem site t3 t4 uidPtr ptrs values uids rs[i].value heap.toNat (recordPadding mem heap.toNat))
    (hlength : ats.length = ptrs.length) (hptrlen : ptrs.length = rs.length)
    (rd : RD fork (deployedRuntime v) ee g s0 (requestReadPC site)
      (recordNextStack site schema (UInt256.ofNat i) t3 t4 R) mem aw rdata σ k C) :
    (∃ L' evm' σ' mp aw' k' C' heap' word,
      let a := {newAttestation rs[i] schema (easTimeWord ee) attester with uid := word}
      let final := recordTailMemory mp site heap t3 t4 rs[i].value uidPtr word i
      ee.perm = true ∧ heap.toNat+320 ≤ heap' ∧ heap' ≤ 2^64-1 ∧
      AttestLoopLocals L' rs s schema attester available last (ats.set i a) (values.set i rs[i].value) (uids.set i word) used (i+1) heap' ∧
      ExecBlock fork config {contract := contract,locals := L,immutables := immStore v} evm attestIteration
        (.ok {contract := contract,locals := L',immutables := immStore v} evm') ∧
      SourceState s0 ee σ' evm' ∧ MemoryPrefix mem final uidPtr.toNat ∧ MemoryPrefix mem mp heap.toNat ∧
      AttestationMemoryView mp heap dataPtr a ∧ AttestationMemoryView final heap dataPtr a ∧
      RecordTailMemoryView mp site t3 t4 uidPtr ptrs values uids rs[i].value heap' ∧
      WordArrayMemoryView final uidPtr (uids.set i word) heap' ∧
      WordArrayMemoryView final (recordArrayPtr site t3 t4) (ptrs.set i heap) heap' ∧
      WordArrayMemoryView final (recordValuesPtr site t4) (values.set i rs[i].value) heap' ∧
      memLoad (UInt256.ofNat 64) final = UInt256.ofNat heap' ∧
      RD fork (deployedRuntime v) ee g s0 (recordNextPC site)
        (recordNextStack site schema (UInt256.ofNat (i+1)) t3 t4 R) final aw' rdata σ' k' C') ∨
    (ExecBlock fork config {contract := contract,locals := L,immutables := immStore v} evm attestIteration .reverted ∧
      RDrev fork (deployedRuntime v) g s0) ∨
    (ExecBlock fork config {contract := contract,locals := L,immutables := immStore v} evm attestIteration .staticViolation ∧
      RDstatic fork (deployedRuntime v) g s0) := by
  have hfront := attestReadGuardsRun v site (by omega) hs hf.data hf.index hf.schemaRecord hf.heap hi harray hl hp hv hsv rd
  rw [attestIteration_parts]
  split at hfront
  · obtain ⟨hfront,aw1,k1,C1,rd1⟩ := hfront
    have hu := hm.uidArray.span
    have hr := hm.requestEnd
    have hrec := attestRecordRun (L := attestReadGuardsLocals L rs[i] (easTimeWord ee) heap.toNat)
      v site hstack hs (attestReadGuardsLocals_request _ _ _ _)
      ((attestReadGuardsLocals_get _ _ _ _ _ (by decide)).trans hf.schema)
      ((attestReadGuardsLocals_get _ _ _ _ _ (by decide)).trans hf.attester)
      (attestReadGuardsLocals_heap _ _ _ _)
      ((attestReadGuardsLocals_get _ _ _ _ _ (by decide)).trans hf.db) hv hlo hmem hdata (by omega) (by omega) hat hheap hm
      ((attestReadGuardsLocals_get _ _ _ _ _ (by decide)).trans hf.index)
      ((attestReadGuardsLocals_get _ _ _ _ _ (by decide)).trans hf.attestations)
      ((attestReadGuardsLocals_get _ _ _ _ _ (by decide)).trans hf.values)
      ((attestReadGuardsLocals_get _ _ _ _ _ (by decide)).trans hf.result) hlength (by omega) rd1
    rcases hrec with ⟨Lp,e1,σ1,m1,aw2,k2,C2,heap2,word,hperm,hgrowth,hcap,hkeep,hlheap,hsol,hstate,hpre,hpm,hav,hm1,hu2,ha2,hv2,hh2,hr2⟩ |
        ⟨hsol,hrev⟩ | ⟨hsol,hstatic⟩
    · have hb : heap2 < UInt256.size := by change heap2 < 2^256; omega
      exact Or.inl ⟨_,e1,σ1,m1,aw2,k2,C2,heap2,word,hperm,hgrowth,hcap,hf.afterRecord hkeep hlheap,
        execBlock_append hfront hsol,hstate,hpre,hpm,hav,
        recordTailMemory_record site hm1 hav (by omega) hb hgrowth hm.valueArray.span hdataend,
        hm1,hu2,ha2,hv2,hh2,hr2⟩
    · exact Or.inr (Or.inl ⟨execBlock_append hfront hsol,hrev⟩)
    · exact Or.inr (Or.inr ⟨execBlock_append hfront hsol,hstatic⟩)
  · exact Or.inr (Or.inl ⟨execBlock_append_term hfront.1 (by intros; exact nofun),hfront.2⟩)

end Benchmarks.EAS.EAS
