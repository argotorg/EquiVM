import Benchmarks.EAS.EAS.RecordProcessRun
import Benchmarks.EAS.EAS.RecordTailPreserve

variable {fork : Ethereum.Fork}
open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables Benchmarks.EAS.EAS.Immutables
namespace Benchmarks.EAS.EAS

def attestRecordBody : Body := recordProcessBody ++ recordTailBody

theorem attestRecordRun {L : Store} {evm : EVM.State} {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C i : Nat}
    {heap dataPtr schema t3 t4 uidPtr used : UInt256} {r : AttestationRequestRecord} {attester : AccountAddress}
    {ats : List AttestationRecord} {ptrs values uids R : List UInt256}
    (v : EASImmutables) (site : UIDSite) (hstack : R.length+34 ≤ 1024) (hs : SourceState s0 ee σ evm)
    (hr : L.get? "request" = some r.struct) (hsch : L.get? "schema" = some (wordBytes32Value schema))
    (ha : L.get? "attester" = some (.address attester)) (hh : L.get? "$EAS.freeMemory" = some (.int (Int.ofNat heap.toNat)))
    (hd : L.get? "_db" = none) (hv : AttestationRequestMemoryView mem (refUIDPtr site t3) dataPtr r)
    (hlo : 192 ≤ heap.toNat) (hmem : 192 ≤ mem.size) (hlen : r.data.size < 2^64)
    (hrend : (refUIDPtr site t3).toNat+192 ≤ heap.toNat)
    (hdend : dataPtr.toNat+32+32*((r.data.size+31)/32) ≤ heap.toNat)
    (hat : recordCreateAttester site mem = UInt256.ofNat attester.val)
    (hheap : memLoad (UInt256.ofNat 64) mem = heap)
    (hm : RecordTailMemoryView mem site t3 t4 uidPtr ptrs values uids r.value heap.toNat (recordPadding mem heap.toNat))
    (hli : L.get? "i" = some (.int (Int.ofNat i)))
    (hlas : L.get? "attestations" = some (.array (ats.map AttestationRecord.value)))
    (hlvs : L.get? "values" = some (.array (values.map (fun w => Value.int (Int.ofNat w.toNat)))))
    (hlres : L.get? "res" = some (attestationsResultValue uids used))
    (hlength : ats.length = ptrs.length) (hi : i < ptrs.length)
    (rd : RD fork (deployedRuntime v) ee g s0 (recordPreparePC site)
      (uidSaved site (refUIDPtr site t3+UInt256.ofNat 32) (schema::UInt256.ofNat i::t3::t4::R)) mem aw rdata σ k C) :
    (∃ Lp evm' σ' mp aw' k' C' heap' word,
      let a := {newAttestation r schema (easTimeWord ee) attester with uid := word}
      let final := recordTailMemory mp site heap t3 t4 r.value uidPtr word i
      ee.perm = true ∧ heap.toNat+320 ≤ heap' ∧ heap' ≤ 2^64-1 ∧ RecordProcessKeep L Lp ∧
      Lp.get? "$EAS.freeMemory" = some (.int (Int.ofNat heap')) ∧
      ExecBlock fork config {contract := contract,locals := L,immutables := immStore v} evm attestRecordBody
        (.ok {contract := contract,locals := recordTailLocals Lp ats values uids used a r.value word i,immutables := immStore v} evm') ∧
      SourceState s0 ee σ' evm' ∧ MemoryPrefix mem final uidPtr.toNat ∧ MemoryPrefix mem mp heap.toNat ∧
      AttestationMemoryView mp heap dataPtr a ∧ RecordTailMemoryView mp site t3 t4 uidPtr ptrs values uids r.value heap' ∧
      WordArrayMemoryView final uidPtr (uids.set i word) heap' ∧
      WordArrayMemoryView final (recordArrayPtr site t3 t4) (ptrs.set i heap) heap' ∧
      WordArrayMemoryView final (recordValuesPtr site t4) (values.set i r.value) heap' ∧
      memLoad (UInt256.ofNat 64) final = UInt256.ofNat heap' ∧
      RD fork (deployedRuntime v) ee g s0 (recordNextPC site)
        (recordNextStack site schema (UInt256.ofNat (i+1)) t3 t4 R) final aw' rdata σ' k' C') ∨
    (ExecBlock fork config {contract := contract,locals := L,immutables := immStore v} evm attestRecordBody .reverted ∧
      RDrev fork (deployedRuntime v) g s0) ∨
    (ExecBlock fork config {contract := contract,locals := L,immutables := immStore v} evm attestRecordBody .staticViolation ∧
      RDstatic fork (deployedRuntime v) g s0) := by
  have hp := recordProcessRun v site hstack hs hr hsch ha hh hd hv hlo hmem hlen hrend hdend hat hheap rd
  dsimp only at hp
  rcases hp with ⟨Lp,e1,σ1,m1,dummy,aw1,k1,C1,heap1,word,hperm,hgrowth,hcap,hkeep,hla,hlu,hlh,hsol,hstate,hpre,hpad,hview,hfree,hr1⟩ |
      ⟨hsol,hrev⟩ | ⟨hsol,hstatic⟩
  · have hb : heap1 < UInt256.size := by change heap1 < 2^256; omega
    have hm1 := hm.preserveValues hpre hpad heap.val.isLt (by omega) (by omega) (by omega) hfree
    have hf : RecordTailSourceView Lp ats values uids used word schema
        {newAttestation r schema (easTimeWord ee) attester with uid := word} r attester i :=
      ⟨hla,(hkeep "request" (by decide)).trans hr,hlu,(hkeep "i" (by decide)).trans hli,
        (hkeep "attestations" (by decide)).trans hlas,(hkeep "values" (by decide)).trans hlvs,
        (hkeep "res" (by decide)).trans hlres,(hkeep "attester" (by decide)).trans ha,(hkeep "schema" (by decide)).trans hsch⟩
    obtain ⟨hs2,hu2,ha2,hv2,hh2,aw2,k2,C2,hr2⟩ := recordTailRun
      (hperm := (congrArg ExecutionEnv.perm hstate.env).trans hperm)
      v site (by omega) hperm hf hm1 hlength hi hb hr1
    exact Or.inl ⟨Lp,e1,σ1,m1,aw2,k2,C2,heap1,word,hperm,hgrowth,hcap,hkeep,hlh,
      execBlock_append hsol hs2,hstate,(hpre.mono (by have := hm.uidArray.span; omega)).trans
        (recordTailMemory_prefix site hm1 hi hb),hpre,hview,hm1,hu2,ha2,hv2,hh2,hr2⟩
  · exact Or.inr (Or.inl ⟨execBlock_append_term hsol (by intros; exact nofun),hrev⟩)
  · exact Or.inr (Or.inr ⟨execBlock_append_term hsol (by intros; exact nofun),hstatic⟩)

end Benchmarks.EAS.EAS
