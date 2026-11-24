import Benchmarks.EAS.EAS.RevokeReadGuards
import Benchmarks.EAS.EAS.RevokeLoopMemory

variable {fork : Ethereum.Fork}
open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables Benchmarks.EAS.EAS.Immutables
namespace Benchmarks.EAS.EAS

theorem revokeIterationRun {L : Store} {evm : EVM.State} {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C i : Nat} {heap : UInt256}
    {rs : List RevocationRequestRecord} {s : SchemaRecord} {ats : List AttestationRecord} {ptrs values R : List UInt256}
    (v : EASImmutables) (site : RevokeSite) (hstack : R.length+37 ≤ 1024) (hs : SourceState s0 ee σ evm)
    (hf : RevokeLoopLocals L site rs s ats values i heap.toNat)
    (hm : RevokeLoopMemory mem site rs s ptrs values ats heap.toNat) (hi : i < rs.length)
    (rd : RD fork (deployedRuntime v) ee g s0 site.kind.readPC
      (revokeLoopStack site ee (UInt256.ofNat i) R) mem aw rdata σ k C) :
    (∃ L' evm' σ' mem' aw' k' C' next a,
      ee.perm = true ∧ heap.toNat ≤ next ∧ next ≤ 2^64-1 ∧
      RevokeLoopLocals L' site rs s (ats.set i a) (values.set i rs[i].value) (i+1) next ∧
      ExecBlock fork config {contract := contract,locals := L,immutables := immStore v} evm revokeIteration
        (.ok {contract := contract,locals := L',immutables := immStore v} evm') ∧
      SourceState s0 ee σ' evm' ∧ MemoryPrefix mem mem' site.records.toNat ∧
      RevokeLoopMemory mem' site rs s (ptrs.set i heap) (values.set i rs[i].value) (ats.set i a) next ∧
      site.values.toNat+32+32*values.length ≤ mem'.size ∧
      RD fork (deployedRuntime v) ee g s0 site.kind.loopPC
        (revokeLoopStack site ee (UInt256.ofNat (i+1)) R) mem' aw' rdata σ' k' C') ∨
    (ExecBlock fork config {contract := contract,locals := L,immutables := immStore v} evm revokeIteration .reverted ∧
      RDrev fork (deployedRuntime v) g s0) ∨
    (ExecBlock fork config {contract := contract,locals := L,immutables := immStore v} evm revokeIteration .staticViolation ∧
      RDstatic fork (deployedRuntime v) g s0) := by
  obtain ⟨request,hcell,hr,hrequest⟩ := hm.requests.requests i hi
  have has := hm.records.span
  have hac := hm.records.covered
  have halo := hm.records.low
  have hvs := hm.valueArray.span
  have hav := hm.recordValues
  have hsc := hm.schemaHigh
  have hpl := hm.lengthRequests
  have hvl := hm.lengthValues
  have hsl := hm.lengthSite
  have hlength := hm.regions.length_eq
  have hsize : 96 ≤ mem.size := by omega
  have hlo : 96 ≤ heap.toNat := by omega
  have harray := lt_of_le_of_lt hm.requests.span site.schemaPtr.val.isLt
  have hfront := revokeReadGuardsRun v site (by omega) hs hf hi hsl harray hm.requests.length hcell hr rd
  rw [revokeIteration_parts]
  by_cases hok : revokeGuardsValid (storedAttestationRecord evm rs[i].uid) site.schema site.revoker
  · rw [if_pos hok] at hfront
    obtain ⟨hfront,aw1,k1,C1,rd1⟩ := hfront
    have hhash : MemoryPrefix mem (twoWordHashMem rs[i].uid ⟨1⟩ mem) heap.toNat :=
      (memoryPrefix_sparse_writeWord _ 0 _ _ (Or.inr (by decide))).trans
        (memoryPrefix_sparse_writeWord _ 32 _ _ (Or.inr (by decide)))
    have hfree : memLoad (UInt256.ofNat 64) (twoWordHashMem rs[i].uid ⟨1⟩ mem) = heap := by
      exact twoWordHashMem_heap rs[i].uid ⟨1⟩ heap mem hsize (by simpa only [u256_ofNat_toNat] using hm.heapRead)
    have hcopy := revokeStoreCopyRun v site hstack hs (revokeReadLocals_alias L rs[i] heap.toNat)
      (revokeReadLocals_request L rs[i] heap.toNat) (revokeReadLocals_heap L rs[i] heap.toNat) hlo hfree rd1
    rcases hcopy with ⟨evm',σ',mid,aw2,k2,C2,next,dp,hs',hperm,hgrow,hcap,hprefix,hpadding,hdp,hview,hend,hdend,hh,hsol,rd2⟩ |
        ⟨hsol,hrev⟩ | ⟨hsol,hstatic⟩
    · let a := storedAttestationRecord evm' rs[i].uid
      let Lp := revokeStoreCopyLocals (revokeReadLocals L rs[i] heap.toNat) (easTimeWord ee) heap.toNat next a
      have keep (name : Ident) (hn : name ∉ ["request$allocation","request","attestation","$EAS.freeMemory"])
          (hn' : name ∉ ["__c1$allocation","__c1","copied$allocation","copied","$EAS.freeMemory"]) :
          Lp.get? name = L.get? name :=
        (revokeStoreCopyLocals_get _ _ _ _ _ _ hn').trans (revokeReadLocals_get _ _ _ _ hn)
      have hup := revokeUpdateSource (fork := fork) (hperm := (congrArg ExecutionEnv.perm hs'.env).trans hperm) (evm := evm') (imms := immStore v) (L := Lp)
        (heapResultLocals_result _ _ _ _ _ _ (by decide))
        ((revokeStoreCopyLocals_get _ _ _ _ _ _ (by decide)).trans (revokeReadLocals_alias L rs[i] heap.toNat))
        ((revokeStoreCopyLocals_get _ _ _ _ _ _ (by decide)).trans (revokeReadLocals_request L rs[i] heap.toNat))
        ((keep "i" (by decide) (by decide)).trans hf.index)
        ((keep "attestations" (by decide) (by decide)).trans hf.attestations)
        ((keep "values" (by decide) (by decide)).trans hf.values)
        ((keep "revoker" (by decide) (by decide)).trans hf.revoker) (by omega) (by omega)
        (by have := hm.requests.span; have := site.schemaPtr.val.isLt; omega)
      have hcore := hhash.trans hprefix
      have hpad := (recordPadding_hash_prefix mem heap.toNat rs[i].uid hsize).trans hpadding
      have hb : next < UInt256.size := by change next < 2^256; omega
      have ha := (hm.records.preserve hcore heap.val.isLt).mono (by omega : heap.toNat ≤ next)
      have hv := (hm.valueArray.preserve hpad heap.val.isLt).mono (by omega : heap.toNat ≤ next)
      have hr' := hr.preserve hcore (by omega) heap.val.isLt
      have haLen : memLoad site.records mid = UInt256.ofNat site.length := by rw [ha.length,hpl,hsl]
      have hvLen : memLoad site.values mid = UInt256.ofNat site.length := by rw [hv.length,hvl,hpl,hsl]
      obtain ⟨aw3,k3,C3,rd3⟩ := easRevokeUpdate v site (by omega) hperm (by omega)
        (by have := hv.span; omega) (by omega) (by have := ha.covered; omega)
        (by have := hv.covered; omega) halo haLen hvLen hr' (by omega) hh rd2
      have hn := hm.next (i := i) (value := rs[i].value) (word := rs[i].uid) hcore hpad hview (by omega) hb hend hdend (by omega) hh
      have hp := (hcore.mono (by omega : site.records.toNat ≤ heap.toNat)).trans
        (revokeUpdateMemory_prefix mid site heap (UInt256.ofNat next) rs[i].value rs[i].uid i
          (by omega) (by rw [ulit_toNat' next hb]; omega))
      have hviews := revokeUpdateMemory_views (i := i) (src := heap) (value := rs[i].value) (word := rs[i].uid)
        site ha hv hav (by omega) (by omega) hb
      refine Or.inl ⟨revokeIterationLocals L rs[i] (easTimeWord ee) heap.toNat next ats values a i,
        evm',σ',_,aw3,k3,C3,next,a,hperm,hgrow,hcap,hf.next,
        execBlock_append hfront (execBlock_append hsol hup),hs',hp,hn,?_,rd3⟩
      simpa only [List.length_set] using hviews.2.1.covered
    · exact Or.inr (Or.inl ⟨execBlock_append hfront (execBlock_append_term hsol (by intros; exact nofun)),hrev⟩)
    · exact Or.inr (Or.inr ⟨execBlock_append hfront (execBlock_append_term hsol (by intros; exact nofun)),hstatic⟩)
  · rw [if_neg hok] at hfront
    exact Or.inr (Or.inl ⟨execBlock_append_term hfront.1 (by intros; exact nofun),hfront.2⟩)

end Benchmarks.EAS.EAS
