import Benchmarks.EAS.EAS.RecordProcessLocals

variable {fork : Ethereum.Fork}
open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables Benchmarks.EAS.EAS.Immutables
namespace Benchmarks.EAS.EAS

def recordProcessBody : Body := newRecordBody ++ [.while (.boolLit true) uidIteration] ++ recordStoreBody ++ [refUIDStmt]

theorem recordProcessRun {L : Store} {evm : EVM.State} {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : Nat}
    {heap dataPtr schema idx t3 t4 : UInt256} {r : AttestationRequestRecord} {attester : AccountAddress} {R : List UInt256}
    (v : EASImmutables) (site : UIDSite) (hstack : R.length+34 ≤ 1024) (hs : SourceState s0 ee σ evm)
    (hr : L.get? "request" = some r.struct) (hsch : L.get? "schema" = some (wordBytes32Value schema))
    (ha : L.get? "attester" = some (.address attester)) (hh : L.get? "$EAS.freeMemory" = some (.int (Int.ofNat heap.toNat)))
    (hd : L.get? "_db" = none) (hv : AttestationRequestMemoryView mem (refUIDPtr site t3) dataPtr r)
    (hlo : 192 ≤ heap.toNat) (hmem : 192 ≤ mem.size) (hlen : r.data.size < 2^64)
    (hrend : (refUIDPtr site t3).toNat+192 ≤ heap.toNat)
    (hdend : dataPtr.toNat+32+32*((r.data.size+31)/32) ≤ heap.toNat)
    (hat : recordCreateAttester site mem = UInt256.ofNat attester.val)
    (hheap : memLoad (UInt256.ofNat 64) mem = heap)
    (rd : RD fork (deployedRuntime v) ee g s0 (recordPreparePC site)
      (uidSaved site (refUIDPtr site t3+UInt256.ofNat 32) (schema::idx::t3::t4::R)) mem aw rdata σ k C) :
    let a := newAttestation r schema (easTimeWord ee) attester
    (∃ L' evm' σ' mem' dummy aw' k' C' heap' word,
      ee.perm = true ∧ heap.toNat+320 ≤ heap' ∧ heap' ≤ 2^64-1 ∧ RecordProcessKeep L L' ∧
      L'.get? "attestation" = some {a with uid := word}.value ∧
      L'.get? "uid" = some (wordBytes32Value word) ∧ L'.get? "$EAS.freeMemory" = some (.int (Int.ofNat heap')) ∧
      ExecBlock fork config {contract := contract,locals := L,immutables := immStore v} evm recordProcessBody
        (.ok {contract := contract,locals := L',immutables := immStore v} evm') ∧
      SourceState s0 ee σ' evm' ∧ MemoryPrefix mem mem' heap.toNat ∧
      MemoryPrefix (recordPadding mem heap.toNat) mem' heap.toNat ∧
      AttestationMemoryView mem' heap dataPtr {a with uid := word} ∧
      memLoad (UInt256.ofNat 64) mem' = UInt256.ofNat heap' ∧
      RD fork (deployedRuntime v) ee g s0 (refUIDReadyPC site)
        (refUIDReadyStack site dummy word heap schema idx t3 t4 R) mem' aw' rdata σ' k' C') ∨
    (ExecBlock fork config {contract := contract,locals := L,immutables := immStore v} evm recordProcessBody .reverted ∧
      RDrev fork (deployedRuntime v) g s0) ∨
    (ExecBlock fork config {contract := contract,locals := L,immutables := immStore v} evm recordProcessBody .staticViolation ∧
      RDstatic fork (deployedRuntime v) g s0) := by
  dsimp only
  let a := newAttestation r schema (easTimeWord ee) attester
  let next := allocateNext heap.toNat 320
  have hnew := newRecordRun v site (by omega) hs hr hsch ha hh hd hv hlo hmem hrend hdend hat hheap rd
  dsimp only at hnew
  by_cases hg : allocateNext heap.toNat 320 ≤ 2^64-1 ∧ heap.toNat ≤ allocateNext heap.toNat 320
  · rw [if_pos hg] at hnew
    obtain ⟨m1,aw1,k1,C1,hs1,hf1,hp1,hpad1,hv1,hh1,rd1⟩ := hnew
    have hn : (UInt256.ofNat next).toNat = next := ulit_toNat' _ (by change next < 2^256; dsimp only [next]; omega)
    have hnext : next = heap.toNat+320 := (allocate320_bounds hg).1
    have hnb : next < UInt256.size := by change next < 2^256; dsimp only [next]; omega
    have hloop := uidLoopRun (heap := UInt256.ofNat next) v site
      (by simp only [List.length_cons]; omega) (by simpa only [hn] using hf1) hs hv1
      (by rw [hn]; exact hg.1) hh1 (by rw [hn,hnext]) (by rw [hn,hnext]; exact le_trans hdend (by omega)) (by decide) rd1
    rcases hloop with ⟨L2,m2,aw2,k2,C2,heap2,word,bump,hlo2,hhi2,hp2,hh2,hkeep2,hf2,hu2,hz2,hs2,rd2⟩ | ⟨hs2,hr2⟩
    · rw [hn] at hlo2 hp2
      have hv2 := hv1.preserve hp2 (by rw [hnext]) (by rw [hnext]; exact le_trans hdend (by omega)) hnb
      have hs12 := execBlock_append hs1 (ExecBlock.consNormal hs2 ExecBlock.nil)
      have hk12 := (newRecordLocals_keep L r schema (easTimeWord ee) attester heap.toNat).trans hkeep2.recordProcess
      have hp12 := hp1.trans (hp2.mono (by rw [hnext]; omega))
      have hstore := recordStoreRun v site (by omega) hs hf2.attestation hu2 hf2.db hv2 hlen hdend (by rw [← hnext]; exact hnb) rd2
      rcases hstore with ⟨e3,σ3,m3,aw3,k3,C3,hperm,hs3,hstate3,hp3,hv3,hh3,rd3⟩ | ⟨hs3,hr3⟩ | ⟨hs3,hr3⟩
      · have hk3 := hk12.trans (recordScalarLocals_keep L2 a word)
        have hp123 := hp12.trans hp3
        have hvreq3 := hv.preserve hp123 hrend hdend heap.val.isLt
        have hhlocal3 : (recordScalarLocals L2 a word).get? "$EAS.freeMemory" = some (.int (Int.ofNat heap2)) :=
          (recordScalarLocals_get _ _ _ _ (by decide)).trans hf2.heap
        have href := refUIDRun v site (by omega) hstate3 (by have := hp123.size; omega)
          ((hk3 "request" (by decide)).trans hr) hhlocal3 hvreq3.refUID rd3
        have hs123 := execBlock_append hs12 hs3
        split at href
        · obtain ⟨m4,dummy,aw4,k4,C4,hp4,hh4,hs4,rd4⟩ := href
          let L4 := refUIDLocals (recordScalarLocals L2 a word) r.refUID (dbUIDWord e3 r.refUID) heap2
          refine Or.inl ⟨L4,e3,σ3,m4,dummy,aw4,k4,C4,heap2,word,hperm,?_,hhi2,
            hk3.trans (refUIDLocals_keep _ _ _ _),?_,?_,refUIDLocals_heap hhlocal3,
            execBlock_append hs123 (ExecBlock.consNormal hs4 ExecBlock.nil),hstate3,
            hp123.trans (hp4 _),
            ((hpad1.trans (hp2.mono (by rw [hnext]; omega))).trans hp3).trans (hp4 _),?_,hh4.trans (hh3.trans hh2),rd4⟩
          · rw [← hnext]; exact hlo2
          · exact (refUIDLocals_get _ _ _ _ _ (by decide) (by decide) (by decide)).trans
              (recordScalarLocals_attestation L2 a word)
          · exact (refUIDLocals_get _ _ _ _ _ (by decide) (by decide) (by decide)).trans
              ((recordScalarLocals_get _ _ _ _ (by decide)).trans hu2)
          · exact hv3.preserve (hp4 (heap.toNat+320)) (le_refl _) (by change dataPtr.toNat+32+32*((r.data.size+31)/32) ≤ heap.toNat+320; omega)
              (by rw [← hnext]; exact hnb)
        · exact Or.inr (Or.inl ⟨execBlock_append hs123 (ExecBlock.consRevert href.1),href.2⟩)
      · exact Or.inr (Or.inl ⟨execBlock_append_term (execBlock_append hs12 hs3) (by intros; exact nofun),hr3⟩)
      · exact Or.inr (Or.inr ⟨execBlock_append_term (execBlock_append hs12 hs3) (by intros; exact nofun),hr3⟩)
    · have hsol := execBlock_append hs1 (ExecBlock.consRevert (stmts := []) hs2)
      exact Or.inr (Or.inl ⟨execBlock_append_term (execBlock_append_term hsol (s2 := recordStoreBody) (by intros; exact nofun))
        (by intros; exact nofun),hr2⟩)
  · rw [if_neg hg] at hnew
    exact Or.inr (Or.inl ⟨execBlock_append_term (execBlock_append_term
      (execBlock_append_term hnew.1 (s2 := [.while (.boolLit true) uidIteration]) (by intros; exact nofun))
      (s2 := recordStoreBody) (by intros; exact nofun)) (by intros; exact nofun),hnew.2⟩)

end Benchmarks.EAS.EAS
