import Benchmarks.EAS.EAS.RecordDataRun
import Benchmarks.EAS.EAS.RecordScalarRun

variable {fork : Ethereum.Fork}
open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables Benchmarks.EAS.EAS.Immutables
namespace Benchmarks.EAS.EAS

def recordStoreBody : Body := recordScalarBody ++ [attestationWriteStmt "data"]

theorem recordStoreRun {L : Store} {evm : EVM.State} {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : Nat}
    {src dataPtr word bump t1 t2 t3 t4 : UInt256} {a : AttestationRecord} {R : List UInt256}
    (v : EASImmutables) (site : UIDSite) (hstack : R.length+25 ≤ 1024)
    (hs : SourceState s0 ee σ evm)
    (ha : L.get? "attestation" = some a.value) (hu : L.get? "uid" = some (wordBytes32Value word))
    (hd : L.get? "_db" = none) (hview : AttestationMemoryView mem src dataPtr a) (hlen : a.data.size < 2^64)
    (hdata : dataPtr.toNat+32+32*((a.data.size+31)/32) ≤ src.toNat) (hb : src.toNat+320 < UInt256.size)
    (rd : RD fork (deployedRuntime v) ee g s0 (uidAvailablePC site)
      (word::bump::uidSaved site src (t1::t2::t3::t4::R)) mem aw rdata σ k C) :
    (∃ evm' σ' mem' aw' k' C', ee.perm = true ∧
      ExecBlock fork config {contract := contract,locals := L,immutables := immStore v} evm recordStoreBody
        (.ok {contract := contract,locals := recordScalarLocals L a word,immutables := immStore v} evm') ∧
      SourceState s0 ee σ' evm' ∧ MemoryPrefix mem mem' src.toNat ∧
      AttestationMemoryView mem' src dataPtr {a with uid := word} ∧
      memLoad (UInt256.ofNat 64) mem' = memLoad (UInt256.ofNat 64) mem ∧
      RD fork (deployedRuntime v) ee g s0 (bytesWrittenPC site)
        (bytesWriteSaved site word src t1 t2 t3 t4 R) mem' aw' rdata σ' k' C') ∨
    (ExecBlock fork config {contract := contract,locals := L,immutables := immStore v} evm recordStoreBody .reverted ∧
      RDrev fork (deployedRuntime v) g s0) ∨
    (ExecBlock fork config {contract := contract,locals := L,immutables := immStore v} evm recordStoreBody .staticViolation ∧
      RDstatic fork (deployedRuntime v) g s0) := by
  cases hp : ee.perm with
  | false =>
    refine Or.inr (Or.inr ⟨?_,easRecordWriteStatic v site (by omega) hp rd⟩)
    exact execBlock_append_term (recordScalarSource_static ha hu hd (by rw [hs.env]; exact hp)) (by intros; exact nofun)
  | true =>
    obtain ⟨aw1,k1,C1,hr1⟩ := easRecordScalarWrites v site (by omega) hp hview hlen hdata hb rd
    have hs1 := attestationWriteHead_sourceState hs (dbSlot word) {a with uid := word}
    have hsol1 := recordScalarSource (fork := fork) (hperm := by simpa only [hs.env] using hp) (imms := immStore v) (evm := evm) ha hu hd
    have hv1 := recordStoreMemory_view hview word hdata hb
    have hr := recordDataRun v site hstack hp hs1 (recordScalarLocals_attestation L a word)
      ((recordScalarLocals_get L a word "uid" (by decide)).trans hu)
      ((recordScalarLocals_get L a word "_db" (by decide)).trans hd) hv1 hlen (by change dataPtr.toNat+a.data.size+64 < UInt256.size; omega) hr1
    split at hr
    · obtain ⟨mem',aw',k',C',hpre,hfree,hsol2,hs2,hr2⟩ := hr
      refine Or.inl ⟨_,_,mem',aw',k',C',rfl,execBlock_append hsol1 (ExecBlock.consNormal hsol2 ExecBlock.nil),hs2,
        (recordStoreMemory_prefix mem src word).trans (hpre src.toNat),?_,?_,hr2⟩
      · exact hv1.preserve (hpre (src.toNat+320)) (le_refl _)
          (by change dataPtr.toNat+32+32*((a.data.size+31)/32) ≤ src.toNat+320; omega) hb
      · exact hfree.trans (recordStoreMemory_heap mem src word (memLoad (UInt256.ofNat 64) mem)
          hview.sourceLow (by have := hview.sourceCovered; have := hview.sourceLow; omega) rfl)
    · exact Or.inr (Or.inl ⟨execBlock_append hsol1 (ExecBlock.consRevert hr.1),hr.2⟩)

end Benchmarks.EAS.EAS
