import Benchmarks.EAS.EAS.RecordWriteFields
import Benchmarks.EAS.EAS.RecordScalarSource
import Benchmarks.EAS.EAS.RecordWriteStatic

variable {fork : Ethereum.Fork}
open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables Benchmarks.EAS.EAS.Immutables
namespace Benchmarks.EAS.EAS

theorem easRecordScalarWrites {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : Nat}
    {src dataPtr word bump t1 t2 t3 t4 : UInt256} {a : AttestationRecord} {R : List UInt256}
    (v : EASImmutables) (site : UIDSite) (hstack : R.length+22 ≤ 1024) (hperm : ee.perm = true)
    (hview : AttestationMemoryView mem src dataPtr a) (hlen : a.data.size < 2^64)
    (hdata : dataPtr.toNat+32+32*((a.data.size+31)/32) ≤ src.toNat) (hb : src.toNat+320 < UInt256.size)
    (rd : RD fork (deployedRuntime v) ee g s0 (uidAvailablePC site)
      (word::bump::uidSaved site src (t1::t2::t3::t4::R)) mem aw rdata σ k C) :
    ∃ aw' k' C', RD fork (deployedRuntime v) ee g s0 (recordBytesPC site)
      (recordBytesStack site (dbSlot word) word src dataPtr (UInt256.ofNat a.data.size) t1 t2 t3 t4 R)
      (recordStoreMemory mem src word) aw' rdata (attestationWriteAccounts σ ee (dbSlot word) {a with uid := word}) k' C' := by
  obtain ⟨aw1,k1,C1,hr1⟩ := easRecordWriteStart v site (by omega) hperm hview hdata hb rd
  have hv := recordStoreMemory_view hview word hdata hb
  obtain ⟨aw2,k2,C2,hr2⟩ := easRecordWriteTimes v site hstack hperm hv hr1
  obtain ⟨aw3,k3,C3,hr3⟩ := easRecordWriteFields v site hstack hperm hv hlen hr2
  exact ⟨aw3,k3,C3,hr3⟩

theorem recordScalarRun {L : Store} {evm : EVM.State} {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : Nat}
    {src dataPtr word bump t1 t2 t3 t4 : UInt256} {a : AttestationRecord} {R : List UInt256}
    (v : EASImmutables) (site : UIDSite) (hstack : R.length+22 ≤ 1024)
    (hs : SourceState s0 ee σ evm)
    (ha : L.get? "attestation" = some a.value) (hu : L.get? "uid" = some (wordBytes32Value word))
    (hd : L.get? "_db" = none) (hview : AttestationMemoryView mem src dataPtr a) (hlen : a.data.size < 2^64)
    (hdata : dataPtr.toNat+32+32*((a.data.size+31)/32) ≤ src.toNat) (hb : src.toNat+320 < UInt256.size)
    (rd : RD fork (deployedRuntime v) ee g s0 (uidAvailablePC site)
      (word::bump::uidSaved site src (t1::t2::t3::t4::R)) mem aw rdata σ k C) :
    (∃ aw' k' C',
      ExecBlock fork config {contract := contract,locals := L,immutables := immStore v} evm recordScalarBody
        (.ok {contract := contract,locals := recordScalarLocals L a word,immutables := immStore v}
          (attestationWriteHead evm (dbSlot word) {a with uid := word})) ∧
      SourceState s0 ee (attestationWriteAccounts σ ee (dbSlot word) {a with uid := word})
        (attestationWriteHead evm (dbSlot word) {a with uid := word}) ∧
      RD fork (deployedRuntime v) ee g s0 (recordBytesPC site)
        (recordBytesStack site (dbSlot word) word src dataPtr (UInt256.ofNat a.data.size) t1 t2 t3 t4 R)
        (recordStoreMemory mem src word) aw' rdata
        (attestationWriteAccounts σ ee (dbSlot word) {a with uid := word}) k' C') ∨
    (ExecBlock fork config {contract := contract,locals := L,immutables := immStore v} evm recordScalarBody .staticViolation ∧
      RDstatic fork (deployedRuntime v) g s0) := by
  cases hp : ee.perm with
  | false =>
    exact Or.inr ⟨recordScalarSource_static ha hu hd (by rw [hs.env]; exact hp),
      easRecordWriteStatic v site (by omega) hp rd⟩
  | true =>
    obtain ⟨aw',k',C',hr⟩ := easRecordScalarWrites v site hstack hp hview hlen hdata hb rd
    exact Or.inl ⟨aw',k',C',recordScalarSource (hperm := by simpa only [hs.env] using hp) ha hu hd,attestationWriteHead_sourceState hs _ _,hr⟩

end Benchmarks.EAS.EAS
