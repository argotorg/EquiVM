import Benchmarks.EAS.EAS.BytesWriteRun
import Benchmarks.EAS.EAS.RecordDataSource
import Benchmarks.EAS.EAS.BytesWriteState

variable {fork : Ethereum.Fork}
open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables Benchmarks.EAS.EAS.Immutables
namespace Benchmarks.EAS.EAS

theorem recordDataRun {L : Store} {evm : EVM.State} {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : Nat}
    {src dataPtr word t1 t2 t3 t4 : UInt256} {a : AttestationRecord} {R : List UInt256}
    (v : EASImmutables) (site : UIDSite) (hstack : R.length+25 ≤ 1024) (hp : ee.perm = true)
    (hs : SourceState s0 ee σ evm)
    (ha : L.get? "attestation" = some a.value) (hu : L.get? "uid" = some (wordBytes32Value word))
    (hd : L.get? "_db" = none) (hview : AttestationMemoryView mem src dataPtr a) (hlen : a.data.size < 2^64)
    (hb : dataPtr.toNat+a.data.size+64 < UInt256.size)
    (rd : RD fork (deployedRuntime v) ee g s0 (recordBytesPC site)
      (recordBytesStack site (dbSlot word) word src dataPtr (UInt256.ofNat a.data.size) t1 t2 t3 t4 R)
      mem aw rdata σ k C) :
    if storedBytesValid (attestationHeader evm word) then
      ∃ mem' aw' k' C', (∀ limit, MemoryPrefix mem mem' limit) ∧
        memLoad (UInt256.ofNat 64) mem' = memLoad (UInt256.ofNat 64) mem ∧
        ExecStmt fork config {contract := contract,locals := L,immutables := immStore v} evm (attestationWriteStmt "data")
          (.ok {contract := contract,locals := L,immutables := immStore v}
            (bytesWriteState evm (dbSlot word+⟨6⟩) a.data (storedBytesLengthWord (attestationHeader evm word)).toNat)) ∧
        SourceState s0 ee (bytesWriteAccounts σ ee (dbSlot word+⟨6⟩) a.data (storedBytesLengthWord (attestationHeader evm word)).toNat)
          (bytesWriteState evm (dbSlot word+⟨6⟩) a.data (storedBytesLengthWord (attestationHeader evm word)).toNat) ∧
        RD fork (deployedRuntime v) ee g s0 (bytesWrittenPC site)
          (bytesWriteSaved site word src t1 t2 t3 t4 R) mem' aw' rdata
          (bytesWriteAccounts σ ee (dbSlot word+⟨6⟩) a.data (storedBytesLengthWord (attestationHeader evm word)).toNat) k' C'
    else ExecStmt fork config {contract := contract,locals := L,immutables := immStore v} evm (attestationWriteStmt "data") .reverted ∧
      RDrev fork (deployedRuntime v) g s0 := by
  have hh : attestationHeader evm word = solcSlotWord σ ee (dbSlot word+⟨6⟩) := hs.storageRead _
  have hsol := recordDataSource (fork := fork) (hperm := by simpa only [hs.env] using hp) (imms := immStore v) (evm := evm) hd hu ha
  have hevm := easRecordBytesDecode v site (by omega) rd
  rw [← hh] at hevm
  by_cases hv : storedBytesValid (attestationHeader evm word)
  · rw [if_pos hv] at hsol hevm ⊢
    obtain ⟨aw1,k1,C1,hr1⟩ := hevm
    obtain ⟨mem',aw',k',C',hpre,hfree,hr⟩ := easBytesWrite v site hstack hp hview.dataLow hlen
      (storedBytesLength_bound _) hb hview.dataCovered hview.payload hr1
    exact ⟨mem',aw',k',C',hpre,hfree,hsol,sourceState_bytesWrite hs _ _ _,hr⟩
  · rw [if_neg hv] at hsol hevm ⊢
    exact ⟨hsol,hevm⟩

end Benchmarks.EAS.EAS
