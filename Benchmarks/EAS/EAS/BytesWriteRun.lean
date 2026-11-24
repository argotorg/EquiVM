import Benchmarks.EAS.EAS.BytesLongRun
import Benchmarks.EAS.EAS.BytesShortMemory
import Benchmarks.EAS.EAS.BytesCleanRun

variable {fork : Ethereum.Fork}
open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables Benchmarks.EAS.EAS.Immutables
namespace Benchmarks.EAS.EAS

theorem easBytesWrite {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : Nat}
    {ptr slot old word src t1 t2 t3 t4 : UInt256} {bytes : ByteArray} {R : List UInt256}
    (v : EASImmutables) (site : UIDSite) (hstack : R.length+25 ≤ 1024) (hp : ee.perm = true)
    (hlo : 96 ≤ ptr.toNat) (hlen : bytes.size < 2^64) (hold : old.toNat < 2^255)
    (hb : ptr.toNat+bytes.size+64 < UInt256.size)
    (hin : ptr.toNat+32+32*((bytes.size+31)/32) ≤ mem.size)
    (hread : mem.readWithPadding (ptr.toNat+32) bytes.size = bytes)
    (rd : RD fork (deployedRuntime v) ee g s0 (recordBytesDecodedPC site)
      (old::ptr::UInt256.ofNat bytes.size::slot::recordBytesSaved site word src t1 t2 t3 t4 R)
      mem aw rdata σ k C) :
    ∃ mem' aw' k' C', (∀ limit, MemoryPrefix mem mem' limit) ∧
      memLoad (UInt256.ofNat 64) mem' = memLoad (UInt256.ofNat 64) mem ∧
      RD fork (deployedRuntime v) ee g s0 (bytesWrittenPC site)
        (bytesWriteSaved site word src t1 t2 t3 t4 R) mem' aw' rdata
        (bytesWriteAccounts σ ee (slot+⟨6⟩) bytes old.toNat) k' C' := by
  have hsz : (UInt256.ofNat bytes.size).toNat = bytes.size := ulit_toNat' _ (by omega)
  obtain ⟨mem1,aw1,k1,C1,hm1,hr1⟩ := easBytesClean v site (by omega) hp hold (by rw [hsz]; omega) rd
  have hpfx1 (limit : Nat) : MemoryPrefix mem mem1 limit := by
    rcases hm1 with he | he
    · rw [he]; exact MemoryPrefix.refl _ _
    · rw [he]; exact memoryPrefix_sparse_writeWord _ _ _ _ (Or.inr (by decide))
  have hf1 : memLoad (UInt256.ofNat 64) mem1 = memLoad (UInt256.ofNat 64) mem := by
    rcases hm1 with he | he
    · rw [he]
    · rw [he]; exact memLoad_write_above _ _ _ _ (by decide) (by change 96 ≤ mem.size; omega)
  have hcov1 : ptr.toNat+32+32*((bytes.size+31)/32) ≤ mem1.size := le_trans hin (hpfx1 0).size
  have hread1 : mem1.readWithPadding (ptr.toNat+32) bytes.size = bytes :=
    (memoryPrefix_read_prefix (hpfx1 (ptr.toNat+32+32*((bytes.size+31)/32)))
      (ptr.toNat+32) ((bytes.size+31)/32) bytes.size (by omega) (by omega) hin (by omega) (by omega)).trans hread
  obtain ⟨aw2,k2,C2,hr2⟩ := easBytesWriteDispatch v site (by omega) hr1
  simp only [hsz] at hr2
  by_cases hshort : bytes.size<32
  · rw [if_pos hshort] at hr2
    obtain ⟨aw3,k3,C3,hr3⟩ := easBytesShortWrite v site
      (by cases site <;> simp only [bytesWriteSaved,recordBytesSaved,List.length_cons] <;> omega) hp hr2
    rw [bytesShortMemoryWord hshort (by omega) (by intro hz; omega) hread1] at hr3
    refine ⟨mem1,aw3,k3,C3,hpfx1,hf1,?_⟩
    simpa only [bytesWriteAccounts,if_pos hshort] using hr3
  · rw [if_neg hshort] at hr2
    obtain ⟨aw3,k3,C3,hr3⟩ := easBytesLongWrite v site hstack hp hlo hshort hlen hb hcov1 hread1 hr2
    refine ⟨Reasoning.Theory.writeWord mem1 0 (slot+⟨6⟩),aw3,k3,C3,?_,?_,?_⟩
    · intro limit
      exact (hpfx1 limit).trans (memoryPrefix_sparse_writeWord _ _ _ _ (Or.inr (by decide)))
    · exact (memLoad_write_above _ _ _ _ (by decide) (by change 96 ≤ mem1.size; omega)).trans hf1
    · simpa only [bytesWriteAccounts,if_neg hshort] using hr3

end Benchmarks.EAS.EAS
