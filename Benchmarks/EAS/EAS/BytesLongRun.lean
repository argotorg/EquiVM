import Benchmarks.EAS.EAS.BytesLongWord
import Benchmarks.EAS.EAS.BytesLongLoop
import Benchmarks.EAS.EAS.BytesPayloadWords

variable {fork : Ethereum.Fork}
open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables Benchmarks.EAS.EAS.Immutables
namespace Benchmarks.EAS.EAS

theorem easBytesLongWrite {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : Nat}
    {ptr slot word src t1 t2 t3 t4 : UInt256} {bytes : ByteArray} {R : List UInt256}
    (v : EASImmutables) (site : UIDSite) (hstack : R.length+25 ≤ 1024) (hp : ee.perm = true)
    (hlo : 96 ≤ ptr.toNat) (hlong : ¬bytes.size<32) (hlen : bytes.size < 2^64)
    (hb : ptr.toNat+bytes.size+64 < UInt256.size)
    (hin : ptr.toNat+32+32*((bytes.size+31)/32) ≤ mem.size)
    (hread : mem.readWithPadding (ptr.toNat+32) bytes.size = bytes)
    (rd : RD fork (deployedRuntime v) ee g s0 (bytesLongPC site)
      (ptr::UInt256.ofNat 32::UInt256.ofNat bytes.size::slot::bytesWriteSaved site word src t1 t2 t3 t4 R)
      mem aw rdata σ k C) :
    ∃ aw' k' C', RD fork (deployedRuntime v) ee g s0 (bytesWrittenPC site)
      (bytesWriteSaved site word src t1 t2 t3 t4 R) (Reasoning.Theory.writeWord mem 0 (slot+⟨6⟩)) aw' rdata
      (sstoreAccountMap ee.codeOwner
        (solidityDataWordsForwardFrom ee.codeOwner σ (slot+⟨6⟩) bytes 0 (solidityBytesDataWordCount bytes.size))
        (slot+⟨6⟩) (solidityBytesHeaderWord bytes.size)) k' C' := by
  let out := Reasoning.Theory.writeWord mem 0 (slot+⟨6⟩)
  have hpfx := memoryPrefix_sparse_writeWord mem 0 (ptr.toNat+32+32*((bytes.size+31)/32)) (slot+⟨6⟩) (Or.inr (by decide))
  have hr : out.readWithPadding (ptr.toNat+32) bytes.size = bytes :=
    (memoryPrefix_read_prefix hpfx (ptr.toNat+32) ((bytes.size+31)/32) bytes.size (by omega)
      (by omega) hin (by omega) (by omega)).trans hread
  have hcover : ptr.toNat+32+32*((bytes.size+31)/32) ≤ out.size := le_trans hin hpfx.size
  have hsz : (UInt256.ofNat bytes.size).toNat = bytes.size := ulit_toNat' _ (by omega)
  have haddr (i : Nat) (hi : i ≤ bytes.size/32) :
      UInt256.ofNat (32+32*i)+ptr = UInt256.ofNat (ptr.toNat+32+i*32) := by
    apply u256_inj
    rw [u256_add_comm,uadd_word_ofNat_toNat _ _ (by have := Nat.div_mul_le_self bytes.size 32; omega),
      ulit_toNat' _ (by have := Nat.div_mul_le_self bytes.size 32; omega)]
    omega
  have hwords (i : Nat) (hi : i < bytes.size/32) :
      memLoad (UInt256.ofNat (32+32*i)+ptr) out = uInt256OfByteArray (bytes.readWithPadding (i*32) 32) := by
    rw [haddr i (by omega)]
    exact payloadMemoryWord hr (by omega) (by omega) (by omega)
  obtain ⟨aw1,k1,C1,hr1⟩ := easBytesLongPrepare v site
    (by cases site <;> simp only [bytesWriteSaved,recordBytesSaved,List.length_cons] <;> omega) rd
  have hbase : solidityBytesDataSlot (slot+⟨6⟩) 0 = solidityBytesDataBaseSlot (slot+⟨6⟩) := uint256_add_zero_right _
  rw [← hbase] at hr1
  obtain ⟨aw2,k2,C2,hr2⟩ := easBytesLongLoop v site (by omega) hp (by omega) hwords 0 (bytes.size/32) (by omega) hr1
  obtain ⟨aw3,k3,C3,hr3⟩ := easBytesLongTail v site
    (by cases site <;> simp only [bytesWriteSaved,recordBytesSaved,List.length_cons] <;> omega) hp hr2
  rw [hsz,bytesLongHeader_eq _ (by rw [hsz]; exact hlong) (by rw [hsz]; unfold solcMaxU64; omega),hsz] at hr3
  by_cases hz : bytes.size%32=0
  · rw [if_pos hz] at hr3
    have hc : solidityBytesDataWordCount bytes.size = bytes.size/32 := nat_ceil32_eq_div_of_mod_zero hz
    exact ⟨aw3,k3,C3,by simpa only [hc] using hr3⟩
  · rw [if_neg hz] at hr3
    have hrem : bytes.size-bytes.size/32*32 = bytes.size%32 := by omega
    have htail : bytesLongTailEVMWord (memLoad (ptr+UInt256.ofNat (32+32*(bytes.size/32))) out)
        (UInt256.ofNat bytes.size) = uInt256OfByteArray (bytes.readWithPadding (bytes.size/32*32) 32) := by
      rw [bytesLongTailEVMWord,bytesLongTailMask,hsz,u256_add_comm ptr,haddr _ (le_refl _),← hrem]
      exact payloadMemoryTail hr (by omega) (by omega) (by omega) (by omega)
    rw [htail] at hr3
    have hc : solidityBytesDataWordCount bytes.size = bytes.size/32+1 := by unfold solidityBytesDataWordCount; omega
    rw [hc,solidityDataWordsForwardFrom_append,solidityDataWordsForwardFrom,Nat.zero_add,solidityDataWordsForwardFrom]
    exact ⟨aw3,k3,C3,hr3⟩

end Benchmarks.EAS.EAS
