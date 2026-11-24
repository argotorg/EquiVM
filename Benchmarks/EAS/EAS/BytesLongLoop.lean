import Benchmarks.EAS.EAS.BytesLongControl

variable {fork : Ethereum.Fork}
open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables Benchmarks.EAS.EAS.Immutables
namespace Benchmarks.EAS.EAS

theorem easBytesLongLoop {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : Nat}
    {ptr slot word src t1 t2 t3 t4 : UInt256} {bytes : ByteArray} {R : List UInt256}
    (v : EASImmutables) (site : UIDSite) (hstack : R.length+24 ≤ 1024) (hp : ee.perm = true)
    (hlen : bytes.size+64 < UInt256.size)
    (hwords : ∀ i, i < bytes.size/32 → memLoad (UInt256.ofNat (32+32*i)+ptr) mem =
      uInt256OfByteArray (bytes.readWithPadding (i*32) 32))
    (idx fuel : Nat) (hcount : idx+fuel = bytes.size/32)
    (rd : RD fork (deployedRuntime v) ee g s0 (bytesLongLoopPC site)
      (UInt256.ofNat (32*idx)::ptr::UInt256.ofNat (32+32*idx)::solidityBytesDataSlot (slot+⟨6⟩) idx::
        UInt256.ofNat bytes.size::slot::bytesWriteSaved site word src t1 t2 t3 t4 R) mem aw rdata σ k C) :
    ∃ aw' k' C', RD fork (deployedRuntime v) ee g s0 (bytesLongTailPC site)
      (UInt256.ofNat (32*(bytes.size/32))::ptr::UInt256.ofNat (32+32*(bytes.size/32))::
        solidityBytesDataSlot (slot+⟨6⟩) (bytes.size/32)::UInt256.ofNat bytes.size::slot::
        bytesWriteSaved site word src t1 t2 t3 t4 R) mem aw' rdata
      (solidityDataWordsForwardFrom ee.codeOwner σ (slot+⟨6⟩) bytes idx fuel) k' C' := by
  have hdiv := Nat.div_mul_le_self bytes.size 32
  have hcut : (UInt256.land (UInt256.ofNat bytes.size) (UInt256.ofNat (2^256-32))).toNat = 32*(bytes.size/32) := by
    change (UInt256.land (UInt256.ofNat bytes.size) (UInt256.lnot ⟨31⟩)).toNat = _
    rw [longDataCutoff_toNat,ulit_toNat' _ (by omega),Nat.mul_comm]
  induction fuel generalizing idx aw σ k C with
  | zero =>
    have hi : idx = bytes.size/32 := by omega
    subst idx
    exact easBytesLongDone v site
      (by cases site <;> simp only [bytesWriteSaved,recordBytesSaved,List.length_cons] <;> omega)
      (ult_zero (by rw [hcut,ulit_toNat' _ (by omega)])) rd
  | succ fuel ih =>
    have hidx : idx < bytes.size/32 := by omega
    have hib : 32*idx < UInt256.size := by omega
    have hc : UInt256.lt (UInt256.ofNat (32*idx)) (UInt256.land (UInt256.ofNat bytes.size) (UInt256.ofNat (2^256-32))) ≠ ⟨0⟩ := by
      rw [ult_one (by rw [ulit_toNat' _ hib,hcut]; omega)]
      decide
    obtain ⟨aw1,k1,C1,hr⟩ := easBytesLongStep v site hstack hp hc rd
    have hi : UInt256.ofNat 32+UInt256.ofNat (32*idx) = UInt256.ofNat (32*(idx+1)) := by
      have h := u256_32_add_ofNat (32*idx)
      convert h using 1
    have hj : UInt256.ofNat 32+UInt256.ofNat (32+32*idx) = UInt256.ofNat (32+32*(idx+1)) := by
      have h := u256_32_add_ofNat (32+32*idx)
      convert h using 1
    have hs : solidityBytesDataSlot (slot+⟨6⟩) idx+UInt256.ofNat 1 = solidityBytesDataSlot (slot+⟨6⟩) (idx+1) :=
      solidityBytesDataSlot_succ _ _
    rw [hi,hj,hs,hwords idx hidx] at hr
    have hr' := ih (idx+1) (by omega) hr
    simpa only [solidityDataWordsForwardFrom] using hr'

end Benchmarks.EAS.EAS
