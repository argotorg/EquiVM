import Benchmarks.EAS.EAS.RevocationCopyMemory

variable {fork : Ethereum.Fork}
open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables Benchmarks.EAS.EAS.Immutables
namespace Benchmarks.EAS.EAS
set_option maxRecDepth 10000

-- GENERALIZES wordStride32_next to any bounded byte stride.
theorem wordStride_next (base stride i : Nat) (hb : base+stride*(i+1) < UInt256.size) :
    UInt256.ofNat (base+stride*i)+UInt256.ofNat stride = UInt256.ofNat (base+stride*(i+1)) := by
  simp only [Nat.mul_add,Nat.mul_one] at hb ⊢
  apply u256_inj
  rw [uadd_word_ofNat_toNat _ _ (by rw [ulit_toNat' _ (by omega)]; omega),
    ulit_toNat' _ (by omega),ulit_toNat' _ hb]
  omega

theorem copyRevocationArrayLoopStrong {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : Nat}
    {offset array ret : UInt256} {rs : List RevocationRequestRecord} {i cursor : Nat} {R : List UInt256}
    (v : EASImmutables) (hstack : R.length+15 ≤ 1024)
    (hc : RevocationArrayCalldataView ee.calldata offset rs) (hsize : ee.calldata.size < 2^255)
    (hret : (D_J (deployedRuntime v) 0).contains ret = true)
    (n : Nat) (hn : i+n = rs.length)
    (hm : CopyRevocationArrayMemory mem array rs i cursor)
    (hh : cursor ≤ 2^64-1) (hfree : memLoad (UInt256.ofNat 64) mem = UInt256.ofNat cursor)
    (rd : RD fork (deployedRuntime v) ee g s0 ⟨5973⟩
      (UInt256.ofNat (array.toNat+32+32*i)::UInt256.ofNat ee.calldata.size::
        UInt256.ofNat (offset.toNat+64*rs.length)::UInt256.ofNat (offset.toNat+64*i)::ret::array::R) mem aw rdata σ k C) :
    if cursor+64*n ≤ 2^64-1 then
      ∃ mem' aw' k' C', MemoryPrefix mem mem' array.toNat ∧
        CopyRevocationArrayMemory mem' array rs rs.length (cursor+64*n) ∧
        memLoad (UInt256.ofNat 64) mem' = UInt256.ofNat (cursor+64*n) ∧
        RD fork (deployedRuntime v) ee g s0 ret (array::R) mem' aw' rdata σ k' C'
    else RDrev fork (deployedRuntime v) g s0 := by
  induction n generalizing i cursor mem aw k C with
  | zero =>
    have hi : i = rs.length := by omega
    subst i
    simp only [Nat.mul_zero,Nat.add_zero,if_pos hh]
    obtain ⟨a1,k1,C1,r1⟩ := easCopyRevocationArrayDone v (by omega) hret rd
    exact ⟨mem,a1,k1,C1,MemoryPrefix.refl _ _,hm,hfree,r1⟩
  | succ n ih =>
    have hi : i < rs.length := by omega
    have hcb := hc.extent
    have hspan := hm.span
    have hcur : (UInt256.ofNat cursor).toNat = cursor := ulit_toNat' _ (by change cursor < 2^256; omega)
    have hsrc : (UInt256.ofNat (offset.toNat+64*i)).toNat = offset.toNat+64*i :=
      ulit_toNat' _ (by change _ < 2^256; omega)
    have hend : (UInt256.ofNat (offset.toNat+64*rs.length)).toNat = offset.toNat+64*rs.length :=
      ulit_toNat' _ (by change _ < 2^256; omega)
    have hrun := easCopyRevocationArrayStep v (by simp only [List.length_cons]; omega)
      (by rw [hsrc,hend]; omega) (by rw [hsrc]; omega) hsize (by rw [hcur]; exact hh) hfree rd
    rw [hcur] at hrun
    by_cases hg : cursor+64 ≤ 2^64-1
    · rw [if_pos hg] at hrun
      obtain ⟨a1,k1,C1,r1⟩ := hrun
      let m1 := revocationArrayCopyMemory mem ee.calldata (UInt256.ofNat (offset.toNat+64*i))
        (UInt256.ofNat (array.toNat+32+32*i)) (UInt256.ofNat cursor)
      have hm0 : CopyRevocationArrayMemory mem array rs i (UInt256.ofNat cursor).toNat := by rw [hcur]; exact hm
      have hmem := revocationArrayCopyMemory_step hm0 hi (by rw [hcur]; change cursor+64 < 2^256; omega)
        (by rw [hsrc]; change offset.toNat+64*i+32 < 2^256; omega)
        (by rw [hsrc]; exact hc.requests i hi)
      simp only [hcur] at hmem
      rw [wordStride_next (array.toNat+32) 32 i (by change _ < 2^256; omega),
        wordStride_next offset.toNat 64 i (by change _ < 2^256; omega)] at r1
      have hnext := ih (i := i+1) (cursor := cursor+64) (by omega) hmem.2.1 hg hmem.2.2 r1
      have heq : cursor+64+64*n = cursor+64*(n+1) := by omega
      rw [heq] at hnext
      by_cases hall : cursor+64*(n+1) ≤ 2^64-1
      · rw [if_pos hall] at hnext ⊢
        obtain ⟨m2,a2,k2,C2,hp2,hv2,hf2,r2⟩ := hnext
        exact ⟨m2,a2,k2,C2,hmem.1.trans hp2,hv2,hf2,r2⟩
      · rw [if_neg hall] at hnext ⊢
        exact hnext
    · rw [if_neg hg] at hrun
      rw [if_neg (by omega : ¬ cursor+64*(n+1) ≤ 2^64-1)]
      exact hrun

theorem copyRevocationArrayLoop {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : Nat}
    {offset array ret : UInt256} {rs : List RevocationRequestRecord} {i cursor : Nat} {R : List UInt256}
    (v : EASImmutables) (hstack : R.length+15 ≤ 1024)
    (hc : RevocationArrayCalldataView ee.calldata offset rs) (hsize : ee.calldata.size < 2^255)
    (hret : (D_J (deployedRuntime v) 0).contains ret = true)
    (n : Nat) (hn : i+n = rs.length)
    (hm : CopyRevocationArrayMemory mem array rs i cursor)
    (hh : cursor ≤ 2^64-1) (hfree : memLoad (UInt256.ofNat 64) mem = UInt256.ofNat cursor)
    (rd : RD fork (deployedRuntime v) ee g s0 ⟨5973⟩
      (UInt256.ofNat (array.toNat+32+32*i)::UInt256.ofNat ee.calldata.size::
        UInt256.ofNat (offset.toNat+64*rs.length)::UInt256.ofNat (offset.toNat+64*i)::ret::array::R) mem aw rdata σ k C) :
    if cursor+64*n ≤ 2^64-1 then
      ∃ mem' aw' k' C', MemoryPrefix mem mem' array.toNat ∧
        RevocationRequestArrayMemoryView mem' array rs (cursor+64*n) ∧
        memLoad (UInt256.ofNat 64) mem' = UInt256.ofNat (cursor+64*n) ∧
        RD fork (deployedRuntime v) ee g s0 ret (array::R) mem' aw' rdata σ k' C'
    else RDrev fork (deployedRuntime v) g s0 := by
  have h := copyRevocationArrayLoopStrong v hstack hc hsize hret n hn hm hh hfree rd
  by_cases hg : cursor+64*n ≤ 2^64-1
  · rw [if_pos hg] at h ⊢
    obtain ⟨m,a,j,D,hp,hv,hf,hr⟩ := h
    exact ⟨m,a,j,D,hp,hv.finish,hf,hr⟩
  · simpa only [if_neg hg] using h

end Benchmarks.EAS.EAS
