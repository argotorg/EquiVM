import Benchmarks.EAS.EAS.CopySignatureArrayControl
import Benchmarks.EAS.EAS.CopyRevocationArrayLoop
import Benchmarks.EAS.EAS.SignatureArrayDecode

variable {fork : Ethereum.Fork}
open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables Benchmarks.EAS.EAS.Immutables
namespace Benchmarks.EAS.EAS
set_option maxRecDepth 10000

theorem signatureListClean_iff (ss : List SignatureRecord) :
    (∀ s∈ss,signatureClean s) ↔ ∀ i (hi : i<ss.length),signatureClean ss[i] := by
  constructor
  · intro h i hi
    exact h _ (List.getElem_mem hi)
  · intro h s hs
    obtain ⟨i,hi,he⟩ := List.getElem_of_mem hs
    rw [← he]
    exact h i hi

theorem copySignatureArrayLoop {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : Nat}
    {offset array : UInt256} {ss : List SignatureRecord} {i cursor : Nat} {R : List UInt256}
    (v : EASImmutables) (hstack : R.length+15 ≤ 1024)
    (he : offset.toNat+96*ss.length ≤ ee.calldata.size)
    (hc : ∀ j (hj : j<ss.length),signatureRecord ee.calldata (offset.toNat+96*j) = ss[j])
    (hsize : ee.calldata.size < 2^255)
    (n : Nat) (hn : i+n = ss.length)
    (hm : CopySignatureArrayMemory mem array ss i cursor)
    (hbefore : ∀ j (hj : j<ss.length),j < i → signatureClean ss[j])
    (hh : cursor ≤ 2^64-1) (hfree : memLoad (UInt256.ofNat 64) mem = UInt256.ofNat cursor)
    (rd : RD fork (deployedRuntime v) ee g s0 ⟨1492⟩
      (UInt256.ofNat (array.toNat+32+32*i)::UInt256.ofNat (offset.toNat+96*i)::UInt256.ofNat (offset.toNat+96*ss.length)::R)
        mem aw rdata σ k C) :
    if (∀ s∈ss,signatureClean s) ∧ cursor+96*n ≤ 2^64-1 then
      ∃ mem' aw' k' C', MemoryPrefix mem mem' array.toNat ∧
        CopySignatureArrayMemory mem' array ss ss.length (cursor+96*n) ∧
        memLoad (UInt256.ofNat 64) mem' = UInt256.ofNat (cursor+96*n) ∧
        RD fork (deployedRuntime v) ee g s0 ⟨1500⟩
          (UInt256.ofNat (array.toNat+32+32*ss.length)::UInt256.ofNat (offset.toNat+96*ss.length)::UInt256.ofNat (offset.toNat+96*ss.length)::R)
          mem' aw' rdata σ k' C'
    else RDrev fork (deployedRuntime v) g s0 := by
  induction n generalizing i cursor mem aw k C with
  | zero =>
    have hi : i=ss.length := by omega
    subst i
    have hall : ∀ s∈ss,signatureClean s := (signatureListClean_iff ss).mpr (fun j hj => hbefore j hj hj)
    simp only [Nat.mul_zero,Nat.add_zero]
    rw [if_pos (show (∀ s∈ss,signatureClean s) ∧ cursor ≤ 2^64-1 from ⟨hall,hh⟩)]
    obtain ⟨a1,j1,D1,r1⟩ := easCopySignatureArrayDone v (by omega) rd
    exact ⟨mem,a1,j1,D1,MemoryPrefix.refl _ _,hm,hfree,r1⟩
  | succ n ih =>
    have hi : i<ss.length := by omega
    have hspan := hm.span
    have hcur : (UInt256.ofNat cursor).toNat = cursor := ulit_toNat' _ (by change cursor<2^256; omega)
    have hsrc : (UInt256.ofNat (offset.toNat+96*i)).toNat = offset.toNat+96*i := ulit_toNat' _ (by change _<2^256; omega)
    have hend : (UInt256.ofNat (offset.toNat+96*ss.length)).toNat = offset.toNat+96*ss.length := ulit_toNat' _ (by change _<2^256; omega)
    have hsig : signatureAt ee.calldata (UInt256.ofNat (offset.toNat+96*i)) = ss[i] := by
      rw [signatureAt_eq_record _ _ (by rw [hsrc]; change _<2^256; omega),hsrc]
      exact hc i hi
    have hhead : UInt256.slt (UInt256.sub (UInt256.ofNat ee.calldata.size) (UInt256.ofNat (offset.toNat+96*i))) ⟨96⟩ = ⟨0⟩ :=
      solcDecodeLenCheckOk (head := UInt256.ofNat (offset.toNat+96*i)) (need := ⟨96⟩)
        (by rw [hsrc]; change offset.toNat+96*i+96 ≤ ee.calldata.size; omega)
        (by omega) (by change ee.calldata.size<2^256; omega) (by decide)
    have hrun := easCopySignatureArrayStep v hstack (by rw [hsrc,hend]; omega) (by rw [hcur]; exact hh) hfree rd
    simp only [signatureAtValid,hsig,hhead,true_and,hcur] at hrun
    by_cases hg : signatureClean ss[i] ∧ cursor+96 ≤ 2^64-1
    · obtain ⟨a1,j1,D1,r1⟩ := hrun.1 hg
      let m1 := signatureArrayCopyMemory mem (UInt256.ofNat (array.toNat+32+32*i)) (UInt256.ofNat cursor) ss[i]
      have hm0 : CopySignatureArrayMemory mem array ss i (UInt256.ofNat cursor).toNat := by rw [hcur]; exact hm
      have hmem := signatureArrayCopyMemory_step hm0 hi (by rw [hcur]; change cursor+96<2^256; omega) hg.1
      simp only [hcur] at hmem
      rw [wordStride_next (array.toNat+32) 32 i (by change _<2^256; omega),
        wordStride_next offset.toNat 96 i (by change _<2^256; omega)] at r1
      have hbefore' : ∀ j (hj : j<ss.length),j < i+1 → signatureClean ss[j] := by
        intro j hj hji
        by_cases hjold : j < i
        · exact hbefore j hj hjold
        · have hji' : j=i := by omega
          subst j
          exact hg.1
      have hnext := ih (i := i+1) (cursor := cursor+96) (by omega) hmem.2.1 hbefore' hg.2 hmem.2.2 r1
      rw [show cursor+96+96*n = cursor+96*(n+1) by omega] at hnext
      by_cases hall : (∀ s∈ss,signatureClean s) ∧ cursor+96*(n+1) ≤ 2^64-1
      · rw [if_pos hall] at hnext ⊢
        obtain ⟨m2,a2,j2,D2,hp2,hv2,hf2,r2⟩ := hnext
        exact ⟨m2,a2,j2,D2,hmem.1.trans hp2,hv2,hf2,r2⟩
      · rw [if_neg hall] at hnext ⊢
        exact hnext
    · rw [if_neg (by intro hall; exact hg ⟨hall.1 _ (List.getElem_mem hi),by omega⟩)]
      exact hrun.2 hg

end Benchmarks.EAS.EAS
