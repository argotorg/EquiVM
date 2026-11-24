import Benchmarks.EAS.EAS.ResolveOneFinish

variable {fork : Ethereum.Fork}
open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables Benchmarks.EAS.EAS.Immutables
namespace Benchmarks.EAS.EAS
set_option maxRecDepth 10000

theorem resolveOneResolverRun {locals imms : Store} {ee : ExecutionEnv} {g : Sat256} {s0 evm : EVM.State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : Nat}
    {src dataPtr available value ptr ret : UInt256} {R : List UInt256} {a : AttestationRecord} {target : AccountAddress}
    {rev last : Bool} (v : EASImmutables)
    (hf : ResolveOneLocals locals a target value (UInt256.sub available value) rev last ptr.toNat)
    (hstack : R.length+26 ≤ 1024) (hperm : ee.perm = true) (hs : SourceState s0 ee σ evm)
    (hview : AttestationMemoryView mem src dataPtr a)
    (hsrc : src.toNat+320 ≤ ptr.toNat) (hdata : dataPtr.toNat+32+32*((a.data.size+31)/32) ≤ ptr.toNat)
    (hheap : ptr.toNat ≤ 2^64-1) (hh : memLoad (UInt256.ofNat 64) mem = ptr)
    (hret : (D_J (deployedRuntime v) 0).contains ret = true)
    (rd : RD fork (deployedRuntime v) ee g s0 ⟨15784⟩
      (src::rev.toUInt256::UInt256.ofNat target.val::last.toUInt256::available::value::ret::R) mem aw rdata σ k C) :
    HeapReturnRun fork config (deployedRuntime v) ee g s0 {contract := contract, locals := locals, immutables := imms}
      evm ([resolveOneResolver,resolveOneRefund] ++ resolveOneReturn) (.int (Int.ofNat value.toNat)) ret (value::R) mem ptr.toNat := by
  have hlo : 96 ≤ ptr.toNat := by have h := hview.sourceLow; omega
  have hb : ptr.toNat+420+32*((a.data.size+31)/32) < UInt256.size := by change _ < 2^256; omega
  have hsize : a.data.size < UInt256.size := by change a.data.size < 2^256; omega
  obtain ⟨aw1,k1,C1,rd1⟩ := resolveOneChoose v rev (by simp only [List.length_cons]; omega) rd
  obtain ⟨evm',σ',success,out,hcall,hs',hout,hr⟩ := resolverOneEVM v rev
    (by simp only [List.length_cons]; omega) hperm hs hview hsrc hdata hheap hh rd1
  simp only [accountAddress_roundtrip] at hcall
  have hsource := resolveOneResolverSource (hperm := Or.inr ((congrArg ExecutionEnv.perm hs.env).trans hperm)) (imms := imms) hf.resolver hf.attestation hf.value hf.heap hf.revocation
    hsize hcall (by omega)
  have houtWord : out.size < UInt256.size := by change out.size < 2^256; omega
  by_cases hv : resolverCallValid ptr.toNat success out
  · rw [if_pos hv] at hr
    obtain ⟨aw2,k2,C2,rd2⟩ := hr
    have hg := resolveOneAccepted v rev (by simp only [List.length_cons]; omega) rd2
    by_cases hn : calldataWord out 0 ≠ ⟨0⟩
    · rw [if_pos hn] at hg
      rw [if_pos (show callBoolAccepted ptr.toNat success out from ⟨hv,hn⟩)] at hsource
      obtain ⟨aw3,k3,C3,rd3⟩ := hg
      let next := allocateNext ptr.toNat (min out.size 32)
      let nextPtr := UInt256.ofNat next
      have hnext : nextPtr.toNat = next := ulit_toNat' _ (by change next < 2^256; have h := hv.2.1.1; omega)
      have hf' : ResolveOneLocals (resolveOneResolverLocals locals rev ptr.toNat out)
          a target value (UInt256.sub available value) rev last nextPtr.toNat := by
        simpa only [hnext] using hf.resolved out
      have hfinish := resolveOneFinishRun (imms := imms) v hf' (by omega) hperm hs'
        (by rw [hnext]; exact hv.2.1.1) (by rw [hnext]; have h := hv.2.1.2; omega)
        (resolverOneCallOutput_heap mem src ptr dataPtr rev out) hret rd3
      simp only [hnext] at hfinish
      exact hfinish.prepend (ExecBlock.consNormal hsource ExecBlock.nil)
        (resolverOneCallOutput_prefix hview hsrc hdata hb out houtWord) hv.2.1.2
    · rw [if_neg hn] at hg
      rw [if_neg (show ¬ callBoolAccepted ptr.toNat success out from fun h => hn h.2)] at hsource
      exact HeapReturnRun.of_revert_prefix (front := [resolveOneResolver]) (ExecBlock.consRevert hsource) hg
  · rw [if_neg hv] at hr
    rw [if_neg (show ¬ callBoolAccepted ptr.toNat success out from fun h => hv h.1)] at hsource
    exact HeapReturnRun.of_revert_prefix (front := [resolveOneResolver]) (ExecBlock.consRevert hsource) hr


end Benchmarks.EAS.EAS
