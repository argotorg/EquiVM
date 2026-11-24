import Benchmarks.EAS.EAS.ResolveManyFinishRun

variable {fork : Ethereum.Fork}
open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables Benchmarks.EAS.EAS.Immutables
namespace Benchmarks.EAS.EAS
set_option maxRecDepth 10000

theorem resolveManyResolverRun {locals imms : Store} {ee : ExecutionEnv} {g : Sat256} {s0 evm : EVM.State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C i : Nat}
    {junk0 junk1 junk2 array values available total ptr ret : UInt256} {R : List UInt256}
    {ats : List AttestationRecord} {words : List UInt256} {target : AccountAddress} {rev last : Bool}
    (v : EASImmutables) (hf : ResolveManyLocals locals ats words target available total rev last ptr.toNat i)
    (hstack : R.length+36 ≤ 1024) (hperm : ee.perm = true ∨ total = ⟨0⟩) (hs : SourceState s0 ee σ evm)
    (harray : AttestationArrayMemoryView mem array ats ptr.toNat)
    (hvalues : WordArrayMemoryView mem values words ptr.toNat)
    (hheap : ptr.toNat ≤ 2^64-1) (hh : memLoad (UInt256.ofNat 64) mem = ptr)
    (hret : (D_J (deployedRuntime v) 0).contains ret = true)
    (rd : RD fork (deployedRuntime v) ee g s0 (resolverManyEntryPC rev)
      (resolverManyEntryStack rev junk0 junk1 junk2 array (UInt256.ofNat target.val) values last.toUInt256 available total (ret::R))
      mem aw rdata σ k C) :
    HeapReturnOrStatic fork config (deployedRuntime v) ee g s0 {contract := contract, locals := locals, immutables := imms}
      evm ([resolveManyResolver,resolveManyRefund] ++ resolveManyReturn) (.int (Int.ofNat total.toNat)) ret (total::R) mem ptr.toNat := by
  have hlo : 124 ≤ ptr.toNat := by have := harray.low; have := harray.span; omega
  have henc := resolverManyBody_bound harray hvalues hheap
  rw [resolverArraysBody_size] at henc
  have hdata : ∀ a ∈ ats, a.data.size < UInt256.size := by
    intro a ha
    have hb := harray.data_bound a ha
    change a.data.size < 2^256
    omega
  have hbound : attestationArrayOffset ats ats.length < UInt256.size := by
    rw [attestationArrayEncoding_size] at henc
    change attestationArrayOffset ats ats.length < 2^256
    omega
  have hvlen : words.length < UInt256.size := by have := hvalues.span; change words.length < 2^256; omega
  have hsize : 64+(attestationArrayEncoding ats).size < UInt256.size := by change _ < 2^256; omega
  obtain ⟨evm',σ',success,out,finalMem,hcall,hs',hout,hp,hh',hr⟩ := resolverManyEVM
    (junk0 := junk0) (junk1 := junk1) (junk2 := junk2) v rev
    (by simp only [List.length_cons]; omega) hperm hs harray hvalues hheap hlo hh rd
  simp only [accountAddress_roundtrip] at hcall
  have hsource := resolveManyResolverSource (imms := imms)
    (hperm := by
      rcases hperm with hp | hz
      · exact Or.inr ((congrArg ExecutionEnv.perm hs.env).trans hp)
      · exact Or.inl (by subst total; rfl))
    hf hdata hbound hvlen hsize hcall (by omega)
  by_cases hv : resolverCallValid ptr.toNat success out
  · rw [if_pos hv] at hr
    obtain ⟨a1,k1,C1,r1⟩ := hr
    have hg := resolveManyAccepted v rev (by simp only [List.length_cons]; omega) r1
    by_cases hn : calldataWord out 0 ≠ ⟨0⟩
    · rw [if_pos hn] at hg
      rw [if_pos (show callBoolAccepted ptr.toNat success out from ⟨hv,hn⟩)] at hsource
      obtain ⟨a2,k2,C2,r2⟩ := hg
      let next := allocateNext ptr.toNat (min out.size 32)
      let nextPtr := UInt256.ofNat next
      have hnext : nextPtr.toNat = next := ulit_toNat' _ (by change next < 2^256; have := hv.2.1.1; omega)
      have hf' : ResolveManyLocals (resolveManyResolverLocals locals rev ptr.toNat out)
          ats words target available total rev last nextPtr.toNat i := by
        simpa only [hnext] using hf.resolved out
      have hfinish := resolveManyFinishRun (imms := imms) v hf' (by omega) hs'
        (by rw [hnext]; exact hv.2.1.1) (by rw [hnext]; have := hv.2.1.2; omega) hh' hret r2
      simp only [hnext] at hfinish
      exact hfinish.prepend (ExecBlock.consNormal hsource ExecBlock.nil) hp hv.2.1.2
    · rw [if_neg hn] at hg
      rw [if_neg (show ¬ callBoolAccepted ptr.toNat success out from fun h => hn h.2)] at hsource
      exact HeapReturnOrStatic.of_revert_prefix (front := [resolveManyResolver]) (ExecBlock.consRevert hsource) hg
  · rw [if_neg hv] at hr
    rw [if_neg (show ¬ callBoolAccepted ptr.toNat success out from fun h => hv h.1)] at hsource
    exact HeapReturnOrStatic.of_revert_prefix (front := [resolveManyResolver]) (ExecBlock.consRevert hsource) hr

end Benchmarks.EAS.EAS
