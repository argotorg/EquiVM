import Benchmarks.EAS.EAS.ResolveManyLoopRun
import Benchmarks.EAS.EAS.HeapPost
import Benchmarks.EAS.EAS.ResolveManyResolverRun

variable {fork : Ethereum.Fork}
open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables Benchmarks.EAS.EAS.Immutables
namespace Benchmarks.EAS.EAS
set_option maxRecDepth 10000

theorem resolveManyTailRun {locals imms : Store} {ee : ExecutionEnv} {g : Sat256} {s0 evm : EVM.State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : Nat}
    {array values available ptr ret : UInt256} {R : List UInt256}
    {ats : List AttestationRecord} {words : List UInt256} {target : AccountAddress} {rev last : Bool}
    (v : EASImmutables) (hf : ResolveManyLocals locals ats words target available ⟨0⟩ rev last ptr.toNat 0)
    (hstack : R.length+36 ≤ 1024) (hperm : ee.perm = true ∨ words = []) (hs : SourceState s0 ee σ evm)
    (harray : AttestationArrayMemoryView mem array ats ptr.toNat)
    (hvalues : WordArrayMemoryView mem values words ptr.toNat)
    (hheap : ptr.toNat ≤ 2^64-1) (hh : memLoad (UInt256.ofNat 64) mem = ptr)
    (hret : (D_J (deployedRuntime v) 0).contains ret = true)
    (rd : RD fork (deployedRuntime v) ee g s0 (resolveManyLoopPC rev)
      (resolveManyLoopStack rev 0 array (UInt256.ofNat target.val) values available last.toUInt256 ⟨0⟩ words.length (ret::R))
      mem aw rdata σ k C) :
    HeapReturnPostOrStatic fork ((resolveManyTotal words words.length).toNat ≤ available.toNat) config (deployedRuntime v) ee g s0 {contract := contract, locals := locals, immutables := imms}
      evm ([.while timeArrayGuard resolveManyIteration,resolveManyResolver,resolveManyRefund] ++ resolveManyReturn)
      (.int (Int.ofNat (resolveManyTotal words words.length).toNat)) ret (resolveManyTotal words words.length::R) mem ptr.toNat := by
  obtain ⟨available',hloop⟩ := resolveManyLoopRun (imms := imms) v hf (by simp only [List.length_cons]; omega) hs hvalues hheap hh rd
  rcases hloop with ⟨L,e,σ',m,out,a,j,D,heap',hs',hlo,hhi,hp,hh',⟨hf',hbudget⟩,hsrc,hr⟩ | ⟨hsrc,hr⟩
  · let p := UInt256.ofNat heap'
    have hn : p.toNat = heap' := ulit_toNat' _ (by change _ < 2^256; omega)
    have ha := (harray.preserve hp ptr.val.isLt).mono hlo
    have hv := (hvalues.preserve hp ptr.val.isLt).mono hlo
    have hf1 : ResolveManyLocals L ats words target available' (resolveManyTotal words words.length) rev last p.toNat words.length := by
      simpa only [hn] using hf'
    have hpv : ee.perm = true ∨ resolveManyTotal words words.length = ⟨0⟩ := by
      rcases hperm with hpv | rfl
      · exact Or.inl hpv
      · exact Or.inr rfl
    have hfinish := resolveManyResolverRun (imms := imms) (junk0 := UInt256.ofNat words.length)
      (junk1 := UInt256.ofNat words.length) (junk2 := ⟨0⟩) v hf1 hstack hpv hs'
      (by simpa only [hn] using ha) (by simpa only [hn] using hv) (by rw [hn]; exact hhi) hh' hret hr
    simp only [hn] at hfinish
    exact (hfinish.withPost (by omega : (resolveManyTotal words words.length).toNat ≤ available.toNat)).prepend hsrc hp hlo
  · exact HeapReturnPostOrStatic.of_revert_prefix (front := [.while timeArrayGuard resolveManyIteration]) hsrc hr

end Benchmarks.EAS.EAS
