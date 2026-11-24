import Benchmarks.EAS.EAS.RevokeLoopRun
import Benchmarks.EAS.EAS.RevokeFinishRun

variable {fork : Ethereum.Fork}
open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables Benchmarks.EAS.EAS.Immutables
namespace Benchmarks.EAS.EAS

theorem revokeLoopFinishRun {L : Store} {evm : EVM.State} {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : Nat} {heap : UInt256}
    {rs : List RevocationRequestRecord} {s : SchemaRecord} {ats : List AttestationRecord} {ptrs values R : List UInt256}
    (v : EASImmutables) (site : RevokeSite) (hstack : R.length+37 ≤ 1024) (hs : SourceState s0 ee σ evm)
    (hf : RevokeLoopLocals L site rs s ats values 0 heap.toNat)
    (hm : RevokeLoopMemory mem site rs s ptrs values ats heap.toNat) (hh : heap.toNat ≤ 2^64-1)
    (hlast : site.kind = .single → site.last = true)
    (hret : (D_J (deployedRuntime v) 0).contains site.ret = true)
    (rd : RD fork (deployedRuntime v) ee g s0 site.kind.loopPC
      (revokeLoopStack site ee (UInt256.ofNat 0) R) mem aw rdata σ k C) :
    ∃ used : UInt256, HeapReturnPostOrStatic fork (used.toNat ≤ site.available.toNat)
      config (deployedRuntime v) ee g s0 {contract := contract,locals := L,immutables := immStore v} evm
      ([revokeLoop] ++ revokeFinish) (.int (Int.ofNat used.toNat)) site.ret (used::R) mem site.records.toNat := by
  have hr := revokeLoopRun v site hstack hs hf hm hh rd
  rcases hr with ⟨L1,e1,σ1,m1,a1,k1,C1,next,ps,records,vs,hlo,hhi,hperm,hstate,hpre,hf1,hm1,hv1,hsol,rd1⟩ |
      ⟨hsol,hrev⟩ | ⟨hsol,hstatic⟩
  · have hn : (UInt256.ofNat next).toNat = next := ulit_toNat' _ (by change next < 2^256; omega)
    have hfinish := revokeFinishRun (heap := UInt256.ofNat next) v site hstack hstate
      (by simpa only [hn] using hf1) (by simpa only [hn] using hm1) (by simpa only [hn] using hv1)
      (by rw [hn]; exact hhi) hperm hlast hret rd1
    refine ⟨resolveManyUsedValue s.resolver vs,hfinish.prepend (ExecBlock.consNormal hsol ExecBlock.nil) hpre ?_⟩
    rw [hn]; have := hm1.records.span; omega
  · exact ⟨⟨0⟩,HeapReturnPostOrStatic.of_revert_prefix (ExecBlock.consRevert hsol) hrev⟩
  · exact ⟨⟨0⟩,Or.inr ⟨ExecFuncBody.execBlockStatic (ExecBlock.consStatic hsol),hstatic⟩⟩

end Benchmarks.EAS.EAS
