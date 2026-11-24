import Benchmarks.EAS.EAS.DomainEVM
import Benchmarks.EAS.EAS.HeapCall

variable {fork : Ethereum.Fork}
open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables Benchmarks.EAS.EAS.Immutables
namespace Benchmarks.EAS.EAS

theorem domainMemory_prefix (v : EASImmutables) (owner : AccountAddress) (mem : ByteArray) (heap : Nat) :
    MemoryPrefix mem (domainMemory v owner mem heap) heap := by
  unfold domainMemory
  split
  · exact MemoryPrefix.refl _ _
  · exact (writeWordSequence_prefix mem (heap+32) heap _ (by omega)).trans
      ((memoryPrefix_sparse_writeWord _ heap heap _ (Or.inl (le_refl _))).trans
        (memoryPrefix_sparse_writeWord _ 64 heap _ (Or.inr (by decide))))

theorem domainMemory_free (v : EASImmutables) (owner : AccountAddress) (mem : ByteArray) (heap : UInt256)
    (hh : memLoad (UInt256.ofNat 64) mem = heap) :
    memLoad (UInt256.ofNat 64) (domainMemory v owner mem heap.toNat) = UInt256.ofNat (domainNext v owner heap.toNat) := by
  unfold domainMemory domainNext
  split
  · simpa only [u256_ofNat_toNat] using hh
  · apply mloadWordValue_of_readWithPadding
    · change 64 < (Reasoning.Theory.writeWord _ 64 _).size
      rw [writeWord_sparse_size]; omega
    exact buildDomainMemory_free mem heap.toNat _ _ _ owner

theorem domainNext_bounds (v : EASImmutables) (owner : AccountAddress) (heap : Nat)
    (hheap : heap ≤ 2^64-1)
    (hg : domainCacheHit v owner ∨ (allocateNext heap 192 ≤ 2^64-1 ∧ heap ≤ allocateNext heap 192)) :
    heap ≤ domainNext v owner heap ∧ domainNext v owner heap ≤ 2^64-1 := by
  unfold domainNext
  split
  · exact ⟨le_refl _,hheap⟩
  · rename_i hn
    exact ⟨(hg.resolve_left hn).2,(hg.resolve_left hn).1⟩

theorem domainCallRun {L : Store} {heapExpr : Expr} {retVar : Ident}
    {ee : ExecutionEnv} {g : Sat256} {s0 evm : EVM.State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : Nat}
    {heap ret : UInt256} {R : List UInt256} (v : EASImmutables)
    (he : evalExpr? config {contract := contract,locals := L,immutables := immStore v} evm heapExpr =
      .ok (.int (Int.ofNat heap.toNat)))
    (hstack : R.length+8 ≤ 1024) (hs : SourceState s0 ee σ evm)
    (hh : memLoad (UInt256.ofNat 64) mem = heap) (hlo : 96 ≤ heap.toNat) (hheap : heap.toNat ≤ 2^64-1)
    (hret : (D_J (deployedRuntime v) 0).contains ret = true)
    (rd : RD fork (deployedRuntime v) ee g s0 ⟨13959⟩ (ret::R) mem aw rdata σ k C) :
    HeapCallRun fork config (deployedRuntime v) ee g s0 {contract := contract,locals := L,immutables := immStore v}
      evm "_domainSeparatorV4" [heapExpr] retVar (wordBytes32Value (domainWord v ee.codeOwner))
      ret (domainWord v ee.codeOwner::R) mem heap.toNat := by
  by_cases hg : domainCacheHit v ee.codeOwner ∨
      (allocateNext heap.toNat 192 ≤ 2^64-1 ∧ heap.toNat ≤ allocateNext heap.toNat 192)
  · obtain ⟨aw1,k1,C1,r1⟩ := easDomain_ok v hstack hh hlo hg hret rd
    have hb := domainNext_bounds v ee.codeOwner heap.toNat hheap hg
    refine Or.inl ⟨evm,σ,domainMemory v ee.codeOwner mem heap.toNat,rdata,aw1,k1,C1,
      domainNext v ee.codeOwner heap.toNat,hs,hb.1,hb.2,domainMemory_prefix v ee.codeOwner mem heap.toNat,
      domainMemory_free v ee.codeOwner mem heap hh,?_,r1⟩
    have hc := domainCall_ok (fork := fork) (cfg := config) (retVar := retVar) v he (by simpa only [hs.env] using hg)
    simpa only [hs.env] using hc
  · have hn : ¬ domainCacheHit v ee.codeOwner := fun h => hg (Or.inl h)
    have ha : ¬ (allocateNext heap.toNat 192 ≤ 2^64-1 ∧ heap.toNat ≤ allocateNext heap.toNat 192) := fun h => hg (Or.inr h)
    refine Or.inr ⟨domainCall_revert v he (by simpa only [hs.env] using hn) ha,?_⟩
    exact easDomain_revert v (by simp only [List.length_cons]; omega) hh hn ha rd

end Benchmarks.EAS.EAS
