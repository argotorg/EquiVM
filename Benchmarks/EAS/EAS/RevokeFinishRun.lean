import Benchmarks.EAS.EAS.RevokeLoopMemory
import Benchmarks.EAS.EAS.RevokeLoopLocals
import Benchmarks.EAS.EAS.RevokeLoopControl
import Benchmarks.EAS.EAS.ResolveManyCall

variable {fork : Ethereum.Fork}
open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables Benchmarks.EAS.EAS.Immutables
namespace Benchmarks.EAS.EAS
set_option maxRecDepth 10000

def revokeFinishLocals (L : Store) (used : UInt256) (heap : Nat) : Store :=
  heapResultLocals L "__c2$allocation" "__c2" "$EAS.freeMemory" (.int (Int.ofNat used.toNat)) heap

theorem revokeFinishSource {L imms : Store} {evm evm' : EVM.State} {old heap : Nat} {used : UInt256}
    (hh : L.get? "$EAS.freeMemory" = some (.int (Int.ofNat old)))
    (hc : ExecStmt fork config {contract := contract,locals := L,immutables := imms} evm
      (.internalCall "_resolveAttestations" revokeResolveArgs "__c2$allocation")
      (.ok (resumeAfterInternalCall {contract := contract,locals := L,immutables := imms} "__c2$allocation"
        (some [.int (Int.ofNat used.toNat),.int (Int.ofNat heap)])) evm')) :
    ExecFuncBody fork config {contract := contract,locals := L,immutables := imms} evm revokeFinish
      (.returned {contract := contract,locals := revokeFinishLocals L used heap,immutables := imms} evm'
        (some [.int (Int.ofNat used.toNat),.int (Int.ofNat heap)])) := by
  apply execFuncBody_append (heapResultBlock_ok (result := "__c2") hc hh (by decide) (by decide) (by decide))
  apply ExecFuncBody.execBlockRet
  apply ExecBlock.consReturn (ExecStmt.return ?_)
  have hu := heapResultLocals_result L "__c2$allocation" "__c2" "$EAS.freeMemory" (.int (Int.ofNat used.toNat)) heap (by decide)
  have hf := heapResultLocals_heap L "__c2$allocation" "__c2" "$EAS.freeMemory" (.int (Int.ofNat used.toNat)) heap
  simp only [evalExprs?,evalExpr?,hu,hf,EvalResult.ofOption,EvalResult.bind,bind,pure]

theorem revokeFinishRun {L : Store} {evm : EVM.State} {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C i : Nat} {heap : UInt256}
    {rs : List RevocationRequestRecord} {s : SchemaRecord} {ats : List AttestationRecord} {ptrs values R : List UInt256}
    (v : EASImmutables) (site : RevokeSite) (hstack : R.length+37 ≤ 1024) (hs : SourceState s0 ee σ evm)
    (hf : RevokeLoopLocals L site rs s ats values i heap.toNat)
    (hm : RevokeLoopMemory mem site rs s ptrs values ats heap.toNat)
    (hv : WordArrayMemoryView mem site.values values heap.toNat)
    (hh : heap.toNat ≤ 2^64-1) (hperm : rs.length = 0 ∨ ee.perm = true)
    (hlast : site.kind = .single → site.last = true)
    (hret : (D_J (deployedRuntime v) 0).contains site.ret = true)
    (rd : RD fork (deployedRuntime v) ee g s0 site.kind.exitPC
      (revokeLoopStack site ee (UInt256.ofNat i) R) mem aw rdata σ k C) :
    HeapReturnPostOrStatic fork ((resolveManyUsedValue s.resolver values).toNat ≤ site.available.toNat)
      config (deployedRuntime v) ee g s0 {contract := contract,locals := L,immutables := immStore v} evm
      revokeFinish (.int (Int.ofNat (resolveManyUsedValue s.resolver values).toNat)) site.ret
      (resolveManyUsedValue s.resolver values::R) mem heap.toNat := by
  have hlen : ats.length = values.length := hm.regions.length_eq.symm.trans hm.lengthValues.symm
  have hpv : ee.perm = true ∨ ats = [] := by
    rcases hperm with hz | hp
    · exact Or.inr (List.length_eq_zero_iff.mp (by have := hm.regions.length_eq; have := hm.lengthRequests; omega))
    · exact Or.inl hp
  obtain ⟨aw1,k1,C1,rd1⟩ := easRevokeLoopExit v site (by omega) hlast rd
  have hr := resolveManyCallRun (locals := L) (imms := immStore v) (args := revokeResolveArgs) (retVar := "__c2$allocation")
    (ats := ats) (words := values) (target := s.resolver) (ptr := heap) (record := s.value) (rev := true)
    (available := site.available) (last := site.last) (R := site.ret::R) (ret := ⟨4692⟩)
    (schema := site.schemaPtr) (array := site.records) (values := site.values) v
    (by simp only [revokeResolveArgs,evalExprs?,evalExpr?,hf.schemaRecord,hf.attestations,hf.values,hf.available,hf.last,hf.heap,
      EvalResult.ofOption,EvalResult.bind,bind,pure]) rfl
    (by rw [hm.schemaView.resolver]; exact solcAddrMask_clean (word_val_addr_canonical s.resolver))
    (by simpa only [List.length_cons] using hstack) hpv hs (hm.regions.arrayView hm.records) hv hlen hh
    (by simpa only [u256_ofNat_toNat] using hm.heapRead)
    (by rw [easPatchedValidJumps v]; jump_dest) rd1
  rcases hr with (⟨hbudget,⟨e1,σ1,m1,out,a2,k2,C2,next,hs1,hlo,hhi,hpre,hfree,hcall,rd2⟩ | ⟨hcall,hrev⟩⟩ | ⟨hcall,hrev⟩) | ⟨hcall,hstatic⟩
  · obtain ⟨a3,k3,C3,rd3⟩ := easBlocks.eas_block_4692_packed (immWords := wordsOf (immStore v)) (by omega) hret rd2
    exact Or.inl (Or.inl ⟨hbudget,Or.inl ⟨_,e1,σ1,m1,out,a3,k3,C3,next,hs1,hlo,hhi,hpre,hfree,
      revokeFinishSource hf.heap hcall,rd3⟩⟩)
  · exact Or.inl (Or.inr ⟨ExecFuncBody.execBlockRevert (ExecBlock.consRevert hcall),hrev⟩)
  · exact Or.inl (Or.inr ⟨ExecFuncBody.execBlockRevert (ExecBlock.consRevert hcall),hrev⟩)
  · exact Or.inr ⟨ExecFuncBody.execBlockStatic (ExecBlock.consStatic hcall),hstatic⟩

end Benchmarks.EAS.EAS
