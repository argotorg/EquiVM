import Benchmarks.EAS.EAS.GetUIDEVM
import Benchmarks.EAS.EAS.GetUIDSource

variable {fork : Ethereum.Fork}
open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables Benchmarks.EAS.EAS.Immutables
namespace Benchmarks.EAS.EAS
set_option maxRecDepth 10000

theorem getUIDCallRun {locals : Store} {args : List Expr} {retVar : Ident} {evm : EVM.State}
    {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem rdata : ByteArray} {aw : UInt256} {σ : AccountMap} {k C : Nat}
    {src heap dataPtr bump : UInt256} {a : AttestationRecord} {R : List UInt256} (v : EASImmutables) (site : UIDSite)
    (he : evalExprs? config {contract := contract,locals := locals,immutables := immStore v} evm args =
      .ok [a.value,.int (Int.ofNat bump.toNat),.int (Int.ofNat heap.toNat)])
    (hstack : R.length+30 ≤ 1024) (hview : AttestationMemoryView mem src dataPtr a)
    (hh : heap.toNat ≤ 2^64-1) (hheap : memLoad (UInt256.ofNat 64) mem = heap)
    (hdisj : dataPtr.toNat+32+32*((a.data.size+31)/32) ≤ heap.toNat) (hbump : bump.toNat < 2^32)
    (rd : RD fork (deployedRuntime v) ee g s0 (uidStartPC site) (bump::uidSaved site src R) mem aw rdata σ k C) :
    (∃ (mem' : ByteArray) (aw' : UInt256) (k' C' : Nat),
      heap.toNat ≤ allocateNext heap.toNat (157+a.data.size) ∧ allocateNext heap.toNat (157+a.data.size) ≤ 2^64-1 ∧
      MemoryPrefix mem mem' heap.toNat ∧ memLoad (UInt256.ofNat 64) mem' = UInt256.ofNat (allocateNext heap.toNat (157+a.data.size)) ∧
      ExecStmt fork config {contract := contract,locals := locals,immutables := immStore v} evm
        (.internalCall "_getUID" args retVar)
        (.ok (resumeAfterInternalCall {contract := contract,locals := locals,immutables := immStore v} retVar
          (some [wordBytes32Value (getUIDWord a bump),.int (Int.ofNat (allocateNext heap.toNat (157+a.data.size)))])) evm) ∧
      RD fork (deployedRuntime v) ee g s0 (uidDonePC site) (getUIDWord a bump::bump::uidSaved site src R) mem' aw' rdata σ k' C') ∨
    (ExecStmt fork config {contract := contract,locals := locals,immutables := immStore v} evm
      (.internalCall "_getUID" args retVar) .reverted ∧ RDrev fork (deployedRuntime v) g s0) := by
  have hsrc := getUIDBodySource (fork := fork) (cfg := config) (locals := getUIDArgs a bump heap.toNat) (imms := immStore v)
    (evm := evm) (a := a) (bump := bump) (heap := heap.toNat)
    (by simp only [getUIDArgs,store_get_self])
    (by simp only [getUIDArgs,store_get_ne _ _ (by decide : ("attestation" == "bump") = false),store_get_self])
    (by simp only [getUIDArgs,store_get_ne _ _ (by decide : ("attestation" == "$EAS.freeMemory") = false),
      store_get_ne _ _ (by decide : ("bump" == "$EAS.freeMemory") = false),store_get_self])
    hview.uidTimeBounds.1 hview.uidTimeBounds.2 hbump
  have hevm := easGetUID v site hstack hview hh hheap hdisj rd
  by_cases hg : allocateNext heap.toNat (157+a.data.size) ≤ 2^64-1 ∧ heap.toNat ≤ allocateNext heap.toNat (157+a.data.size)
  · rw [if_pos hg] at hsrc hevm
    obtain ⟨locals',hbody⟩ := hsrc
    obtain ⟨aw',k',C',rd',hprefix,hfree⟩ := hevm
    exact Or.inl ⟨getUIDMemory mem heap dataPtr a bump,aw',k',C',hg.2,hg.1,hprefix,hfree,
      internalCallFunctionReturn (retVar := retVar) he getUID_lookup (getUID_bind a bump heap.toNat) hbody,rd'⟩
  · rw [if_neg hg] at hsrc hevm
    exact Or.inr ⟨internalCallFunctionRevert he getUID_lookup (getUID_bind a bump heap.toNat) hsrc,hevm⟩

end Benchmarks.EAS.EAS
