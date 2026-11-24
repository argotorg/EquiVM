import Benchmarks.EAS.EAS.UIDIteration
import Benchmarks.EAS.EAS.WhileRank

variable {fork : Ethereum.Fork}
open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables Benchmarks.EAS.EAS.Immutables
namespace Benchmarks.EAS.EAS
set_option maxRecDepth 10000

theorem uidLoopRun {L : Store} {evm : EVM.State} {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : Nat}
    {src heap dataPtr bump : UInt256} {a : AttestationRecord} {R : List UInt256} (v : EASImmutables) (site : UIDSite)
    (hstack : R.length+30 ≤ 1024) (hf : UIDLoopLocals L a bump heap.toNat) (hs : SourceState s0 ee σ evm)
    (hview : AttestationMemoryView mem src dataPtr a) (hh : heap.toNat ≤ 2^64-1)
    (hheap : memLoad (UInt256.ofNat 64) mem = heap) (hsrc : src.toNat+320 ≤ heap.toNat)
    (hdisj : dataPtr.toNat+32+32*((a.data.size+31)/32) ≤ heap.toNat) (hbump : bump.toNat < 2^32)
    (rd : RD fork (deployedRuntime v) ee g s0 (uidStartPC site) (bump::uidSaved site src R) mem aw rdata σ k C) :
    (∃ (L' : Store) (mem' : ByteArray) (aw' : UInt256) (k' C' heap' : Nat) (word bump' : UInt256),
      heap.toNat ≤ heap' ∧ heap' ≤ 2^64-1 ∧ MemoryPrefix mem mem' heap.toNat ∧
      memLoad (UInt256.ofNat 64) mem' = UInt256.ofNat heap' ∧ UIDLoopKeep L L' ∧
      UIDLoopLocals L' a bump' heap' ∧ L'.get? "uid" = some (wordBytes32Value word) ∧ dbUIDWord evm word = ⟨0⟩ ∧
      ExecStmt fork config {contract := contract,locals := L,immutables := immStore v} evm (.while (.boolLit true) uidIteration)
        (.ok {contract := contract,locals := L',immutables := immStore v} evm) ∧
      RD fork (deployedRuntime v) ee g s0 (uidAvailablePC site) (word::bump'::uidSaved site src R) mem' aw' rdata σ k' C') ∨
    (ExecStmt fork config {contract := contract,locals := L,immutables := immStore v} evm (.while (.boolLit true) uidIteration) .reverted ∧
      RDrev fork (deployedRuntime v) g s0) := by
  let Inv : Nat → Store → EVM.State → Prop := fun n L1 e1 =>
    ∃ (ptr b : UInt256) (m : ByteArray) (a1 : UInt256) (j D : Nat),
      e1 = evm ∧ n = 2^64-ptr.toNat ∧ heap.toNat ≤ ptr.toNat ∧ ptr.toNat ≤ 2^64-1 ∧ b.toNat < 2^32 ∧
      MemoryPrefix mem m heap.toNat ∧ AttestationMemoryView m src dataPtr a ∧ memLoad (UInt256.ofNat 64) m = ptr ∧
      UIDLoopKeep L L1 ∧ UIDLoopLocals L1 a b ptr.toNat ∧
      RD fork (deployedRuntime v) ee g s0 (uidStartPC site) (b::uidSaved site src R) m a1 rdata σ j D
  let Post : Store → EVM.State → Prop := fun L1 e1 => e1 = evm ∧
    ∃ (m : ByteArray) (a1 : UInt256) (j D next : Nat) (word b : UInt256),
      heap.toNat ≤ next ∧ next ≤ 2^64-1 ∧ MemoryPrefix mem m heap.toNat ∧
      memLoad (UInt256.ofNat 64) m = UInt256.ofNat next ∧ UIDLoopKeep L L1 ∧ UIDLoopLocals L1 a b next ∧
      L1.get? "uid" = some (wordBytes32Value word) ∧ dbUIDWord evm word = ⟨0⟩ ∧
      RD fork (deployedRuntime v) ee g s0 (uidAvailablePC site) (word::b::uidSaved site src R) m a1 rdata σ j D
  have hstep : ∀ n L1 e1, Inv n L1 e1 →
      (∃ L2 e2, ExecBlock fork config {contract := contract,locals := L1,immutables := immStore v} e1 uidIteration
        (.break {contract := contract,locals := L2,immutables := immStore v} e2) ∧ Post L2 e2) ∨
      (∃ n' L2 e2, n' < n ∧ ExecBlock fork config {contract := contract,locals := L1,immutables := immStore v} e1 uidIteration
        (.ok {contract := contract,locals := L2,immutables := immStore v} e2) ∧ Inv n' L2 e2) ∨
      (ExecBlock fork config {contract := contract,locals := L1,immutables := immStore v} e1 uidIteration .reverted ∧ RDrev fork (deployedRuntime v) g s0) ∨
      (ExecBlock fork config {contract := contract,locals := L1,immutables := immStore v} e1 uidIteration .staticViolation ∧ False) := by
    rintro n L1 e1 ⟨ptr,b,m,a1,j,D,rfl,hn,hlo,hhi,hb,hp,hv,hh1,hkeep,hf1,hr1⟩
    have hr := uidIterationRun v site hstack hf1 hs hv hhi hh1 (by omega) hb hr1
    dsimp only at hr
    rcases hr with ⟨m',a2,j',D',hgrowth,hcap,hp',hh2,hcase⟩ | ⟨hsrc',hrev⟩
    · let next := allocateNext ptr.toNat (157+a.data.size)
      let word := getUIDWord a b
      have hmono : ptr.toNat ≤ next := by omega
      have hp2 := hp.trans (hp'.mono hlo)
      rcases hcase with ⟨hz,hsrc',hr2⟩ | ⟨hz,hsrc',hr2⟩
      · refine Or.inl ⟨uidComputeLocals L1 word next,e1,hsrc',rfl,m',a2,j',D',next,word,b,
          le_trans hlo hmono,hcap,hp2,hh2,hkeep.trans (uidComputeLocals_keep _ _ _),hf1.compute,?_,hz,hr2⟩
        exact store_get_self _ _ _
      · let ptr' := UInt256.ofNat next
        have hptr : ptr'.toNat = next := ulit_toNat' _ (by change next < 2^256; dsimp only [next]; omega)
        have hv' := hv.preserve hp' (by omega) (by omega) ptr.val.isLt
        refine Or.inr (Or.inl ⟨2^64-next,uidNextLocals L1 word b next,e1,?_,hsrc',
          ptr',nextUIDBump b,m',a2,j',D',rfl,?_,?_,?_,nextUIDBump_lt b,hp2,hv',hh2,
          hkeep.trans (uidNextLocals_keep _ _ _ _),?_,hr2⟩)
        · dsimp only [next]; omega
        · rw [hptr]
        · rw [hptr]; exact le_trans hlo hmono
        · rw [hptr]; exact hcap
        · simpa only [hptr] using hf1.next (word := word) (next := next)
    · exact Or.inr (Or.inr (Or.inl ⟨hsrc',hrev⟩))
  have hloop := execWhile_true_rank (cfg := config) (contract := contract) (imms := immStore v)
    (body := uidIteration) Inv Post (RDrev fork (deployedRuntime v) g s0) False hstep (2^64-heap.toNat) L evm
    ⟨heap,bump,mem,aw,k,C,rfl,rfl,le_refl _,hh,hbump,MemoryPrefix.refl _ _,hview,hheap,UIDLoopKeep.refl _,hf,rd⟩
  rcases hloop with ⟨L',e',hwhile,hpost⟩ | ⟨hwhile,hrev⟩ | ⟨_,hfalse⟩
  · rcases hpost with ⟨rfl,m',a1,j,D,next,word,b,hlo,hcap,hp,hh1,hkeep,hf1,hu,hz,hr⟩
    exact Or.inl ⟨L',m',a1,j,D,next,word,b,hlo,hcap,hp,hh1,hkeep,hf1,hu,hz,hwhile,hr⟩
  · exact Or.inr ⟨hwhile,hrev⟩
  · exact hfalse.elim

end Benchmarks.EAS.EAS
