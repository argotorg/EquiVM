import Benchmarks.EAS.EAS.ResolveManyIterationRun
import Benchmarks.EAS.EAS.ResolveManyFinishControl
import Benchmarks.EAS.EAS.WhileInvariant

variable {fork : Ethereum.Fork}
open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables Benchmarks.EAS.EAS.Immutables
namespace Benchmarks.EAS.EAS
set_option maxRecDepth 10000

def resolveManyTotal (words : List UInt256) (i : Nat) : UInt256 :=
  (words.take i).foldl (fun total value => total+value) ⟨0⟩

theorem resolveManyTotal_step (words : List UInt256) (i : Nat) (hi : i < words.length) :
    resolveManyTotal words (i+1) = resolveManyTotal words i+words[i] := by
  simp only [resolveManyTotal,List.take_succ_eq_append_getElem hi,List.foldl_append,List.foldl_cons,List.foldl_nil]

theorem resolveManyLoopRun {locals imms : Store} {ee : ExecutionEnv} {g : Sat256} {s0 evm : EVM.State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : Nat}
    {array values available ptr : UInt256} {R : List UInt256}
    {ats : List AttestationRecord} {words : List UInt256} {target : AccountAddress} {rev last : Bool}
    (v : EASImmutables) (hf : ResolveManyLocals locals ats words target available ⟨0⟩ rev last ptr.toNat 0)
    (hstack : R.length+21 ≤ 1024) (hs : SourceState s0 ee σ evm)
    (hv : WordArrayMemoryView mem values words ptr.toNat)
    (hheap : ptr.toNat ≤ 2^64-1) (hh : memLoad (UInt256.ofNat 64) mem = ptr)
    (rd : RD fork (deployedRuntime v) ee g s0 (resolveManyLoopPC rev)
      (resolveManyLoopStack rev 0 array (UInt256.ofNat target.val) values available last.toUInt256 ⟨0⟩ words.length R)
      mem aw rdata σ k C) :
    ∃ available', HeapBlockRun fork config (deployedRuntime v) ee g s0 {contract := contract, locals := locals, immutables := imms}
      evm [.while timeArrayGuard resolveManyIteration]
      (fun L heap => ResolveManyLocals L ats words target available' (resolveManyTotal words words.length) rev last heap words.length ∧
        available'.toNat+(resolveManyTotal words words.length).toNat = available.toNat)
      (resolverManyEntryPC rev)
      (resolverManyEntryStack rev (UInt256.ofNat words.length) (UInt256.ofNat words.length) ⟨0⟩ array (UInt256.ofNat target.val)
        values last.toUInt256 available' (resolveManyTotal words words.length) R) mem ptr.toNat := by
  let Inv := fun i L e => ∃ (σ1 : AccountMap) (m out : ByteArray) (a : UInt256) (j D : Nat) (p avail : UInt256),
    SourceState s0 ee σ1 e ∧ ptr.toNat ≤ p.toNat ∧ p.toNat ≤ 2^64-1 ∧ MemoryPrefix mem m ptr.toNat ∧
    WordArrayMemoryView m values words p.toNat ∧ memLoad (UInt256.ofNat 64) m = p ∧
    ResolveManyLocals L ats words target avail (resolveManyTotal words i) rev last p.toNat i ∧
    avail.toNat+(resolveManyTotal words i).toNat = available.toNat ∧
    RD fork (deployedRuntime v) ee g s0 (resolveManyLoopPC rev)
      (resolveManyLoopStack rev i array (UInt256.ofNat target.val) values avail last.toUInt256 (resolveManyTotal words i) words.length R)
      m a out σ1 j D
  have hguard : ∀ i L e, i ≤ words.length → Inv i L e →
      evalExpr? config {contract := contract, locals := L, immutables := imms} e timeArrayGuard =
        .ok (.bool (decide (i < words.length))) := by
    rintro i L e _ ⟨σ1,m,out,a,j,D,p,avail,_,_,_,_,_,_,hf1,_,_⟩
    exact resolveManyGuardSource hf1
  have hstep : ∀ i L e, i < words.length → Inv i L e →
      (∃ L' e', ExecBlock fork config {contract := contract, locals := L, immutables := imms} e resolveManyIteration
        (.ok {contract := contract, locals := L', immutables := imms} e') ∧ Inv (i+1) L' e') ∨
      (ExecBlock fork config {contract := contract, locals := L, immutables := imms} e resolveManyIteration .reverted ∧
        RDrev fork (deployedRuntime v) g s0) ∨
      (ExecBlock fork config {contract := contract, locals := L, immutables := imms} e resolveManyIteration .staticViolation ∧ False) := by
    rintro i L e hi ⟨σ1,m,out,a,j,D,p,avail,hs1,hlo,hhi,hp,hv1,hh1,hf1,hbudget,hr1⟩
    have hrun := resolveManyIterationRun (imms := imms) v hf1 hi hstack hs1 hv1 hhi hh1 hr1
    rcases hrun with ⟨L',e',σ2,m',out',a',j',D',heap',hs2,hlo',hhi',hp',hh2,⟨hf2,hpay⟩,hsrc,hr2⟩ | ⟨hsrc,hr2⟩
    · let p' := UInt256.ofNat heap'
      have hn : p'.toNat = heap' := ulit_toNat' _ (by change _ < 2^256; omega)
      have hb : p.toNat < UInt256.size := p.val.isLt
      have hv2 := (hv1.preserve hp' hb).mono hlo'
      refine Or.inl ⟨L',e',hsrc,σ2,m',out',a',j',D',p',UInt256.sub avail words[i],hs2,?_,?_,?_,?_,hh2,?_,?_,?_⟩
      · rw [hn]; omega
      · rw [hn]; exact hhi'
      · exact hp.trans (hp'.mono hlo)
      · simpa only [hn] using hv2
      · simpa only [hn,resolveManyTotal_step words i hi] using hf2
      · have hfit : (resolveManyTotal words i).toNat+words[i].toNat < UInt256.size := by
          have : available.toNat < UInt256.size := available.val.isLt
          omega
        rw [resolveManyTotal_step words i hi,usub_toNat hpay,uadd_toNat,Nat.mod_eq_of_lt hfit]
        omega
      · simpa only [resolveManyTotal_step words i hi] using hr2
    · exact Or.inr (Or.inl ⟨hsrc,hr2⟩)
  have hloop := execWhile_invariant (cfg := config) (contract := contract) (imms := imms)
    (cond := timeArrayGuard) (body := resolveManyIteration) (bound := words.length)
    Inv (Inv words.length) (RDrev fork (deployedRuntime v) g s0) False hguard (fun _ _ h => h) hstep
    words.length 0 locals evm (by omega)
    ⟨σ,mem,rdata,aw,k,C,ptr,available,hs,le_refl _,hheap,MemoryPrefix.refl _ _,hv,hh,hf,by simp only [resolveManyTotal,List.take_zero,List.foldl_nil]; rfl,rd⟩
  rcases hloop with ⟨L,e,hsrc,σ1,m,out,a,j,D,p,avail,hs1,hlo,hhi,hp,hv1,hh1,hf1,hbudget,hr1⟩ | ⟨hsrc,hr1⟩ | ⟨_,hfalse⟩
  · obtain ⟨a',j',D',hr⟩ := resolveManyLoopDone v rev (by omega) hr1
    exact ⟨avail,Or.inl ⟨L,e,σ1,m,out,a',j',D',p.toNat,hs1,hlo,hhi,hp,
      by simpa only [u256_ofNat_toNat] using hh1,⟨hf1,hbudget⟩,ExecBlock.consNormal hsrc ExecBlock.nil,hr⟩⟩
  · exact ⟨available,Or.inr ⟨ExecBlock.consRevert hsrc,hr1⟩⟩
  · exact hfalse.elim

end Benchmarks.EAS.EAS
