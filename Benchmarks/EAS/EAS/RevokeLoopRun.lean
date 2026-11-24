import Benchmarks.EAS.EAS.RevokeIterationRun
import Benchmarks.EAS.EAS.WhileInvariant
import Benchmarks.EAS.EAS.TimeArray

variable {fork : Ethereum.Fork}
open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables Benchmarks.EAS.EAS.Immutables
namespace Benchmarks.EAS.EAS

theorem revokeLoopRun {L : Store} {evm : EVM.State} {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : Nat} {heap : UInt256}
    {rs : List RevocationRequestRecord} {s : SchemaRecord} {ats : List AttestationRecord} {ptrs values R : List UInt256}
    (v : EASImmutables) (site : RevokeSite) (hstack : R.length+37 ≤ 1024) (hs : SourceState s0 ee σ evm)
    (hf : RevokeLoopLocals L site rs s ats values 0 heap.toNat)
    (hm : RevokeLoopMemory mem site rs s ptrs values ats heap.toNat) (hh : heap.toNat ≤ 2^64-1)
    (rd : RD fork (deployedRuntime v) ee g s0 site.kind.loopPC
      (revokeLoopStack site ee (UInt256.ofNat 0) R) mem aw rdata σ k C) :
    (∃ L' evm' σ' mem' aw' k' C' next ptrs' ats' values',
      heap.toNat ≤ next ∧ next ≤ 2^64-1 ∧ (rs.length = 0 ∨ ee.perm = true) ∧
      SourceState s0 ee σ' evm' ∧ MemoryPrefix mem mem' site.records.toNat ∧
      RevokeLoopLocals L' site rs s ats' values' rs.length next ∧
      RevokeLoopMemory mem' site rs s ptrs' values' ats' next ∧ WordArrayMemoryView mem' site.values values' next ∧
      ExecStmt fork config {contract := contract,locals := L,immutables := immStore v} evm revokeLoop
        (.ok {contract := contract,locals := L',immutables := immStore v} evm') ∧
      RD fork (deployedRuntime v) ee g s0 site.kind.exitPC
        (revokeLoopStack site ee (UInt256.ofNat rs.length) R) mem' aw' rdata σ' k' C') ∨
    (ExecStmt fork config {contract := contract,locals := L,immutables := immStore v} evm revokeLoop .reverted ∧
      RDrev fork (deployedRuntime v) g s0) ∨
    (ExecStmt fork config {contract := contract,locals := L,immutables := immStore v} evm revokeLoop .staticViolation ∧
      RDstatic fork (deployedRuntime v) g s0) := by
  let Inv := fun i L1 e1 => ∃ (σ1 : AccountMap) (m : ByteArray) (a : UInt256) (j D : Nat) (p : UInt256)
      (ps vs : List UInt256) (records : List AttestationRecord),
    SourceState s0 ee σ1 e1 ∧ heap.toNat ≤ p.toNat ∧ p.toNat ≤ 2^64-1 ∧
    (i = 0 ∨ (ee.perm = true ∧ site.values.toNat+32+32*vs.length ≤ m.size)) ∧
    MemoryPrefix mem m site.records.toNat ∧ RevokeLoopLocals L1 site rs s records vs i p.toNat ∧
    RevokeLoopMemory m site rs s ps vs records p.toNat ∧
    RD fork (deployedRuntime v) ee g s0 site.kind.loopPC (revokeLoopStack site ee (UInt256.ofNat i) R) m a rdata σ1 j D
  have hguard : ∀ i L1 e1, i ≤ rs.length → Inv i L1 e1 →
      evalExpr? config {contract := contract,locals := L1,immutables := immStore v} e1 timeArrayGuard =
        .ok (.bool (decide (i < rs.length))) := by
    rintro i L1 e1 _ ⟨σ1,m,a,j,D,p,ps,vs,records,_,_,_,_,_,hf1,_,_⟩
    simp only [timeArrayGuard,evalExpr?,hf1.index,hf1.length,EvalResult.ofOption,EvalResult.bind,bind,
      evalBinaryOp_lt_int_ok,Int.ofNat_eq_natCast,Nat.cast_lt]
  have hstep : ∀ i L1 e1, i < rs.length → Inv i L1 e1 →
      (∃ L2 e2, ExecBlock fork config {contract := contract,locals := L1,immutables := immStore v} e1 revokeIteration
        (.ok {contract := contract,locals := L2,immutables := immStore v} e2) ∧ Inv (i+1) L2 e2) ∨
      (ExecBlock fork config {contract := contract,locals := L1,immutables := immStore v} e1 revokeIteration .reverted ∧ RDrev fork (deployedRuntime v) g s0) ∨
      (ExecBlock fork config {contract := contract,locals := L1,immutables := immStore v} e1 revokeIteration .staticViolation ∧ RDstatic fork (deployedRuntime v) g s0) := by
    rintro i L1 e1 hi ⟨σ1,m,a,j,D,p,ps,vs,records,hs1,hlo,hhi,hperm,hpre,hf1,hm1,hr1⟩
    have hn : rs.length < UInt256.size := by have := hm1.requests.span; have htop : site.schemaPtr.toNat < UInt256.size := site.schemaPtr.val.isLt; omega
    have hlen := hm1.lengthSite
    obtain ⟨aw1,k1,C1,rd1⟩ := easRevokeLoopTest v site (by omega) (by omega) (by omega) hr1
    rw [if_pos (by omega : i < site.length)] at rd1
    have hrun := revokeIterationRun v site hstack hs1 hf1 hm1 hi rd1
    rcases hrun with ⟨L2,e2,σ2,m2,a2,j2,D2,heap2,at2,hperm2,hlo2,hhi2,hf2,hsol,hstate,hpre2,hm2,hvc2,hr2⟩ | ⟨hsol,hrev⟩ | ⟨hsol,hstatic⟩
    · have hp : (UInt256.ofNat heap2).toNat = heap2 := ulit_toNat' _ (by change heap2 < 2^256; omega)
      refine Or.inl ⟨L2,e2,hsol,σ2,m2,a2,j2,D2,UInt256.ofNat heap2,ps.set i p,vs.set i rs[i].value,
        records.set i at2,hstate,?_,?_,Or.inr ⟨hperm2,by simpa only [List.length_set] using hvc2⟩,hpre.trans hpre2,?_,?_,hr2⟩
      · rw [hp]; omega
      · rw [hp]; exact hhi2
      · simpa only [hp] using hf2
      · simpa only [hp] using hm2
    · exact Or.inr (Or.inl ⟨hsol,hrev⟩)
    · exact Or.inr (Or.inr ⟨hsol,hstatic⟩)
  have hloop := execWhile_invariant (cfg := config) (contract := contract) (imms := immStore v)
    (cond := timeArrayGuard) (body := revokeIteration) (bound := rs.length)
    Inv (Inv rs.length) (RDrev fork (deployedRuntime v) g s0) (RDstatic fork (deployedRuntime v) g s0)
    hguard (fun _ _ h => h) hstep rs.length 0 L evm (by omega)
    ⟨σ,mem,aw,k,C,heap,ptrs,values,ats,hs,le_refl _,hh,Or.inl rfl,MemoryPrefix.refl _ _,hf,hm,rd⟩
  rcases hloop with ⟨L1,e1,hsol,σ1,m,a,j,D,p,ps,vs,records,hstate,hlo,hhi,hperm,hpre,hf1,hm1,hr1⟩ | ⟨hsol,hrev⟩ | ⟨hsol,hstatic⟩
  · have hn : rs.length < UInt256.size := by have := hm1.requests.span; have htop : site.schemaPtr.toNat < UInt256.size := site.schemaPtr.val.isLt; omega
    have hlen := hm1.lengthSite
    obtain ⟨a2,j2,D2,hr2⟩ := easRevokeLoopTest v site (by omega) hn (by omega) hr1
    rw [if_neg (by omega : ¬rs.length < site.length)] at hr2
    have hpermission : rs.length = 0 ∨ ee.perm = true := hperm.elim Or.inl (fun h => Or.inr h.1)
    have hcovered : site.values.toNat+32+32*vs.length ≤ m.size := by
      rcases hperm with hz | hp
      · have hvlen : vs.length = 0 := by have := hm1.lengthValues; have := hm1.lengthRequests; omega
        simpa only [hvlen,Nat.mul_zero,Nat.add_zero] using hm1.valueCovered
      · exact hp.2
    exact Or.inl ⟨L1,e1,σ1,m,a2,j2,D2,p.toNat,ps,records,vs,hlo,hhi,hpermission,hstate,hpre,hf1,hm1,
      hm1.valueArray.reflect (recordPadding_prefix _ _) hcovered p.val.isLt,hsol,hr2⟩
  · exact Or.inr (Or.inl ⟨hsol,hrev⟩)
  · exact Or.inr (Or.inr ⟨hsol,hstatic⟩)

end Benchmarks.EAS.EAS
