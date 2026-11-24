import Benchmarks.EAS.EAS.AttestLoopStep
import Benchmarks.EAS.EAS.WhileInvariant
import Benchmarks.EAS.EAS.TimeArray

variable {fork : Ethereum.Fork}
open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables Benchmarks.EAS.EAS.Immutables
namespace Benchmarks.EAS.EAS

def attestLoopStmt : Stmt := .while timeArrayGuard attestIteration

theorem attestLoopStmt_eq : attestFunction.body[26]! = attestLoopStmt := by native_decide

theorem attestLoopRun {L : Store} {evm : EVM.State} {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : Nat}
    {heap schema t3 t4 uidPtr available used : UInt256} {attester : AccountAddress} {last : Bool}
    {rs : List AttestationRequestRecord} {s : SchemaRecord} {ats : List AttestationRecord} {ptrs values uids R : List UInt256}
    (v : EASImmutables) (site : UIDSite) (hstack : R.length+34 ≤ 1024) (hs : SourceState s0 ee σ evm)
    (hf : AttestLoopLocals L rs s schema attester available last ats values uids used 0 heap.toNat)
    (hm : AttestLoopMemory mem site t3 t4 uidPtr rs s attester ptrs values uids ats heap.toNat)
    (hh : heap.toNat ≤ 2^64-1) (hreglen : attestLoopLength site = UInt256.ofNat rs.length)
    (rd : RD fork (deployedRuntime v) ee g s0 (recordNextPC site)
      (recordNextStack site schema (UInt256.ofNat 0) t3 t4 R) mem aw rdata σ k C) :
    (∃ L' evm' σ' mem' aw' k' C' heap' ptrs' ats' values' uids',
      heap.toNat ≤ heap' ∧ heap' ≤ 2^64-1 ∧ (rs.length = 0 ∨ ee.perm = true) ∧ SourceState s0 ee σ' evm' ∧ MemoryPrefix mem mem' uidPtr.toNat ∧
      AttestLoopLocals L' rs s schema attester available last ats' values' uids' used rs.length heap' ∧
      AttestLoopMemory mem' site t3 t4 uidPtr rs s attester ptrs' values' uids' ats' heap' ∧
      WordArrayMemoryView mem' (recordValuesPtr site t4) values' heap' ∧
      ExecStmt fork config {contract := contract,locals := L,immutables := immStore v} evm attestLoopStmt
        (.ok {contract := contract,locals := L',immutables := immStore v} evm') ∧
      RD fork (deployedRuntime v) ee g s0 (attestLoopExitPC site)
        (recordNextStack site schema (UInt256.ofNat rs.length) t3 t4 R) mem' aw' rdata σ' k' C') ∨
    (ExecStmt fork config {contract := contract,locals := L,immutables := immStore v} evm attestLoopStmt .reverted ∧
      RDrev fork (deployedRuntime v) g s0) ∨
    (ExecStmt fork config {contract := contract,locals := L,immutables := immStore v} evm attestLoopStmt .staticViolation ∧
      RDstatic fork (deployedRuntime v) g s0) := by
  let Inv := fun i L1 e1 => ∃ (σ1 : AccountMap) (m : ByteArray) (a : UInt256) (j D : Nat) (p : UInt256)
      (ps vs us : List UInt256) (records : List AttestationRecord),
    SourceState s0 ee σ1 e1 ∧ heap.toNat ≤ p.toNat ∧ p.toNat ≤ 2^64-1 ∧ (i = 0 ∨ (ee.perm = true ∧ (recordValuesPtr site t4).toNat+32+32*vs.length ≤ m.size)) ∧ MemoryPrefix mem m uidPtr.toNat ∧
    AttestLoopLocals L1 rs s schema attester available last records vs us used i p.toNat ∧
    AttestLoopMemory m site t3 t4 uidPtr rs s attester ps vs us records p.toNat ∧
    RD fork (deployedRuntime v) ee g s0 (recordNextPC site)
      (recordNextStack site schema (UInt256.ofNat i) t3 t4 R) m a rdata σ1 j D
  have hguard : ∀ i L1 e1, i ≤ rs.length → Inv i L1 e1 →
      evalExpr? config {contract := contract,locals := L1,immutables := immStore v} e1 timeArrayGuard =
        .ok (.bool (decide (i < rs.length))) := by
    rintro i L1 e1 _ ⟨σ1,m,a,j,D,p,ps,vs,us,records,_,_,_,_,_,hf1,_,_⟩
    simp only [timeArrayGuard,evalExpr?,hf1.index,hf1.length,EvalResult.ofOption,EvalResult.bind,bind,
      evalBinaryOp_lt_int_ok,Int.ofNat_eq_natCast,Nat.cast_lt]
  have hstep : ∀ i L1 e1, i < rs.length → Inv i L1 e1 →
      (∃ L2 e2, ExecBlock fork config {contract := contract,locals := L1,immutables := immStore v} e1 attestIteration
        (.ok {contract := contract,locals := L2,immutables := immStore v} e2) ∧ Inv (i+1) L2 e2) ∨
      (ExecBlock fork config {contract := contract,locals := L1,immutables := immStore v} e1 attestIteration .reverted ∧ RDrev fork (deployedRuntime v) g s0) ∨
      (ExecBlock fork config {contract := contract,locals := L1,immutables := immStore v} e1 attestIteration .staticViolation ∧ RDstatic fork (deployedRuntime v) g s0) := by
    rintro i L1 e1 hi ⟨σ1,m,a,j,D,p,ps,vs,us,records,hs1,hlo,hhi,hperm,hpre,hf1,hm1,hr1⟩
    have hrun := attestLoopStep v site hstack hs1 hf1 hm1 hi hhi hreglen hr1
    rcases hrun with ⟨L2,e2,σ2,m2,a2,j2,D2,heap2,word,hperm2,hlo2,hhi2,hf2,hsol,hstate,hpre2,hm2,hvc2,hr2⟩ | ⟨hsol,hrev⟩ | ⟨hsol,hstatic⟩
    · have hn : (UInt256.ofNat heap2).toNat = heap2 := ulit_toNat' _ (by change heap2 < 2^256; omega)
      refine Or.inl ⟨L2,e2,hsol,σ2,m2,a2,j2,D2,UInt256.ofNat heap2,
        ps.set i p,vs.set i rs[i].value,us.set i word,
        records.set i {newAttestation rs[i] schema (easTimeWord ee) attester with uid := word},
        hstate,?_,?_,Or.inr ⟨hperm2,by simpa only [List.length_set] using hvc2⟩,hpre.trans hpre2,?_,?_,hr2⟩
      · rw [hn]; omega
      · rw [hn]; exact hhi2
      · simpa only [hn] using hf2
      · simpa only [hn] using hm2
    · exact Or.inr (Or.inl ⟨hsol,hrev⟩)
    · exact Or.inr (Or.inr ⟨hsol,hstatic⟩)
  have hloop := execWhile_invariant (cfg := config) (contract := contract) (imms := immStore v)
    (cond := timeArrayGuard) (body := attestIteration) (bound := rs.length)
    Inv (Inv rs.length) (RDrev fork (deployedRuntime v) g s0) (RDstatic fork (deployedRuntime v) g s0)
    hguard (fun _ _ h => h) hstep rs.length 0 L evm (by omega)
    ⟨σ,mem,aw,k,C,heap,ptrs,values,uids,ats,hs,le_refl _,hh,Or.inl rfl,MemoryPrefix.refl _ _,hf,hm,rd⟩
  rcases hloop with ⟨L1,e1,hsol,σ1,m,a,j,D,p,ps,vs,us,records,hstate,hlo,hhi,hperm,hpre,hf1,hm1,hr1⟩ | ⟨hsol,hrev⟩ | ⟨hsol,hstatic⟩
  · obtain ⟨a2,j2,D2,hr2⟩ := easAttestLoopTest v site (by omega) hr1
    rw [if_neg (by rw [hreglen]; exact Nat.lt_irrefl _)] at hr2
    have hpermission : rs.length = 0 ∨ ee.perm = true := hperm.elim Or.inl (fun h => Or.inr h.1)
    have hcovered : (recordValuesPtr site t4).toNat+32+32*vs.length ≤ m.size := by
      rcases hperm with hz | hp
      · have hvlen : vs.length = 0 := by have := hm1.lengthValues; have := hm1.lengthRequests; omega
        simpa only [hvlen,Nat.mul_zero,Nat.add_zero] using hm1.valueCovered
      · exact hp.2
    exact Or.inl ⟨L1,e1,σ1,m,a2,j2,D2,p.toNat,ps,records,vs,us,hlo,hhi,hpermission,hstate,hpre,hf1,hm1,
      hm1.valueArray.reflect (recordPadding_prefix _ _) hcovered p.val.isLt,hsol,hr2⟩
  · exact Or.inr (Or.inl ⟨hsol,hrev⟩)
  · exact Or.inr (Or.inr ⟨hsol,hstatic⟩)

end Benchmarks.EAS.EAS
