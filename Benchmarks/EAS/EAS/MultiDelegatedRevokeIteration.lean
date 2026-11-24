import Benchmarks.EAS.EAS.MultiDelegatedRevokePrepareRun
import Benchmarks.EAS.EAS.MultiDelegatedRevokeVerifyLoop
import Benchmarks.EAS.EAS.MultiDelegatedRevokeCallRun

variable {fork : Ethereum.Fork}
open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables Benchmarks.EAS.EAS.Immutables
namespace Benchmarks.EAS.EAS
set_option maxRecDepth 10000

def MultiDelegatedRevokeAt (fork : Ethereum.Fork) (v : EASImmutables) (ee : ExecutionEnv) (g : Sat256) (s0 : State)
    (n : Nat) (base tag : UInt256) (R : List UInt256) (i : Nat) (L : Store) (evm : EVM.State) : Prop :=
  ∃ (σ : AccountMap) (mem out : ByteArray) (aw : UInt256) (k C : Nat) (heap available : UInt256),
    SourceState s0 ee σ evm ∧ 224 ≤ heap.toNat ∧ heap.toNat ≤ 2^64-1 ∧
    MultiDelegatedRevokeLocals L (delegatedBatchValues .revoke ee.calldata base n) available heap.toNat i ∧
    96 ≤ mem.size ∧ memLoad (UInt256.ofNat 64) mem = heap ∧
    memLoad (UInt256.ofNat 96) (recordPadding mem heap.toNat) = ⟨0⟩ ∧
    RD fork (deployedRuntime v) ee g s0 ⟨1298⟩ (multiDelegatedRevokeLoopStack n i base available (tag::R)) mem aw out σ k C

theorem multiDelegatedRevokeIterationRun {L : Store} {evm : EVM.State} {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {n i : Nat} {base tag : UInt256} {R : List UInt256}
    (v : EASImmutables) (hstack : R.length+52 ≤ 1024)
    (hsize : ee.calldata.size < 2^255) (hbase : base.toNat+32*n < UInt256.size) (hi : i<n)
    (h : MultiDelegatedRevokeAt fork v ee g s0 n base tag R i L evm) :
    (∃ L' evm', ExecBlock fork config {contract := contract,locals := L,immutables := immStore v} evm multiDelegatedRevokeIteration
      (.ok {contract := contract,locals := L',immutables := immStore v} evm') ∧
      MultiDelegatedRevokeAt fork v ee g s0 n base tag R (i+1) L' evm') ∨
    (ExecBlock fork config {contract := contract,locals := L,immutables := immStore v} evm multiDelegatedRevokeIteration .reverted ∧
      RDrev fork (deployedRuntime v) g s0) ∨
    (ExecBlock fork config {contract := contract,locals := L,immutables := immStore v} evm multiDelegatedRevokeIteration .staticViolation ∧
      RDstatic fork (deployedRuntime v) g s0) := by
  obtain ⟨σ,mem,out,aw,k,C,heap,available,hstate,hlo,hh,hf,hmem,hfree,hzero,rd⟩ := h
  have hn : n<UInt256.size := by omega
  have hprep := multiDelegatedRevokePrepareRun (evm := evm) v (by omega) hf hi hn (by omega)
    hsize (by omega) hh hmem hfree rd
  rcases hprep with ⟨r,L1,mem1,a1,k1,C1,hh1,hguard,hsol1,hf1,hp1,hv1,hfree1,r1⟩ | ⟨hbad,hrev⟩
  · let next := delegatedRevocationNext heap r
    have hn1 : (UInt256.ofNat next).toNat=next := ulit_toNat' _ (by change next<2^256; dsimp only [next]; omega)
    have hmin : heap.toNat ≤ next := by dsimp only [next,delegatedRevocationNext]; omega
    have hm1 : 128 ≤ mem1.size := by have := hv1.covered; omega
    have hz1 : memLoad (UInt256.ofNat 96) mem1 = ⟨0⟩ :=
      (memLoad_of_prefix hp1 (UInt256.ofNat 96) (by decide) (by change 128 ≤ heap.toNat; omega)
        (by have := recordPadding_covers mem heap.toNat; change 128 ≤ _; omega)).trans hzero
    have hverify : MultiDelegatedRevokeVerifyAt fork v ee g s0 (delegatedBatchValues .revoke ee.calldata base n)
        r n i base available heap (delegatedRevocationDataPtr heap) (delegatedRevocationSigPtr heap r.data)
        mem1 next (UInt256.ofNat i::tag::R) 0 L1 evm := by
      refine ⟨σ,mem1,out,a1,k1,C1,UInt256.ofNat next,hstate,by rw [hn1],by rw [hn1]; exact hh1,
        MemoryPrefix.refl _ _,?_,?_,hfree1,r1⟩
      · rw [hn1]; exact hf1
      · rw [hn1]; exact hv1
    rcases multiDelegatedRevokeVerifyLoopRun v (by simp only [List.length_cons]; omega) hguard.2 hverify with
      ⟨L2,e2,hsol2,h2⟩ | ⟨hbad,hrev⟩ | ⟨hbad,hstatic⟩
    · obtain ⟨σ2,mem2,out2,a2,k2,C2,heap2,hs2,hlo2,hh2,hp2,hf2,hv2,hfree2,r2⟩ := h2
      have hm2 : 128 ≤ mem2.size := le_trans hm1 hp2.size
      have hz2 : memLoad (UInt256.ofNat 96) mem2 = ⟨0⟩ :=
        (memLoad_of_prefix hp2 (UInt256.ofNat 96) (by decide) (by change 128 ≤ next; omega) hm1).trans hz1
      have hfront := execBlock_append hsol1 (ExecBlock.consNormal hsol2 ExecBlock.nil)
      rcases multiDelegatedRevokeCallRun v (by simp only [List.length_cons]; omega) hs2 hf2 hv2 hi hn hh2 hfree2 hz2
        (by change ee.calldata.size < 2^256; omega) r2 with
        ⟨L3,e3,σ3,mem3,out3,a3,k3,C3,heap3,used,hs3,hlo3,hh3,hp3,hf3,hfree3,hsol3,r3⟩ | ⟨hbad,hrev⟩ | ⟨hbad,hstatic⟩
      · have hn3 : (UInt256.ofNat heap3).toNat=heap3 := ulit_toNat' _ (by change heap3<2^256; omega)
        have hm3 : 128 ≤ mem3.size := le_trans hm2 hp3.size
        have hz3 : memLoad (UInt256.ofNat 96) mem3 = ⟨0⟩ :=
          (memLoad_of_prefix hp3 (UInt256.ofNat 96) (by decide) (by change 128 ≤ heap2.toNat; omega) hm2).trans hz2
        refine Or.inl ⟨L3,e3,?_,σ3,mem3,out3,a3,k3,C3,UInt256.ofNat heap3,UInt256.sub available used,
          hs3,by rw [hn3]; omega,by rw [hn3]; exact hh3,?_,by omega,hfree3,?_,r3⟩
        · simpa only [multiDelegatedRevokeIteration,multiDelegatedRevokeVerifyLoop,List.append_assoc] using
            execBlock_append hfront hsol3
        · rw [hn3]; exact hf3
        · rw [hn3]
          exact (memLoad_of_prefix (recordPadding_prefix mem3 heap3) (UInt256.ofNat 96) (by decide)
            (by change 128 ≤ heap3; omega) hm3).trans hz3
      · refine Or.inr (Or.inl ⟨?_,hrev⟩)
        simpa only [multiDelegatedRevokeIteration,multiDelegatedRevokeVerifyLoop,List.append_assoc] using execBlock_append hfront hbad
      · refine Or.inr (Or.inr ⟨?_,hstatic⟩)
        simpa only [multiDelegatedRevokeIteration,multiDelegatedRevokeVerifyLoop,List.append_assoc] using execBlock_append hfront hbad
    · refine Or.inr (Or.inl ⟨?_,hrev⟩)
      simpa only [multiDelegatedRevokeIteration,multiDelegatedRevokeVerifyLoop,List.append_assoc] using
        execBlock_append hsol1 (ExecBlock.consRevert (stmts := multiDelegatedRevokeCall++multiDelegatedRevokeUpdate) hbad)
    · refine Or.inr (Or.inr ⟨?_,hstatic⟩)
      simpa only [multiDelegatedRevokeIteration,multiDelegatedRevokeVerifyLoop,List.append_assoc] using
        execBlock_append hsol1 (ExecBlock.consStatic (stmts := multiDelegatedRevokeCall++multiDelegatedRevokeUpdate) hbad)
  · refine Or.inr (Or.inl ⟨?_,hrev⟩)
    simpa only [multiDelegatedRevokeIteration,List.append_assoc] using execBlock_append_term
      (s2 := [.while (localArrayGuard "j" "data") multiDelegatedRevokeVerifyIteration]++multiDelegatedRevokeCall++multiDelegatedRevokeUpdate)
      hbad (by intros; exact nofun)

end Benchmarks.EAS.EAS
