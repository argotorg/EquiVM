import Benchmarks.EAS.EAS.MultiDelegatedAttestPrepareRun
import Benchmarks.EAS.EAS.MultiDelegatedAttestVerifyLoop
import Benchmarks.EAS.EAS.MultiDelegatedAttestCopyRun
import Benchmarks.EAS.EAS.MultiDelegatedAttestCallRun

variable {fork : Ethereum.Fork}
open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables Benchmarks.EAS.EAS.Immutables
namespace Benchmarks.EAS.EAS
set_option maxRecDepth 10000

def MultiDelegatedAttestAt (fork : Ethereum.Fork) (v : EASImmutables) (ee : ExecutionEnv) (g : Sat256) (s0 : State)
    (n : Nat) (base table : UInt256) (R : List UInt256) (i : Nat) (L : Store) (evm : EVM.State) : Prop :=
  ∃ (σ : AccountMap) (mem out : ByteArray) (aw : UInt256) (k C : Nat)
      (heap available : UInt256) (groups : List (List UInt256)),
    SourceState s0 ee σ evm ∧ heap.toNat≤2^64-1 ∧ groups.length=n ∧
    MultiDelegatedAttestLocals L (delegatedBatchValues .attest ee.calldata base n) groups available heap.toNat i ∧
    MultiAttestMemory mem table groups i heap.toNat ∧
    RD fork (deployedRuntime v) ee g s0 ⟨2777⟩
      (multiDelegatedAttestLoopStack n i base available (UInt256.ofNat groups.flatten.length) table R) mem aw out σ k C

theorem multiDelegatedAttestIterationRun {L : Store} {evm : EVM.State} {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {n i : Nat} {base table : UInt256} {R : List UInt256}
    (v : EASImmutables) (hstack : R.length+50≤1024)
    (hsize : ee.calldata.size<2^255) (hbase : base.toNat+32*n<UInt256.size)
    (hbaseEq : base=checkAttestationCopyBase ee.calldata) (hi : i<n)
    (h : MultiDelegatedAttestAt fork v ee g s0 n base table R i L evm) :
    (∃ L' evm', ExecBlock fork config {contract := contract,locals := L,immutables := immStore v} evm multiDelegatedAttestIteration
      (.ok {contract := contract,locals := L',immutables := immStore v} evm') ∧
      MultiDelegatedAttestAt fork v ee g s0 n base table R (i+1) L' evm') ∨
    (ExecBlock fork config {contract := contract,locals := L,immutables := immStore v} evm multiDelegatedAttestIteration .reverted ∧
      RDrev fork (deployedRuntime v) g s0) ∨
    (ExecBlock fork config {contract := contract,locals := L,immutables := immStore v} evm multiDelegatedAttestIteration .staticViolation ∧
      RDstatic fork (deployedRuntime v) g s0) := by
  obtain ⟨σ,mem,out,aw,k,C,heap,available,groups,hstate,hh,hg,hf,hm,rd⟩ := h
  have hn : n<UInt256.size := by omega
  have hlo : 224≤heap.toNat := by have := hm.view.span;have := hm.low;omega
  have hfree : memLoad (UInt256.ofNat 64) mem=heap := by simpa only [u256_ofNat_toNat] using hm.free
  have hread := multiDelegatedAttestPrepareRun (evm := evm) v (by omega) hf hi hn (by omega) rd
  rcases hread with ⟨L1,a1,k1,C1,hbatch,hs1,hf1,r1⟩ | ⟨hs1,hrev⟩
  · let root := multiRequestRoot ee.calldata base i
    have hv0 : MultiDelegatedAttestVerifyAt fork v ee g s0 (delegatedBatchValues .attest ee.calldata base n) groups n i base available table root
        mem heap.toNat R 0 L1 evm := by
      exact ⟨σ,mem,out,a1,k1,C1,heap,hstate,le_refl _,hh,MemoryPrefix.refl _ _,hf1,
        by intros;omega,by have := hm.view.covered;have := hm.view.span;have := hm.low;omega,hfree,r1⟩
    have hverify := multiDelegatedAttestVerifyLoopRun v (by omega) hsize (by omega) hbatch hv0
    rcases hverify with ⟨L2,e2,hs2,hv2⟩ | ⟨hs2,hrev⟩ | ⟨hs2,hstatic⟩
    · obtain ⟨σ2,m2,out2,a2,k2,C2,heap2,hstate2,hlo2,hh2,hp2,hf2,hgood2,hmSize2,hfree2,r2⟩ := hv2
      have hm2 : MultiAttestMemory m2 table groups i heap2.toNat := hm.preserve hp2 hlo2 (by change heap2.toNat<2^256;omega) (by simpa only [u256_ofNat_toNat] using hfree2)
      have hfront := execBlock_append hs1 (ExecBlock.consNormal hs2 ExecBlock.nil)
      have hcopy := multiDelegatedAttestCopyRun v (by omega) hstate2 hsize hbaseEq rfl (by omega) hbatch hf2 hgood2 (by omega) hh2 hfree2 r2
      rcases hcopy with ⟨L3,m3,a3,k3,C3,next,hlo3,hh3,hp3,hd3,hfree3,hs3,hf3,r3⟩ | ⟨hs3,hrev⟩
      · have hn3 : (UInt256.ofNat next).toNat=next := ulit_toNat' _ (by change next<2^256;omega)
        have hm3 : MultiAttestMemory m3 table groups i (UInt256.ofNat next).toNat := by
          rw [hn3];exact hm2.preserve hp3 hlo3 (by change next<2^256;omega) hfree3
        have hdata3 : L3.get? "data"=some (.array ((delegatedAttestationRecords ee.calldata root).map AttestationRequestRecord.tuple)) := by
          rw [hf3.data,delegatedAttestationDataList_verified (hbatch.bounds hsize).2.1 (fun t ht => (hgood2 t ht).1)]
        have hd3' : AttestationRequestArrayRegion m3 heap2 (delegatedAttestationRecords ee.calldata root) 224 (UInt256.ofNat next).toNat := by
          rw [hn3]
          refine ⟨hd3.view,by omega,?_⟩
          intro t ht
          have := hd3.objectsLow t ht
          omega
        obtain ⟨a4,k4,C4,r4⟩ := easBlocks.eas_block_3125_packed (immWords := wordsOf (immStore v))
          (by simp only [multiDelegatedAttestCopySaved,multiDelegatedAttestSaved,List.length_cons,List.length_append,List.length_nil];omega)
          (by rw [easPatchedValidJumpsRuntime v];jump_dest) r3
        have hcall := multiDelegatedAttestCallUpdateRun v (by omega) hstate2
          (by rw [hn3];exact hf3.outer) hm3 (by rw [hn3];exact hh3) hi hn hg hf3.request hdata3 (hgood2 0 hbatch.nonempty).2 hf3.last
          hd3' (by change ee.calldata.size<2^256;omega) r4
        rcases hcall with ⟨L4,e4,σ4,m4,out4,a5,k5,C5,heap4,words,used,hs4,hlo4,hh4,hf4,hm4,hsCall,r5⟩ |
          ⟨hsCall,hrev⟩ | ⟨hsCall,hstatic⟩
        · have hn4 : (UInt256.ofNat heap4).toNat=heap4 := ulit_toNat' _ (by change heap4<2^256;omega)
          refine Or.inl ⟨L4,e4,?_,σ4,m4,out4,a5,k5,C5,UInt256.ofNat heap4,UInt256.sub available used,groups.set i words,
            hs4,by rw [hn4];exact hh4,by simpa only [List.length_set] using hg,?_,?_,r5⟩
          · simpa only [multiDelegatedAttestIteration,multiDelegatedAttestVerifyLoop,List.append_assoc] using
              execBlock_append hfront (execBlock_append hs3 hsCall)
          · rw [hn4];exact hf4
          · rw [hn4];exact hm4
        · refine Or.inr (Or.inl ⟨?_,hrev⟩)
          simpa only [multiDelegatedAttestIteration,multiDelegatedAttestVerifyLoop,List.append_assoc] using execBlock_append hfront (execBlock_append hs3 hsCall)
        · refine Or.inr (Or.inr ⟨?_,hstatic⟩)
          simpa only [multiDelegatedAttestIteration,multiDelegatedAttestVerifyLoop,List.append_assoc] using execBlock_append hfront (execBlock_append hs3 hsCall)
      · refine Or.inr (Or.inl ⟨?_,hrev⟩)
        simpa only [multiDelegatedAttestIteration,multiDelegatedAttestVerifyLoop,List.append_assoc] using execBlock_append hfront
          (execBlock_append_term (s2 := multiDelegatedAttestCall++multiAttestUpdate) hs3 (by intros;exact nofun))
    · refine Or.inr (Or.inl ⟨?_,hrev⟩)
      simpa only [multiDelegatedAttestIteration,multiDelegatedAttestVerifyLoop,List.append_assoc] using execBlock_append hs1
        (ExecBlock.consRevert (stmts := multiDelegatedAttestCopyCheck++multiDelegatedAttestArrayCopy++multiDelegatedAttestCall++multiAttestUpdate) hs2)
    · refine Or.inr (Or.inr ⟨?_,hstatic⟩)
      simpa only [multiDelegatedAttestIteration,multiDelegatedAttestVerifyLoop,List.append_assoc] using execBlock_append hs1
        (ExecBlock.consStatic (stmts := multiDelegatedAttestCopyCheck++multiDelegatedAttestArrayCopy++multiDelegatedAttestCall++multiAttestUpdate) hs2)
  · refine Or.inr (Or.inl ⟨?_,hrev⟩)
    simpa only [multiDelegatedAttestIteration,List.append_assoc] using
      execBlock_append_term (s2 := [.while (localArrayGuard "j" "data") multiDelegatedAttestVerifyIteration]++multiDelegatedAttestCopyCheck++multiDelegatedAttestArrayCopy++multiDelegatedAttestCall++multiAttestUpdate) hs1 (by intros;exact nofun)

end Benchmarks.EAS.EAS
