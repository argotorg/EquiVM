import Benchmarks.EAS.EAS.MultiAttestReadRun
import Benchmarks.EAS.EAS.MultiAttestCallRun

variable {fork : Ethereum.Fork}
open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables Benchmarks.EAS.EAS.Immutables
namespace Benchmarks.EAS.EAS
set_option maxRecDepth 10000

def MultiAttestAt (fork : Ethereum.Fork) (v : EASImmutables) (ee : ExecutionEnv) (g : Sat256) (s0 : State)
    (n : Nat) (base table : UInt256) (R : List UInt256) (i : Nat) (L : Store) (evm : EVM.State) : Prop :=
  ∃ (σ : AccountMap) (mem out : ByteArray) (aw : UInt256) (k C : Nat)
      (heap available : UInt256) (groups : List (List UInt256)),
    SourceState s0 ee σ evm ∧ heap.toNat ≤ 2^64-1 ∧ groups.length = n ∧
    MultiAttestLocals L (multiRequestValues ee.calldata base n) groups available heap.toNat i ∧
    MultiAttestMemory mem table groups i heap.toNat ∧
    RD fork (deployedRuntime v) ee g s0 ⟨3767⟩
      (multiAttestLoopStack n i base table available (UInt256.ofNat groups.flatten.length) R) mem aw out σ k C

theorem multiAttestIterationRun {L : Store} {evm : EVM.State} {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {n i : Nat} {base table : UInt256} {R : List UInt256}
    (v : EASImmutables) (hstack : R.length+48 ≤ 1024)
    (hsize : ee.calldata.size < 2^255) (hbase : base.toNat+32*n < UInt256.size) (hi : i < n)
    (h : MultiAttestAt fork v ee g s0 n base table R i L evm) :
    (∃ L' evm', ExecBlock fork config {contract := contract,locals := L,immutables := immStore v} evm multiAttestIteration
      (.ok {contract := contract,locals := L',immutables := immStore v} evm') ∧
      MultiAttestAt fork v ee g s0 n base table R (i+1) L' evm') ∨
    (ExecBlock fork config {contract := contract,locals := L,immutables := immStore v} evm multiAttestIteration .reverted ∧
      RDrev fork (deployedRuntime v) g s0) ∨
    (ExecBlock fork config {contract := contract,locals := L,immutables := immStore v} evm multiAttestIteration .staticViolation ∧
      RDstatic fork (deployedRuntime v) g s0) := by
  obtain ⟨σ,mem,out,aw,k,C,heap,available,groups,hstate,hh,hg,hf,hm,rd⟩ := h
  have hn : n < UInt256.size := by omega
  have hlo : 224 ≤ heap.toNat := by have := hm.view.span; have := hm.low; omega
  have hfree : memLoad (UInt256.ofNat 64) mem = heap := by simpa only [u256_ofNat_toNat] using hm.free
  have hread := multiAttestReadRun (evm := evm) v (by omega) hf hi hn (by omega) hsize (by omega) hh hfree rd
  rcases hread with ⟨rs,a1,j1,D1,hd,hrow,hsol1,r1⟩ | ⟨hbad,hrev⟩
  · let L1 := multiAttestCheckedLocals L ee.calldata base n i
    let schema := calldataWord ee.calldata (multiRequestRoot ee.calldata base i).toNat
    change L1.get? "multiRequest" = some (multiRequestTuple schema rs) at hrow
    have hf1 : MultiAttestLocals L1 (multiRequestValues ee.calldata base n) groups available heap.toNat i :=
      hf.read _ _
    have hlast1 : L1.get? "last" = some (.bool (decide (i=n-1))) := by
      simp (disch := decide) only [L1,multiAttestCheckedLocals,multiAttestReadLocals,store_get_ne,store_get_self]
    have heCopy : evalExprs? config {contract := contract,locals := L1,immutables := immStore v} evm multiAttestCopyArgs =
        .ok [.array (rs.map AttestationRequestRecord.tuple),.int (Int.ofNat heap.toNat)] := by
      simp only [multiAttestCopyArgs,evalExprs?,evalExpr?,hrow,hf1.heap,multiRequestTuple,
        EvalResult.ofOption,bind,EvalResult.bind,pure]
      rfl
    have hcopy := requestArrayCopyCallRun (retVar := "allocation$allocation") (ret := ⟨3846⟩)
      (R := multiAttestCopySaved ee n i base table available (UInt256.ofNat groups.flatten.length) R) v
      (by simp only [multiAttestCopySaved,multiAttestSaved,List.length_cons]; omega) heCopy hd (by omega)
      (by omega) hh hfree (by rw [easPatchedValidJumps v]; jump_dest) r1
    rcases hcopy with ⟨m2,a2,j2,D2,next,hlo2,hhi2,hpre2,hdata,hfree2,hcopySol,r2⟩ | ⟨hcopySol,hrev⟩
    · let L2 := multiAttestCopyLocals L1 next
      have hn2 : (UInt256.ofNat next).toNat = next := ulit_toNat' _ (by change next < 2^256; omega)
      have hf2 : MultiAttestLocals L2 (multiRequestValues ee.calldata base n) groups available (UInt256.ofNat next).toNat i := by
        rw [hn2]; exact hf1.copied next
      have hm2 : MultiAttestMemory m2 table groups i (UInt256.ofNat next).toNat := by
        rw [hn2]; exact hm.preserve hpre2 hlo2 (by change next < 2^256; omega) hfree2
      have hrow2 : L2.get? "multiRequest" = some (multiRequestTuple schema rs) :=
        (heapResultLocals_get _ _ _ _ _ _ _ (by decide) (by decide) (by decide)).trans hrow
      have hlast2 : L2.get? "last" = some (.bool (decide (i=n-1))) :=
        (heapResultLocals_get _ _ _ _ _ _ _ (by decide) (by decide) (by decide)).trans hlast1
      have hd2 : AttestationRequestArrayRegion m2 heap rs 224 (UInt256.ofNat next).toNat := by
        rw [hn2]
        refine ⟨hdata.view,by omega,?_⟩
        intro j hj
        have hlow := hdata.objectsLow j hj
        omega
      have hsol2 : ExecBlock fork config {contract := contract,locals := L1,immutables := immStore v} evm multiAttestCopy
          (.ok {contract := contract,locals := L2,immutables := immStore v} evm) :=
        heapResultBlock_ok hcopySol hf1.heap (by decide) (by decide) (by decide)
      have hfront := execBlock_append hsol1 hsol2
      obtain ⟨a3,j3,D3,r3⟩ := easMultiAttestCall v (by omega) r2
      have hcall := multiAttestCallUpdateRun v hstack hstate hf2 hm2 (by rw [hn2]; exact hhi2)
        hi hn hg hrow2 hlast2 hd2 (by change ee.calldata.size < 2^256; omega) r3
      rcases hcall with ⟨L4,e4,σ4,m4,out4,a4,j4,D4,heap4,words,used,hs4,_,hh4,hf4,hm4,hsol4,r4⟩ |
        ⟨hbad,hrev⟩ | ⟨hbad,hstatic⟩
      · have hn4 : (UInt256.ofNat heap4).toNat = heap4 := ulit_toNat' _ (by change heap4 < 2^256; omega)
        refine Or.inl ⟨L4,e4,?_,σ4,m4,out4,a4,j4,D4,UInt256.ofNat heap4,UInt256.sub available used,
          groups.set i words,hs4,by rw [hn4]; exact hh4,by simpa only [List.length_set] using hg,?_,?_,r4⟩
        · simpa only [multiAttestIteration,List.append_assoc] using execBlock_append hfront hsol4
        · rw [hn4]; exact hf4
        · rw [hn4]; exact hm4
      · refine Or.inr (Or.inl ⟨?_,hrev⟩)
        simpa only [multiAttestIteration,List.append_assoc] using execBlock_append hfront hbad
      · refine Or.inr (Or.inr ⟨?_,hstatic⟩)
        simpa only [multiAttestIteration,List.append_assoc] using execBlock_append hfront hbad
    · have hb : ExecBlock fork config {contract := contract,locals := L1,immutables := immStore v} evm multiAttestCopy .reverted :=
        ExecBlock.consRevert hcopySol
      refine Or.inr (Or.inl ⟨?_,hrev⟩)
      simpa only [multiAttestIteration,List.append_assoc] using execBlock_append hsol1
        (execBlock_append_term (s2 := multiAttestCall++multiAttestUpdate) hb (by intros; exact nofun))
  · refine Or.inr (Or.inl ⟨?_,hrev⟩)
    simpa only [multiAttestIteration,List.append_assoc] using
      execBlock_append_term (s2 := multiAttestCopy++multiAttestCall++multiAttestUpdate) hbad (by intros; exact nofun)

end Benchmarks.EAS.EAS
