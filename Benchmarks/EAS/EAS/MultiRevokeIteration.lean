import Benchmarks.EAS.EAS.MultiRevokeReadRun
import Benchmarks.EAS.EAS.MultiRevokeCallRun
import Benchmarks.EAS.EAS.CopyRevocationArrayRun

variable {fork : Ethereum.Fork}
open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables Benchmarks.EAS.EAS.Immutables
namespace Benchmarks.EAS.EAS
set_option maxRecDepth 10000

def MultiRevokeAt (fork : Ethereum.Fork) (v : EASImmutables) (ee : ExecutionEnv) (g : Sat256) (s0 : State)
    (n : Nat) (base : UInt256) (R : List UInt256) (i : Nat) (L : Store) (evm : EVM.State) : Prop :=
  ∃ (σ : AccountMap) (mem out : ByteArray) (aw : UInt256) (k C : Nat) (heap available : UInt256),
    SourceState s0 ee σ evm ∧ 224 ≤ heap.toNat ∧ heap.toNat ≤ 2^64-1 ∧
    MultiRevokeLocals L (multiRevocationValues ee.calldata base n) available heap.toNat i ∧
    96 ≤ mem.size ∧ memLoad (UInt256.ofNat 64) mem = heap ∧
    memLoad (UInt256.ofNat 96) (recordPadding mem heap.toNat) = ⟨0⟩ ∧
    RD fork (deployedRuntime v) ee g s0 ⟨3396⟩ (multiRevokeLoopStack n i base available R) mem aw out σ k C

theorem multiRevokeIterationRun {L : Store} {evm : EVM.State} {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {n i : Nat} {base : UInt256} {R : List UInt256}
    (v : EASImmutables) (hstack : R.length+48 ≤ 1024)
    (hsize : ee.calldata.size < 2^255) (hbase : base.toNat+32*n < UInt256.size) (hi : i<n)
    (h : MultiRevokeAt fork v ee g s0 n base R i L evm) :
    (∃ L' evm', ExecBlock fork config {contract := contract,locals := L,immutables := immStore v} evm multiRevokeIteration
      (.ok {contract := contract,locals := L',immutables := immStore v} evm') ∧
      MultiRevokeAt fork v ee g s0 n base R (i+1) L' evm') ∨
    (ExecBlock fork config {contract := contract,locals := L,immutables := immStore v} evm multiRevokeIteration .reverted ∧
      RDrev fork (deployedRuntime v) g s0) ∨
    (ExecBlock fork config {contract := contract,locals := L,immutables := immStore v} evm multiRevokeIteration .staticViolation ∧
      RDstatic fork (deployedRuntime v) g s0) := by
  obtain ⟨σ,mem,out,aw,k,C,heap,available,hstate,hlo,hh,hf,hmem,hfree,hzero,rd⟩ := h
  have hn : n<UInt256.size := by omega
  have hread := multiRevokeReadRun (evm := evm) v (by omega) hf hi hn (by omega) hsize hfree rd
  rcases hread with ⟨rs,a1,k1,C1,hd,hrow,hsol1,r1⟩ | ⟨hbad,hrev⟩
  · let L1 := multiRevokeCheckedLocals L ee.calldata base n i
    let schema := calldataWord ee.calldata (multiRequestRoot ee.calldata base i).toNat
    change L1.get? "multiRequest" = some (multiRevocationTuple schema rs) at hrow
    have hf1 : MultiRevokeLocals L1 (multiRevocationValues ee.calldata base n) available heap.toNat i := hf.read _ _
    have hlast1 : L1.get? "last" = some (.bool (decide (i=n-1))) := by
      simp (disch := decide) only [L1,multiRevokeCheckedLocals,multiAttestReadLocals,store_get_ne,store_get_self]
    obtain ⟨hvalid,hlen,hc⟩ := decodeRevocationArray_facts (by omega) hd
    have hl : rs.length ≤ 2^64-1 := by rw [hlen]; exact hvalid.1
    have hlenw : calldataWord ee.calldata (multiRequestArray ee.calldata (multiRequestRoot ee.calldata base i)).toNat =
        UInt256.ofNat rs.length := by rw [hlen,u256_ofNat_toNat]
    rw [hlenw] at r1
    have hcopy := copyRevocationArrayRun v (by simp only [multiRevokeCopySaved,multiRevokeSaved,List.length_cons]; omega)
      hc hsize hl (by omega) hh hfree hmem (by rw [easPatchedValidJumps v]; jump_dest) r1
    have hsol2 := multiRevokeAllocateSource (fork := fork) (imms := immStore v) (evm := evm) hrow hf1.heap hl hh
    let next := heap.toNat+32+96*rs.length
    by_cases hg : next ≤ 2^64-1
    · rw [if_pos hg] at hcopy hsol2
      obtain ⟨m2,a2,k2,C2,hpre2,hdata,hfree2,r2⟩ := hcopy
      let L2 := multiRevokeAllocatedLocals L1 rs next
      have hn2 : (UInt256.ofNat next).toNat = next := ulit_toNat' _ (by change next < 2^256; omega)
      have hf2 : MultiRevokeLocals L2 (multiRevocationValues ee.calldata base n) available (UInt256.ofNat next).toNat i := by
        rw [hn2]; exact hf1.allocated rs next
      have hrow2 : L2.get? "multiRequest" = some (multiRevocationTuple schema rs) := by
        simpa (disch := decide) only [L2,multiRevokeAllocatedLocals,allocateBlockLocals_get,store_get_ne] using hrow
      have hlast2 : L2.get? "last" = some (.bool (decide (i=n-1))) := by
        simpa (disch := decide) only [L2,multiRevokeAllocatedLocals,allocateBlockLocals_get,store_get_ne] using hlast1
      have hd2 : RevocationRequestArrayMemoryView m2 heap rs (UInt256.ofNat next).toNat := by rw [hn2]; exact hdata
      have hz2 : memLoad (UInt256.ofNat 96) m2 = ⟨0⟩ :=
        (memLoad_of_prefix hpre2 (UInt256.ofNat 96) (by decide) (by change 128 ≤ heap.toNat; omega)
          (by have := recordPadding_covers mem heap.toNat; change 128 ≤ _; omega)).trans hzero
      have hfront := execBlock_append hsol1 hsol2
      obtain ⟨a3,k3,C3,r3⟩ := easMultiRevokeCall v (by omega) r2
      have hcall := multiRevokeCallUpdateRun v hstack hstate hf2 (by rw [hn2]; exact hg)
        hi hn hrow2 hlast2 hd2 hfree2 hz2 (by change ee.calldata.size < 2^256; omega) r3
      rcases hcall with ⟨L4,e4,σ4,m4,out4,a4,k4,C4,heap4,used,hs4,hlo4,hh4,hf4,hm4,hfree4,hzero4,hsol4,r4⟩ |
        ⟨hbad,hrev⟩ | ⟨hbad,hstatic⟩
      · have hn4 : (UInt256.ofNat heap4).toNat = heap4 := ulit_toNat' _ (by change heap4 < 2^256; omega)
        rw [hn2] at hlo4
        refine Or.inl ⟨L4,e4,?_,σ4,m4,out4,a4,k4,C4,UInt256.ofNat heap4,UInt256.sub available used,
          hs4,by rw [hn4]; dsimp only [next] at hlo4; omega,by rw [hn4]; exact hh4,?_,by omega,hfree4,?_,r4⟩
        · simpa only [multiRevokeIteration,List.append_assoc] using execBlock_append hfront hsol4
        · rw [hn4]; exact hf4
        · rw [hn4]
          exact (memLoad_of_prefix (recordPadding_prefix m4 heap4) (UInt256.ofNat 96) (by decide)
            (by dsimp only [next] at hlo4; change 128 ≤ _; omega) hm4).trans hzero4
      · refine Or.inr (Or.inl ⟨?_,hrev⟩)
        simpa only [multiRevokeIteration,List.append_assoc] using execBlock_append hfront hbad
      · refine Or.inr (Or.inr ⟨?_,hstatic⟩)
        simpa only [multiRevokeIteration,List.append_assoc] using execBlock_append hfront hbad
    · rw [if_neg hg] at hcopy hsol2
      refine Or.inr (Or.inl ⟨?_,hcopy⟩)
      simpa only [multiRevokeIteration,List.append_assoc] using execBlock_append hsol1
        (execBlock_append_term (s2 := multiRevokeCall++multiRevokeUpdate) hsol2 (by intros; exact nofun))
  · refine Or.inr (Or.inl ⟨?_,hrev⟩)
    simpa only [multiRevokeIteration,List.append_assoc] using
      execBlock_append_term (s2 := multiRevokeAllocate++multiRevokeCall++multiRevokeUpdate) hbad (by intros; exact nofun)

end Benchmarks.EAS.EAS
