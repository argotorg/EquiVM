import Benchmarks.EAS.EAS.MultiDelegatedRevokePrepareSource
import Benchmarks.EAS.EAS.MultiDelegatedRevokeControl
import Benchmarks.EAS.EAS.DelegatedRevocationPrepareValid
import Benchmarks.EAS.EAS.DelegatedRevocationPrepareInvalid
import Benchmarks.EAS.EAS.DelegatedRevocationGuard

variable {fork : Ethereum.Fork}
open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables Benchmarks.EAS.EAS.Immutables
namespace Benchmarks.EAS.EAS
set_option maxRecDepth 10000

theorem multiDelegatedRevokePrepareRun {L : Store} {evm : EVM.State}
    {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256}
    {out : ByteArray} {σ : AccountMap} {k C n i : Nat} {base available heap tag : UInt256} {R : List UInt256}
    (v : EASImmutables) (hstack : R.length+48 ≤ 1024)
    (hf : MultiDelegatedRevokeLocals L (delegatedBatchValues .revoke ee.calldata base n) available heap.toNat i)
    (hi : i<n) (hn : n<UInt256.size) (hb : base.toNat+32*i < UInt256.size)
    (hsize : ee.calldata.size < 2^255) (hlo : 96 ≤ heap.toNat) (hh : heap.toNat ≤ 2^64-1)
    (hmem : 96 ≤ mem.size) (hfree : memLoad (UInt256.ofNat 64) mem = heap)
    (rd : RD fork (deployedRuntime v) ee g s0 ⟨1298⟩ (multiDelegatedRevokeLoopStack n i base available (tag::R)) mem aw out σ k C) :
    (∃ (r : DelegatedRevocationBatch) (L' : Store) (mem' : ByteArray) (aw' : UInt256) (k' C' : Nat),
      delegatedRevocationNext heap r ≤ 2^64-1 ∧ (0<r.data.length ∧ r.data.length=r.signatures.length) ∧
      ExecBlock fork config {contract := contract,locals := L,immutables := immStore v} evm multiDelegatedRevokePrepare
        (.ok {contract := contract,locals := L',immutables := immStore v} evm) ∧
      MultiDelegatedRevokeVerifyLocals L' (delegatedBatchValues .revoke ee.calldata base n) available
        (delegatedRevocationNext heap r) i 0 (decide (i=n-1)) r ∧
      MemoryPrefix (recordPadding mem heap.toNat) mem' heap.toNat ∧
      DelegatedRevocationBatchMemoryView mem' heap (delegatedRevocationDataPtr heap) (delegatedRevocationSigPtr heap r.data)
        r (delegatedRevocationNext heap r) ∧
      memLoad (UInt256.ofNat 64) mem' = UInt256.ofNat (delegatedRevocationNext heap r) ∧
      RD fork (deployedRuntime v) ee g s0 ⟨1552⟩
        (multiDelegatedRevokeVerifyStack 0 base (UInt256.ofNat n) available (UInt256.ofNat n-⟨1⟩) heap
          (delegatedRevocationDataPtr heap) (UInt256.ofNat i::tag::R)) mem' aw' out σ k' C') ∨
    (ExecBlock fork config {contract := contract,locals := L,immutables := immStore v} evm multiDelegatedRevokePrepare .reverted ∧
      RDrev fork (deployedRuntime v) g s0) := by
  let rowValue := delegatedBatchElement .revoke ee.calldata base i
  let L1 := batchRowReadLocals L "multiDelegatedRequest" (decide (i=n-1)) rowValue
  have helem : rowValue = ((decodeDelegatedRevocation ee.calldata base i).map DelegatedRevocationBatch.tuple).getD
      ABI.Solc08Calldata.decodeFailure := by
    dsimp only [rowValue]
    rw [delegatedBatchElement,delegatedRevocationElement_decode _ _ _ hb (by omega)]
  have hnrm : normalizeRawBoolWord? rowValue = .ok rowValue := by
    rw [helem]; cases decodeDelegatedRevocation ee.calldata base i <;> rfl
  have hsol1 : ExecBlock fork config {contract := contract,locals := L,immutables := immStore v} evm multiDelegatedRevokeRead
      (.ok {contract := contract,locals := L1,immutables := immStore v} evm) := by
    have hread := batchRowReadSource (fork := fork) (imms := immStore v) (evm := evm) DelegatedBatchSite.revoke.abi
      "multiDelegatedRequests" "multiDelegatedRequest" (by decide) hf.requests hf.index
      (by rw [delegatedBatchValues_length]; exact hi) (by rw [delegatedBatchValues_length]; exact hn)
      (by rw [delegatedBatchValues_get _ _ _ _ _ hi]; exact hnrm)
    simpa only [delegatedBatchValues_length,delegatedBatchValues_get _ _ _ _ _ hi] using hread
  have hf1 : MultiDelegatedRevokeLocals L1 (delegatedBatchValues .revoke ee.calldata base n) available heap.toNat i := hf.read _ _
  have hlast : L1.get? "last"=some (.bool (decide (i=n-1))) := by
    simp (disch := decide) only [L1,batchRowReadLocals,store_get_ne,store_get_self]
  have haccess := easMultiDelegatedRevokeAccess v (by simp only [List.length_cons]; omega) hi hn hb rd
  cases hd : decodeDelegatedRevocation ee.calldata base i with
  | none =>
    have hrow : L1.get? "multiDelegatedRequest"=some ABI.Solc08Calldata.decodeFailure := by
      simp only [L1,batchRowReadLocals,store_get_self,helem,hd,Option.map_none,Option.getD_none]
    refine Or.inr ⟨?_,?_⟩
    · simpa only [multiDelegatedRevokePrepare,List.append_assoc] using
        execBlock_append hsol1 (ExecBlock.consRevert
          (stmts := multiDelegatedRevokeFields++multiDelegatedRevokeAllocate++[multiDelegatedRevokeGuard,multiDelegatedRevokeJInit])
          (multiDelegatedRevokeCheck_bad hrow))
    · by_cases href : delegatedBatchReferenceValid ee.calldata base i
      · rw [if_pos href] at haccess
        obtain ⟨a1,k1,C1,r1⟩ := haccess
        have hat : decodeDelegatedRevocationAt ee.calldata (multiRequestRoot ee.calldata base i) = none := by
          simpa only [decodeDelegatedRevocation,if_pos href] using hd
        exact easDelegatedRevocationPrepareInvalid (R := UInt256.ofNat i::tag::R) v
          (by simp only [List.length_cons]; omega)
          hsize hlo hh hmem hfree hat r1
      · simpa only [if_neg href] using haccess
  | some r =>
    obtain ⟨href,hat⟩ := decodeDelegatedRevocation_facts hd
    have hrow : L1.get? "multiDelegatedRequest"=some r.tuple := by
      simp only [L1,batchRowReadLocals,store_get_self,helem,hd,Option.map_some,Option.getD_some]
    have hfront := execBlock_append hsol1 (ExecBlock.consNormal (multiDelegatedRevokeCheck_ok hrow) ExecBlock.nil)
    rw [if_pos href] at haccess
    obtain ⟨a1,k1,C1,r1⟩ := haccess
    have hp := easDelegatedRevocationPrepareValid (R := UInt256.ofNat i::tag::R) v
      (by simp only [List.length_cons]; omega)
      hsize hlo hh hmem hfree hat r1
    obtain ⟨_,hfields⟩ := decodeDelegatedRevocationAt_facts hat
    obtain ⟨_,hdData,_,hdSig,_,_,_⟩ := decodeDelegatedRevocationFields_facts hfields
    obtain ⟨hdValid,hdLen,_⟩ := decodeRevocationArray_facts (by omega) hdData
    obtain ⟨hsValid,hsLen,_,_⟩ := decodeSignatureArray_facts (by omega) hdSig
    have hsrc := multiDelegatedRevokePrepareRowSource (fork := fork) (imms := immStore v) (evm := evm) hf1 hrow hlast hh
      (by rw [hdLen]; exact hdValid.1) (by rw [hsLen]; exact hsValid.1)
    by_cases ha : delegatedRevocationNext heap r ≤ 2^64-1
    · rw [if_pos ha] at hp
      rw [if_pos (show heap.toNat+192+96*r.data.length+128*r.signatures.length ≤ 2^64-1 from ha)] at hsrc
      obtain ⟨m2,a2,k2,C2,hpre,hv,hfree2,hfree3,r2⟩ := hp
      have hguard := easDelegatedRevocationGuard v (by omega) (by change delegatedRevocationNext heap r < 2^256; omega) hv r2
      by_cases hg : 0<r.data.length ∧ r.data.length=r.signatures.length
      · rw [if_pos hg] at hguard hsrc
        obtain ⟨L3,hsol3,hf3⟩ := hsrc
        obtain ⟨a3,k3,C3,r3⟩ := hguard
        refine Or.inl ⟨r,L3,_,a3,k3,C3,ha,hg,?_,hf3,hpre,hv,hfree3,r3⟩
        simpa only [multiDelegatedRevokePrepare,multiDelegatedRevokePrepareRow,List.append_assoc] using execBlock_append hfront hsol3
      · rw [if_neg hg] at hguard hsrc
        refine Or.inr ⟨?_,hguard⟩
        simpa only [multiDelegatedRevokePrepare,multiDelegatedRevokePrepareRow,List.append_assoc] using execBlock_append hfront hsrc
    · rw [if_neg ha] at hp
      rw [if_neg (show ¬heap.toNat+192+96*r.data.length+128*r.signatures.length ≤ 2^64-1 from ha)] at hsrc
      refine Or.inr ⟨?_,hp⟩
      simpa only [multiDelegatedRevokePrepare,multiDelegatedRevokePrepareRow,List.append_assoc] using execBlock_append hfront hsrc

end Benchmarks.EAS.EAS
