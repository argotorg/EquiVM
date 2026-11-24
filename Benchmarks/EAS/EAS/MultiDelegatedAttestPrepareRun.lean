import Benchmarks.EAS.EAS.MultiDelegatedAttestPrepareSource
import Benchmarks.EAS.EAS.MultiDelegatedAttestAccess

variable {fork : Ethereum.Fork}
open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach ABI.Solc08Calldata
open Reasoning.Immutables Benchmarks.EAS.EAS.Immutables
namespace Benchmarks.EAS.EAS
set_option maxRecDepth 10000

theorem multiDelegatedAttestPrepareRun {L : Store} {evm : EVM.State}
    {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256}
    {out : ByteArray} {σ : AccountMap} {k C n i : Nat} {base available heap groupsPtr : UInt256}
    {groups : List (List UInt256)} {R : List UInt256}
    (v : EASImmutables) (hstack : R.length+24≤1024)
    (hf : MultiDelegatedAttestLocals L (delegatedBatchValues .attest ee.calldata base n) groups available heap.toNat i)
    (hi : i<n) (hn : n<UInt256.size) (hb : base.toNat+32*i<UInt256.size)
    (rd : RD fork (deployedRuntime v) ee g s0 ⟨2777⟩
      (multiDelegatedAttestLoopStack n i base available (UInt256.ofNat groups.flatten.length) groupsPtr R) mem aw out σ k C) :
    (∃ L' aw' k' C',
      DelegatedAttestationBatchReady ee.calldata (multiRequestRoot ee.calldata base i) ∧
      ExecBlock fork config {contract := contract,locals := L,immutables := immStore v} evm multiDelegatedAttestPrepare
        (.ok {contract := contract,locals := L',immutables := immStore v} evm) ∧
      MultiDelegatedAttestVerifyLocals L' (delegatedBatchValues .attest ee.calldata base n) groups available heap.toNat i 0
        (decide (i=n-1)) (delegatedAttestationTuple ee.calldata (multiRequestRoot ee.calldata base i))
        (delegatedAttestationDataList ee.calldata (multiRequestRoot ee.calldata base i))
        (delegatedAttestationSigList ee.calldata (multiRequestRoot ee.calldata base i)) ∧
      RD fork (deployedRuntime v) ee g s0 ⟨2874⟩
        (multiDelegatedAttestVerifyStack ee.calldata 0 (multiRequestRoot ee.calldata base i)
          (delegatedAttestationDataOffset ee.calldata (multiRequestRoot ee.calldata base i)) base (UInt256.ofNat n)
          (delegatedAttestationDataLength ee.calldata (multiRequestRoot ee.calldata base i)) available groupsPtr
          (UInt256.ofNat groups.flatten.length) (UInt256.ofNat i) (UInt256.ofNat n-⟨1⟩) R) mem aw' out σ k' C') ∨
    (ExecBlock fork config {contract := contract,locals := L,immutables := immStore v} evm multiDelegatedAttestPrepare .reverted ∧
      RDrev fork (deployedRuntime v) g s0) := by
  let row := delegatedBatchElement .attest ee.calldata base i
  let root := multiRequestRoot ee.calldata base i
  let L1 := batchRowReadLocals L "multiDelegatedRequest" (decide (i=n-1)) row
  have helem : row=if delegatedBatchReferenceValid ee.calldata base i then delegatedAttestationTuple ee.calldata root else decodeFailure := by
    simp only [row,delegatedBatchElement,delegatedAttestationElement_decode _ _ _ hb]
    split <;> rfl
  have hnrm : normalizeRawBoolWord? row=.ok row := by
    rw [helem];split <;> rfl
  have hsol1 : ExecBlock fork config {contract := contract,locals := L,immutables := immStore v} evm multiDelegatedAttestRead
      (.ok {contract := contract,locals := L1,immutables := immStore v} evm) := by
    have hread := batchRowReadSource (fork := fork) (imms := immStore v) (evm := evm) DelegatedBatchSite.attest.abi
      "multiDelegatedRequests" "multiDelegatedRequest" (by decide) hf.requests hf.index
      (by rw [delegatedBatchValues_length];exact hi) (by rw [delegatedBatchValues_length];exact hn)
      (by rw [delegatedBatchValues_get _ _ _ _ _ hi];exact hnrm)
    simpa only [delegatedBatchValues_length,delegatedBatchValues_get _ _ _ _ _ hi] using hread
  have hf1 : MultiDelegatedAttestLocals L1 (delegatedBatchValues .attest ee.calldata base n) groups available heap.toNat i := hf.read _ _
  have hlast : L1.get? "last"=some (.bool (decide (i=n-1))) := by
    simp (disch := decide) only [L1,batchRowReadLocals,store_get_ne,store_get_self]
  have haccess := easMultiDelegatedAttestAccess v (by omega) hi hn hb rd
  by_cases href : delegatedBatchReferenceValid ee.calldata base i
  · rw [if_pos href] at haccess
    obtain ⟨a1,k1,C1,r1⟩ := haccess
    have hrow : L1.get? "multiDelegatedRequest"=some (delegatedAttestationTuple ee.calldata root) := by
      simp only [L1,batchRowReadLocals,store_get_self,helem,if_pos href]
    have hcheck := multiDelegatedAttestCheck_tuple (fork := fork) (imms := immStore v) (evm := evm) hrow
    have hsrc := multiDelegatedAttestFieldsReadySource (fork := fork) (imms := immStore v) (evm := evm) hrow
    have hfields := easMultiDelegatedAttestFields v (by omega) r1
    by_cases hready : DelegatedAttestationBatchReady ee.calldata root
    · obtain ⟨a2,k2,C2,r2⟩ := hfields.1 hready
      refine Or.inl ⟨_,a2,k2,C2,hready,?_,hf1.fields _ _ hrow hlast,r2⟩
      simpa only [multiDelegatedAttestPrepare,List.append_assoc,List.singleton_append] using execBlock_append hsol1 (ExecBlock.consNormal hcheck (hsrc.1 hready))
    · refine Or.inr ⟨?_,hfields.2 hready⟩
      simpa only [multiDelegatedAttestPrepare,List.append_assoc,List.singleton_append] using execBlock_append hsol1 (ExecBlock.consNormal hcheck (hsrc.2 hready))
  · rw [if_neg href] at haccess
    have hrow : L1.get? "multiDelegatedRequest"=some decodeFailure := by
      simp only [L1,batchRowReadLocals,store_get_self,helem,if_neg href]
    refine Or.inr ⟨?_,haccess⟩
    simpa only [multiDelegatedAttestPrepare,List.append_assoc,List.singleton_append] using execBlock_append hsol1
      (ExecBlock.consRevert (stmts := multiDelegatedAttestFields) (multiDelegatedAttestCheck_bad (imms := immStore v) (evm := evm) hrow))

end Benchmarks.EAS.EAS
