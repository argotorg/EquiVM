import Benchmarks.EAS.EAS.MultiDelegatedAttestDatumPrepareSource
import Benchmarks.EAS.EAS.MultiDelegatedAttestVerifyAccess
import Benchmarks.EAS.EAS.DelegatedAttestationBatch

variable {fork : Ethereum.Fork}
open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach ABI.Solc08Calldata
open Reasoning.Immutables Benchmarks.EAS.EAS.Immutables
namespace Benchmarks.EAS.EAS
set_option maxRecDepth 10000

def delegatedAttestItemSource (cd : ByteArray) (root : UInt256) (j : Nat) : UInt256 :=
  requestArrayElement cd (delegatedAttestationDataOffset cd root) j
def delegatedAttestItemSigSource (cd : ByteArray) (root : UInt256) (j : Nat) : UInt256 :=
  UInt256.ofNat ((delegatedAttestationSigOffset cd root).toNat+96*j)
def delegatedAttestItemRecord (cd : ByteArray) (root : UInt256) (j : Nat) : DelegatedAttestationRecord :=
  delegatedAttestBuildRecord cd (calldataWord cd root.toNat) (delegatedAttestItemSource cd root j)
    (delegatedAttestItemSigSource cd root j) (root+UInt256.ofNat 96)
def delegatedAttestItemValid (cd : ByteArray) (root heap : UInt256) (j : Nat) : Prop :=
  requestReferenceValid cd (delegatedAttestationDataOffset cd root) (UInt256.ofNat ((delegatedAttestationDataOffset cd root).toNat+32*j)) ∧
  delegatedAttestBuildValid cd (delegatedAttestItemSource cd root j) (delegatedAttestItemSigSource cd root j) (root+UInt256.ofNat 96) heap
instance (cd : ByteArray) (root heap : UInt256) (j : Nat) : Decidable (delegatedAttestItemValid cd root heap j) :=
  inferInstanceAs (Decidable (_ ∧ _))
def delegatedAttestItemNext (cd : ByteArray) (root heap : UInt256) (j : Nat) : Nat :=
  delegatedAttestBuildCopyHeap cd (delegatedAttestItemSource cd root j) heap+96
def delegatedAttestItemMemory (mem cd : ByteArray) (root heap : UInt256) (j : Nat) : ByteArray :=
  delegatedAttestBuildMemory mem cd (calldataWord cd root.toNat) (delegatedAttestItemSource cd root j)
    (delegatedAttestItemSigSource cd root j) (root+UInt256.ofNat 96) heap

theorem multiDelegatedAttestDatumRun {L : Store} {evm : EVM.State}
    {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {out : ByteArray}
    {σ : AccountMap} {k C j : Nat} {root base n available groups total i last heap : UInt256} {R : List UInt256}
    (v : EASImmutables) (hstack : R.length+40≤1024) (hsize : ee.calldata.size<2^255)
    (hb : DelegatedAttestationBatchReady ee.calldata root)
    (hd : L.get? "data"=some (.array (delegatedAttestationDataList ee.calldata root)))
    (hs : L.get? "signatures"=some (.array (delegatedAttestationSigList ee.calldata root)))
    (hr : L.get? "multiDelegatedRequest"=some (delegatedAttestationTuple ee.calldata root))
    (hj : L.get? "j"=some (.int (Int.ofNat j)))
    (hf : L.get? "$EAS.freeMemory"=some (.int (Int.ofNat heap.toNat)))
    (hjl : j<(delegatedAttestationDataLength ee.calldata root).toNat)
    (hlo : 96≤heap.toNat) (hh : heap.toNat≤2^64-1) (hm : 96≤mem.size)
    (hfree : memLoad (UInt256.ofNat 64) mem=heap)
    (rd : RD fork (deployedRuntime v) ee g s0 ⟨2874⟩
      (multiDelegatedAttestVerifyStack ee.calldata j root (delegatedAttestationDataOffset ee.calldata root)
        base n (delegatedAttestationDataLength ee.calldata root) available groups total i last R) mem aw out σ k C) :
    let r := delegatedAttestItemRecord ee.calldata root j
    let next := delegatedAttestItemNext ee.calldata root heap j
    let final := delegatedAttestItemMemory mem ee.calldata root heap j
    let L' := multiDelegatedAttestDatumPreparedLocals L heap.toNat r.data r.signature r.attester
    if delegatedAttestItemValid ee.calldata root heap j then
      ExecBlock fork config {contract := contract,locals := L,immutables := immStore v} evm multiDelegatedAttestDatumPrepare
        (.ok {contract := contract,locals := L',immutables := immStore v} evm) ∧
      heap.toNat≤next ∧ next≤2^64-1 ∧ MemoryPrefix mem final heap.toNat ∧
      DelegatedAttestMemoryView final heap (delegatedAttestBuildData heap) (delegatedAttestBuildBytes heap)
        (UInt256.ofNat (next-96)) r next ∧ memLoad (UInt256.ofNat 64) final=UInt256.ofNat next ∧
      ∃ aw' k' C', RD fork (deployedRuntime v) ee g s0 ⟨13494⟩
        (heap::UInt256.ofNat 3025::UInt256.ofNat j::⟨1⟩::
          multiDelegatedAttestVerifyTail ee.calldata root (delegatedAttestationDataOffset ee.calldata root)
            base n (delegatedAttestationDataLength ee.calldata root) available groups total i last R) final aw' out σ k' C'
    else ExecBlock fork config {contract := contract,locals := L,immutables := immStore v} evm multiDelegatedAttestDatumPrepare .reverted ∧
      RDrev fork (deployedRuntime v) g s0 := by
  dsimp only
  have hbounds := hb.bounds hsize
  have hjb : j<UInt256.size := by have := (delegatedAttestationDataLength ee.calldata root).val.isLt;omega
  have hslot : (delegatedAttestationDataOffset ee.calldata root).toNat+32*j<UInt256.size := by omega
  have hsslot : (delegatedAttestationSigOffset ee.calldata root).toNat+96*j<UInt256.size := by omega
  have hjd : j<(delegatedAttestationDataList ee.calldata root).length := by rw [delegatedAttestationDataList_length];exact hjl
  have hjs : j<(delegatedAttestationSigList ee.calldata root).length := by rw [delegatedAttestationSigList_length,← hb.lengths];exact hjl
  have hdval := delegatedAttestationData_get ee.calldata (delegatedBatchArray ee.calldata root 32) j hjd hslot
  have hsval := delegatedAttestationSignature_get ee.calldata (delegatedBatchArray ee.calldata root 64) j hjs
  have hsrc := multiDelegatedAttestDatumPrepareSource (fork := fork) (imms := immStore v) (evm := evm)
    (r := (delegatedAttestItemRecord ee.calldata root j).data) (s := (delegatedAttestItemRecord ee.calldata root j).signature)
    (addr := (delegatedAttestItemRecord ee.calldata root j).attester)
    (delegatedAttestationDataValid ee.calldata (delegatedAttestationDataOffset ee.calldata root) j)
    (delegatedBatchAddressClean ee.calldata root) (signatureAtValid ee.calldata (delegatedAttestItemSigSource ee.calldata root j))
    hd hs (by rw [hb.tuple] at hr;exact hr) hj hf hjd hjs hdval hsval rfl hh
  have hiff : (delegatedAttestationDataValid ee.calldata (delegatedAttestationDataOffset ee.calldata root) j ∧
      delegatedBatchAddressClean ee.calldata root ∧ signatureAtValid ee.calldata (delegatedAttestItemSigSource ee.calldata root j) ∧
      heap.toNat+128≤2^64-1 ∧ copyRequestValid (heap.toNat+128) (delegatedAttestItemRecord ee.calldata root j).data.data.size ∧
      copyRequestNext (heap.toNat+128) (delegatedAttestItemRecord ee.calldata root j).data.data.size+96≤2^64-1) ↔
      delegatedAttestItemValid ee.calldata root heap j := by
    unfold delegatedAttestationDataValid delegatedAttestItemValid delegatedAttestBuildValid delegatedAttestBuildCopyHeap
      delegatedAttestItemRecord delegatedAttestBuildRecord delegatedAttestItemSource delegatedBatchAddressClean
    constructor
    · rintro ⟨⟨href,hdv⟩,hav,hsv,hcap,hcopy,hnext⟩
      exact ⟨href,hav,hcap,hdv,hcopy,hsv,hnext⟩
    · rintro ⟨href,hav,hcap,hdv,hcopy,hsv,hnext⟩
      exact ⟨⟨href,hdv⟩,hav,hsv,hcap,hcopy,hnext⟩
  simp only [hiff] at hsrc
  have haccess := easMultiDelegatedAttestVerifyAccess v (by omega) hjl hslot hb.signatures
    (by change j<(delegatedAttestationSigLength ee.calldata root).toNat;rw [← hb.lengths];exact hjl) rd
  have heSig := delegatedAttestationSigIndex_word (cd := ee.calldata) (root := root) hjb hsslot
  by_cases href : requestReferenceValid ee.calldata (delegatedAttestationDataOffset ee.calldata root)
      (UInt256.ofNat ((delegatedAttestationDataOffset ee.calldata root).toNat+32*j))
  · rw [if_pos href] at haccess
    obtain ⟨a1,k1,C1,r1⟩ := haccess
    have hbuild := easDelegatedAttestBuild v (by simp only [multiDelegatedAttestVerifyTail,List.length_append,List.length_cons,List.length_nil];omega)
      (by omega) hlo hh hm hfree r1
    change UInt256.mul (UInt256.ofNat j) (UInt256.ofNat 96)+(delegatedBatchArray ee.calldata root 64+UInt256.ofNat 32)=
      delegatedAttestItemSigSource ee.calldata root j at heSig
    dsimp only at hbuild
    rw [heSig] at hbuild
    by_cases hv : delegatedAttestItemValid ee.calldata root heap j
    · rw [if_pos hv] at hsrc ⊢
      have hmem := delegatedAttestBuildMemory_facts (mem := mem) (schema := calldataWord ee.calldata root.toNat)
        hlo hm (by omega) hv.2
      have hrdy := hbuild.1 hv.2
      have hlo' := hmem.2.1.span
      refine ⟨hsrc,by change heap.toNat+128≤delegatedAttestItemNext ee.calldata root heap j at hlo';omega,
        hv.2.2.2.2.2.2,hmem.1,?_,hmem.2.2,hrdy⟩
      simpa only [delegatedAttestItemNext,Nat.add_sub_cancel] using hmem.2.1
    · rw [if_neg hv] at hsrc ⊢
      exact ⟨hsrc,hbuild.2 (fun h => hv ⟨href,h⟩)⟩
  · have hv : ¬delegatedAttestItemValid ee.calldata root heap j := fun h => href h.1
    rw [if_neg href] at haccess
    rw [if_neg hv] at hsrc ⊢
    exact ⟨hsrc,haccess⟩

end Benchmarks.EAS.EAS
