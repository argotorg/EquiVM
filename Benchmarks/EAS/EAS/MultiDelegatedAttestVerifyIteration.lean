import Benchmarks.EAS.EAS.MultiDelegatedAttestDatumRun

variable {fork : Ethereum.Fork}
open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables Benchmarks.EAS.EAS.Immutables
namespace Benchmarks.EAS.EAS
set_option maxRecDepth 10000

def MultiDelegatedAttestVerifyAt (fork : Ethereum.Fork) (v : EASImmutables) (ee : ExecutionEnv) (g : Sat256) (s0 : State)
    (requests : List Value) (groups : List (List UInt256)) (n i : Nat) (base available groupsPtr root : UInt256)
    (initial : ByteArray) (start : Nat) (R : List UInt256) (j : Nat) (L : Store) (evm : EVM.State) : Prop :=
  ∃ (σ : AccountMap) (mem out : ByteArray) (aw : UInt256) (k C : Nat) (heap : UInt256),
    SourceState s0 ee σ evm ∧ start≤heap.toNat ∧ heap.toNat≤2^64-1 ∧ MemoryPrefix initial mem start ∧
    MultiDelegatedAttestVerifyLocals L requests groups available heap.toNat i j (decide (i=n-1))
      (delegatedAttestationTuple ee.calldata root) (delegatedAttestationDataList ee.calldata root) (delegatedAttestationSigList ee.calldata root) ∧
    (∀ t, t < j → delegatedAttestationDataValid ee.calldata (delegatedAttestationDataOffset ee.calldata root) t ∧
      delegatedBatchAddressClean ee.calldata root) ∧
    96≤mem.size ∧ memLoad (UInt256.ofNat 64) mem=heap ∧
    RD fork (deployedRuntime v) ee g s0 ⟨2874⟩
      (multiDelegatedAttestVerifyStack ee.calldata j root (delegatedAttestationDataOffset ee.calldata root)
        base (UInt256.ofNat n) (delegatedAttestationDataLength ee.calldata root) available groupsPtr
        (UInt256.ofNat groups.flatten.length) (UInt256.ofNat i) (UInt256.ofNat n-⟨1⟩) R) mem aw out σ k C

theorem multiDelegatedAttestVerifyIterationRun {L : Store} {evm : EVM.State}
    {ee : ExecutionEnv} {g : Sat256} {s0 : State} {requests : List Value} {groups : List (List UInt256)}
    {n i j : Nat} {base available groupsPtr root : UInt256} {initial : ByteArray} {start : Nat} {R : List UInt256}
    (v : EASImmutables) (hstack : R.length+40≤1024) (hsize : ee.calldata.size<2^255) (hlo : 96≤start)
    (hb : DelegatedAttestationBatchReady ee.calldata root)
    (hj : j<(delegatedAttestationDataLength ee.calldata root).toNat)
    (h : MultiDelegatedAttestVerifyAt fork v ee g s0 requests groups n i base available groupsPtr root initial start R j L evm) :
    (∃ L' evm', ExecBlock fork config {contract := contract,locals := L,immutables := immStore v} evm multiDelegatedAttestVerifyIteration
      (.ok {contract := contract,locals := L',immutables := immStore v} evm') ∧
      MultiDelegatedAttestVerifyAt fork v ee g s0 requests groups n i base available groupsPtr root initial start R (j+1) L' evm') ∨
    (ExecBlock fork config {contract := contract,locals := L,immutables := immStore v} evm multiDelegatedAttestVerifyIteration .reverted ∧
      RDrev fork (deployedRuntime v) g s0) ∨
    (ExecBlock fork config {contract := contract,locals := L,immutables := immStore v} evm multiDelegatedAttestVerifyIteration .staticViolation ∧
      RDstatic fork (deployedRuntime v) g s0) := by
  obtain ⟨σ,mem,out,aw,k,C,heap,hstate,hstart,hh,hprefix,hf,hgood,hmem,hfree,rd⟩ := h
  have hprep := multiDelegatedAttestDatumRun (evm := evm) v hstack hsize hb hf.data hf.signatures hf.request hf.index hf.outer.heap
    hj (by omega) hh hmem hfree rd
  dsimp only at hprep
  by_cases hv : delegatedAttestItemValid ee.calldata root heap j
  · rw [if_pos hv] at hprep
    obtain ⟨hsol1,hlo1,hh1,hp1,hv1,hfree1,a1,k1,C1,r1⟩ := hprep
    let r := delegatedAttestItemRecord ee.calldata root j
    let next := delegatedAttestItemNext ee.calldata root heap j
    let L1 := multiDelegatedAttestDatumPreparedLocals L heap.toNat r.data r.signature r.attester
    have hn1 : (UInt256.ofNat next).toNat=next := ulit_toNat' _ (by change next<2^256;change next≤2^64-1 at hh1;omega)
    have hf1 : MultiDelegatedAttestVerifyLocals L1 requests groups available next i j (decide (i=n-1))
        (delegatedAttestationTuple ee.calldata root) (delegatedAttestationDataList ee.calldata root) (delegatedAttestationSigList ee.calldata root) :=
      hf.prepared r.data r.signature r.attester
    have hfacts := multiDelegatedAttestDatumPreparedLocals_facts L heap.toNat r.data r.signature r.attester
    have hargs := multiDelegatedAttestVerifyArgs_eval (imms := immStore v) (evm := evm) (r := r) hf1.request rfl
      hfacts.1 hfacts.2.1 hfacts.2.2 hf1.outer.heap
    have hcall := verifyAttestCallRun (L := L1) (heap := UInt256.ofNat next) (ptr := heap) (r := r)
      (retVar := "__c0$allocation") v (by simpa only [hn1] using hargs)
      (by simp only [List.length_cons,multiDelegatedAttestVerifyTail,List.length_append,List.length_nil];omega) hstate
      (by simpa only [hn1] using hv1) hfree1 (by rw [hn1];exact hh1)
      (by rw [easPatchedValidJumps v];jump_dest) r1
    rcases hcall with (⟨e2,σ2,mem2,out2,a2,k2,C2,heap2,hs2,hlo2,hh2,hp2,hfree2,hsol2,r2⟩ | ⟨hbad,hrev⟩) | ⟨hbad,hstatic⟩
    · simp only [hn1] at hlo2 hp2
      let L2 := heapResultLocals L1 "__c0$allocation" "__c0" "$EAS.freeMemory" (.tuple []) heap2
      have hf2 : MultiDelegatedAttestVerifyLocals L2 requests groups available heap2 i j (decide (i=n-1))
          (delegatedAttestationTuple ee.calldata root) (delegatedAttestationDataList ee.calldata root) (delegatedAttestationSigList ee.calldata root) := hf1.called heap2
      have hsol2b : ExecBlock fork config {contract := contract,locals := L1,immutables := immStore v} evm multiDelegatedAttestVerify
          (.ok {contract := contract,locals := L2,immutables := immStore v} e2) :=
        heapResultBlock_ok (result := "__c0") (cursor := "$EAS.freeMemory") hsol2 hf1.outer.heap (by decide) (by decide) (by decide)
      have hjb : j+1<UInt256.size := by have := (hb.bounds hsize).1;change _<2^256;omega
      have hsol3 := execLocalCastIncrement (fork := fork) (cfg := config) (frame := {contract := contract,locals := L2,immutables := immStore v})
        (evm := e2) hf2.index hjb
      obtain ⟨a3,k3,C3,r3⟩ := easBlocks.eas_block_3025_packed (immWords := wordsOf (immStore v))
        (by simp only [List.length_cons,multiDelegatedAttestVerifyTail,List.length_append,List.length_nil];omega)
        (by rw [easPatchedValidJumpsRuntime v];jump_dest) r2
      have hn2 : (UInt256.ofNat heap2).toNat=heap2 := ulit_toNat' _ (by change heap2<2^256;omega)
      have hinc : UInt256.ofNat j+⟨1⟩=UInt256.ofNat (j+1) := (u256_add_comm _ _).trans (u256_one_add_ofNat j)
      have hp12 : MemoryPrefix mem mem2 heap.toNat := hp1.trans (hp2.mono hlo1)
      have hitem : delegatedAttestationDataValid ee.calldata (delegatedAttestationDataOffset ee.calldata root) j ∧
          delegatedBatchAddressClean ee.calldata root := ⟨⟨hv.1,hv.2.2.2.1⟩,hv.2.1⟩
      refine Or.inl ⟨L2.insert "j" (.int (Int.ofNat (j+1))),e2,?_,σ2,mem2,out2,a3,k3,C3,UInt256.ofNat heap2,
        hs2,by rw [hn2];change next≤heap2 at hlo2;change heap.toNat≤next at hlo1;omega,
        by rw [hn2];exact hh2,hprefix.trans (hp12.mono hstart),?_,?_,le_trans hmem hp12.size,hfree2,?_⟩
      · simpa only [multiDelegatedAttestVerifyIteration,List.append_assoc] using
          execBlock_append hsol1 (execBlock_append hsol2b (ExecBlock.consNormal hsol3 ExecBlock.nil))
      · rw [hn2];exact hf2.increment
      · intro t ht
        by_cases hlt : t<j
        · exact hgood t hlt
        · have he : t=j := by omega
          simpa only [he] using hitem
      · simpa only [easBlocks.eas_block_3025_stack,hinc,multiDelegatedAttestVerifyStack] using r3
    · refine Or.inr (Or.inl ⟨?_,hrev⟩)
      simpa only [multiDelegatedAttestVerifyIteration,multiDelegatedAttestVerify,heapResultBlock,List.append_assoc] using
        execBlock_append hsol1 (execBlock_append_term (s2 := [localCastIncrement "j"])
          (ExecBlock.consRevert (stmts := multiDelegatedAttestVerify.tail) hbad) (by intros;exact nofun))
    · refine Or.inr (Or.inr ⟨?_,hstatic⟩)
      simpa only [multiDelegatedAttestVerifyIteration,multiDelegatedAttestVerify,heapResultBlock,List.append_assoc] using
        execBlock_append hsol1 (execBlock_append_term (s2 := [localCastIncrement "j"])
          (ExecBlock.consStatic (stmts := multiDelegatedAttestVerify.tail) hbad) (by intros;exact nofun))
  · rw [if_neg hv] at hprep
    refine Or.inr (Or.inl ⟨?_,hprep.2⟩)
    simpa only [multiDelegatedAttestVerifyIteration,List.append_assoc] using
      execBlock_append_term (s2 := multiDelegatedAttestVerify ++ [localCastIncrement "j"]) hprep.1 (by intros;exact nofun)

end Benchmarks.EAS.EAS
