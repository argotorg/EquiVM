import Benchmarks.EAS.EAS.MultiDelegatedRevokeVerifySource
import Benchmarks.EAS.EAS.MultiDelegatedRevokeControl
import Benchmarks.EAS.EAS.SpendAndIncrementSource
import Benchmarks.EAS.EAS.MultiAttestFacts

variable {fork : Ethereum.Fork}
open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables Benchmarks.EAS.EAS.Immutables
namespace Benchmarks.EAS.EAS
set_option maxRecDepth 10000

def multiDelegatedRevokeCallLocals (L : Store) (used : UInt256) (heap : Nat) : Store :=
  heapResultLocals L "__c1$allocation" "__c1" "$EAS.freeMemory" (.int (Int.ofNat used.toNat)) heap

theorem MultiDelegatedRevokeLocals.called {L : Store} {requests : List Value} {available : UInt256} {heap i : Nat}
    (h : MultiDelegatedRevokeLocals L requests available heap i) (used : UInt256) (next : Nat) :
    MultiDelegatedRevokeLocals (multiDelegatedRevokeCallLocals L used next) requests available next i := by
  constructor <;> simp (disch := decide) only [multiDelegatedRevokeCallLocals,heapResultLocals_get,heapResultLocals_heap] <;>
    first | exact h.requests | exact h.available | exact h.index

theorem MultiDelegatedRevokeLocals.next {L : Store} {requests : List Value} {available : UInt256} {heap i : Nat}
    (h : MultiDelegatedRevokeLocals L requests available heap i) (used : UInt256) :
    MultiDelegatedRevokeLocals (spendAndIncrementLocals L available used i) requests (UInt256.sub available used) heap (i+1) := by
  constructor <;> simp (disch := decide) only [spendAndIncrementLocals,store_get_ne,store_get_self] <;>
    first | exact h.requests | exact h.heap

theorem multiDelegatedRevokeCallRun {L : Store} {evm : EVM.State} {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem : ByteArray} {aw : UInt256} {out : ByteArray} {σ : AccountMap} {k C n i : Nat}
    {base available heap row data sig : UInt256} {requests : List Value} {r : DelegatedRevocationBatch} {R : List UInt256}
    (v : EASImmutables) (hstack : R.length+48 ≤ 1024) (hstate : SourceState s0 ee σ evm)
    (hf : MultiDelegatedRevokeVerifyLocals L requests available heap.toNat i r.data.length (decide (i=n-1)) r)
    (hv : DelegatedRevocationBatchMemoryView mem row data sig r heap.toNat)
    (hi : i<n) (hn : n<UInt256.size) (hh : heap.toNat ≤ 2^64-1)
    (hfree : memLoad (UInt256.ofNat 64) mem = heap) (hzero : memLoad (UInt256.ofNat 96) mem = ⟨0⟩)
    (hsize : ee.calldata.size < UInt256.size)
    (rd : RD fork (deployedRuntime v) ee g s0 ⟨1552⟩
      (multiDelegatedRevokeVerifyStack r.data.length base (UInt256.ofNat n) available (UInt256.ofNat n-⟨1⟩) row data
        (UInt256.ofNat i::R)) mem aw out σ k C) :
    (∃ (L' : Store) (evm' : EVM.State) (σ' : AccountMap) (mem' out' : ByteArray) (aw' : UInt256)
        (k' C' next : Nat) (used : UInt256),
      SourceState s0 ee σ' evm' ∧ heap.toNat ≤ next ∧ next ≤ 2^64-1 ∧ MemoryPrefix mem mem' heap.toNat ∧
      MultiDelegatedRevokeLocals L' requests (UInt256.sub available used) next (i+1) ∧
      memLoad (UInt256.ofNat 64) mem' = UInt256.ofNat next ∧
      ExecBlock fork config {contract := contract,locals := L,immutables := immStore v} evm (multiDelegatedRevokeCall++multiDelegatedRevokeUpdate)
        (.ok {contract := contract,locals := L',immutables := immStore v} evm') ∧
      RD fork (deployedRuntime v) ee g s0 ⟨1298⟩
        (multiDelegatedRevokeLoopStack n (i+1) base (UInt256.sub available used) R) mem' aw' out' σ' k' C') ∨
    (ExecBlock fork config {contract := contract,locals := L,immutables := immStore v} evm (multiDelegatedRevokeCall++multiDelegatedRevokeUpdate) .reverted ∧
      RDrev fork (deployedRuntime v) g s0) ∨
    (ExecBlock fork config {contract := contract,locals := L,immutables := immStore v} evm (multiDelegatedRevokeCall++multiDelegatedRevokeUpdate) .staticViolation ∧
      RDstatic fork (deployedRuntime v) g s0) := by
  have he : evalExprs? config {contract := contract,locals := L,immutables := immStore v} evm multiDelegatedRevokeCallArgs =
      .ok [wordBytes32Value r.schema,.array (r.data.map RevocationRequestRecord.tuple),.address r.revoker,
        .int (Int.ofNat available.toNat),.bool (decide (i=n-1)),.int (Int.ofNat heap.toNat)] := by
    simp only [multiDelegatedRevokeCallArgs,evalExprs?,evalExpr?,hf.request,hf.data,hf.outer.available,hf.last,hf.outer.heap,
      DelegatedRevocationBatch.tuple,EvalResult.ofOption,bind,EvalResult.bind,pure]
    rfl
  obtain ⟨a1,k1,C1,r1⟩ := easMultiDelegatedRevokeVerifyDone v (by omega) hv rd
  obtain ⟨used,hr⟩ := revokeCallRun (retVar := "__c1$allocation") (ret := ⟨1710⟩)
    (R := available::⟨1716⟩::⟨1⟩::UInt256.ofNat n::(UInt256.ofNat n-⟨1⟩)::base::UInt256.ofNat i::R)
    v .many (by simp only [List.length_cons]; omega) hstate he hv.data.finish hh hfree hzero (by intro h; cases h)
    hsize (by rw [easPatchedValidJumps v]; jump_dest)
    (by simpa only [revokeEntryStack,RevokeKind.entryPC,multiAttestLastWord_eq hi hn] using r1)
  rcases hr with (⟨hu,hr⟩ | ⟨hbad,hrev⟩) | ⟨hbad,hstatic⟩
  · rcases hr with ⟨e2,σ2,mem2,out2,a2,k2,C2,next,hs2,hlo2,hh2,hp2,hfree2,hcall,r2⟩ | ⟨hbad,hrev⟩
    · let L2 := multiDelegatedRevokeCallLocals L used next
      have hf2 : MultiDelegatedRevokeLocals L2 requests available next i := hf.outer.called used next
      have hres : L2.get? "__c1"=some (.int (Int.ofNat used.toNat)) := heapResultLocals_result _ _ _ _ _ _ (by decide)
      have hsol1 : ExecBlock fork config {contract := contract,locals := L,immutables := immStore v} evm multiDelegatedRevokeCall
          (.ok {contract := contract,locals := L2,immutables := immStore v} e2) :=
        heapResultBlock_ok (result := "__c1") (cursor := "$EAS.freeMemory") hcall hf.outer.heap (by decide) (by decide) (by decide)
      have hsol2 : ExecBlock fork config {contract := contract,locals := L2,immutables := immStore v} e2 multiDelegatedRevokeUpdate
          (.ok {contract := contract,locals := spendAndIncrementLocals L2 available used i,immutables := immStore v} e2) :=
        spendAndIncrementSource hf2.available hres hf2.index (by omega) hu
      obtain ⟨a3,k3,C3,r3⟩ := easMultiDelegatedRevokeUpdate v (by omega) hu r2
      exact Or.inl ⟨_,e2,σ2,mem2,out2,a3,k3,C3,next,used,hs2,hlo2,hh2,hp2,hf2.next used,hfree2,
        execBlock_append hsol1 hsol2,r3⟩
    · exact Or.inr (Or.inl ⟨execBlock_append_term (ExecBlock.consRevert hbad) (by intros; exact nofun),hrev⟩)
  · exact Or.inr (Or.inl ⟨execBlock_append_term (ExecBlock.consRevert hbad) (by intros; exact nofun),hrev⟩)
  · exact Or.inr (Or.inr ⟨execBlock_append_term (ExecBlock.consStatic hbad) (by intros; exact nofun),hstatic⟩)

end Benchmarks.EAS.EAS
