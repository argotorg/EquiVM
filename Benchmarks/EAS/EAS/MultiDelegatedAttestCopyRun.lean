import Benchmarks.EAS.EAS.CheckAttestationCopyFacts
import Benchmarks.EAS.EAS.MultiDelegatedAttestVerifyDone
import Benchmarks.EAS.EAS.MultiDelegatedAttestLocals
import Benchmarks.EAS.EAS.CopyRequestArrayInvalid
import Benchmarks.EAS.EAS.CopyRequestArrayCall

variable {fork : Ethereum.Fork}
open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables Benchmarks.EAS.EAS.Immutables
namespace Benchmarks.EAS.EAS
set_option maxRecDepth 10000

def multiDelegatedAttestCopyCheckLocals (L : Store) (heap : Nat) : Store :=
  heapResultLocals L "__copyCheck$allocation" "__copyCheck" "$EAS.freeMemory" (.tuple []) heap

theorem MultiDelegatedAttestVerifyLocals.copyChecked {L : Store} {requests : List Value} {groups : List (List UInt256)}
    {available : UInt256} {heap i j : Nat} {last : Bool} {row : Value} {data sigs : List Value}
    (h : MultiDelegatedAttestVerifyLocals L requests groups available heap i j last row data sigs) :
    MultiDelegatedAttestVerifyLocals (multiDelegatedAttestCopyCheckLocals L heap) requests groups available heap i j last row data sigs := by
  refine ⟨?_,?_,?_,?_,?_,?_⟩
  · constructor <;> simp (disch := decide) only [multiDelegatedAttestCopyCheckLocals,heapResultLocals_get,heapResultLocals_heap] <;>
      first | exact h.outer.requests | exact h.outer.groups | exact h.outer.count | exact h.outer.available | exact h.outer.index
  all_goals simp (disch := decide) only [multiDelegatedAttestCopyCheckLocals,heapResultLocals_get]
  all_goals first | exact h.request | exact h.data | exact h.signatures | exact h.last | exact h.index

theorem multiDelegatedAttestCopyRun {L : Store} {evm : EVM.State} {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem : ByteArray} {aw : UInt256} {out : ByteArray} {σ : AccountMap} {k C n i : Nat}
    {root base table available heap : UInt256} {requests : List Value} {groups : List (List UInt256)} {R : List UInt256}
    (v : EASImmutables) (hstack : R.length+45≤1024) (hstate : SourceState s0 ee σ evm)
    (hsize : ee.calldata.size<2^255) (hbase : base=checkAttestationCopyBase ee.calldata)
    (hroot : root=multiRequestRoot ee.calldata base i) (hslot : base.toNat+32*i<UInt256.size)
    (hb : DelegatedAttestationBatchReady ee.calldata root)
    (hf : MultiDelegatedAttestVerifyLocals L requests groups available heap.toNat i (delegatedAttestationDataLength ee.calldata root).toNat
      (decide (i=n-1)) (delegatedAttestationTuple ee.calldata root) (delegatedAttestationDataList ee.calldata root) (delegatedAttestationSigList ee.calldata root))
    (hgood : ∀ t, t<(delegatedAttestationDataLength ee.calldata root).toNat →
      delegatedAttestationDataValid ee.calldata (delegatedAttestationDataOffset ee.calldata root) t ∧ delegatedBatchAddressClean ee.calldata root)
    (hlo : 96≤heap.toNat) (hh : heap.toNat≤2^64-1) (hfree : memLoad (UInt256.ofNat 64) mem=heap)
    (rd : RD fork (deployedRuntime v) ee g s0 ⟨2874⟩
      (multiDelegatedAttestVerifyStack ee.calldata (delegatedAttestationDataLength ee.calldata root).toNat root
        (delegatedAttestationDataOffset ee.calldata root) base (UInt256.ofNat n) (delegatedAttestationDataLength ee.calldata root)
        available table (UInt256.ofNat groups.flatten.length) (UInt256.ofNat i) (UInt256.ofNat n-⟨1⟩) R) mem aw out σ k C) :
    (∃ L' mem' aw' k' C' next,
      heap.toNat≤next ∧ next≤2^64-1 ∧ MemoryPrefix mem mem' heap.toNat ∧
      AttestationRequestArrayRegion mem' heap (delegatedAttestationRecords ee.calldata root) heap.toNat next ∧
      memLoad (UInt256.ofNat 64) mem'=UInt256.ofNat next ∧
      ExecBlock fork config {contract := contract,locals := L,immutables := immStore v} evm
        (multiDelegatedAttestCopyCheck++multiDelegatedAttestArrayCopy)
        (.ok {contract := contract,locals := L',immutables := immStore v} evm) ∧
      MultiDelegatedAttestVerifyLocals L' requests groups available next i (delegatedAttestationDataLength ee.calldata root).toNat
        (decide (i=n-1)) (delegatedAttestationTuple ee.calldata root) (delegatedAttestationDataList ee.calldata root) (delegatedAttestationSigList ee.calldata root) ∧
      RD fork (deployedRuntime v) ee g s0 ⟨3125⟩
        (heap::multiDelegatedAttestCopySaved ee.calldata root n i base table available (UInt256.ofNat groups.flatten.length) R) mem' aw' out σ k' C') ∨
    (ExecBlock fork config {contract := contract,locals := L,immutables := immStore v} evm
      (multiDelegatedAttestCopyCheck++multiDelegatedAttestArrayCopy) .reverted ∧ RDrev fork (deployedRuntime v) g s0) := by
  let rs := delegatedAttestationRecords ee.calldata root
  have hlen : rs.length=(delegatedAttestationDataLength ee.calldata root).toNat := delegatedAttestationRecords_length ..
  have hbounds := hb.bounds hsize
  have hlencap : rs.length≤2^64-1 := by rw [hlen];exact hbounds.1
  have hspan : (delegatedAttestationDataOffset ee.calldata root).toNat+32*rs.length<UInt256.size := by rw [hlen];exact hbounds.2.1
  have hdata := delegatedAttestationDataList_verified hbounds.2.1 (fun t ht => (hgood t ht).1)
  have hargs : evalExprs? config {contract := contract,locals := L,immutables := immStore v} evm multiDelegatedAttestCopyCheckArgs=
      .ok [.int (Int.ofNat i),.int (Int.ofNat rs.length),.int (Int.ofNat heap.toNat)] := by
    simp only [multiDelegatedAttestCopyCheckArgs,evalExprs?,evalExpr?,hf.outer.index,hf.data,hf.outer.heap,readLocalPath?,
      EvalResult.ofOption,bind,EvalResult.bind,pure,delegatedAttestationDataList_length,hlen]
    rfl
  have hcheck := checkAttestationCopyCall (fork := fork) (retVar := "__copyCheck$allocation") hargs (by change rs.length<2^256;omega)
  rw [hstate.env] at hcheck
  obtain ⟨a1,k1,C1,r1⟩ := easMultiDelegatedAttestVerifyDone v (by omega) (hgood 0 hb.nonempty).2 rd
  have hword : delegatedAttestationDataLength ee.calldata root=UInt256.ofNat rs.length := by rw [hlen,u256_ofNat_toNat]
  rw [hword] at r1
  have hiff := checkAttestationCopyValid_iff hbase hslot (by rw [← hroot];exact hspan) (by change ee.calldata.size<2^256;omega)
  rw [← hroot] at hiff
  by_cases hv : checkAttestationCopyValid ee.calldata i rs.length
  · let L1 := multiDelegatedAttestCopyCheckLocals L heap.toNat
    have hf1 : MultiDelegatedAttestVerifyLocals L1 requests groups available heap.toNat i (delegatedAttestationDataLength ee.calldata root).toNat
        (decide (i=n-1)) (delegatedAttestationTuple ee.calldata root) (delegatedAttestationDataList ee.calldata root) (delegatedAttestationSigList ee.calldata root) := hf.copyChecked
    have hsol1 : ExecBlock fork config {contract := contract,locals := L,immutables := immStore v} evm multiDelegatedAttestCopyCheck
        (.ok {contract := contract,locals := L1,immutables := immStore v} evm) :=
      heapResultBlock_ok (result := "__copyCheck") (cursor := "$EAS.freeMemory") (hcheck.1 hv) hf.outer.heap (by decide) (by decide) (by decide)
    have hecopy : evalExprs? config {contract := contract,locals := L1,immutables := immStore v} evm [.var "data",.var "$EAS.freeMemory"]=
        .ok [.array (rs.map AttestationRequestRecord.tuple),.int (Int.ofNat heap.toNat)] := by
      simp only [evalExprs?,evalExpr?,hf1.data,hf1.outer.heap,hdata,EvalResult.ofOption,bind,EvalResult.bind,pure]
      rfl
    have hvalid := hiff.mp hv
    have hview : RequestArrayCalldataView ee.calldata (delegatedAttestationDataOffset ee.calldata root) rs :=
      delegatedAttestationRecords_view (fun t ht => (hgood t ht).1) (by rw [← hlen];exact hvalid.1)
        (by intro t ht;exact hvalid.2 t (by rw [hlen];exact ht))
    have hcopy := copyRequestArrayCallRun (retVar := "allocation$allocation")
      (R := multiDelegatedAttestCopySaved ee.calldata root n i base table available (UInt256.ofNat groups.flatten.length) R)
      v (by simp only [multiDelegatedAttestCopySaved,multiDelegatedAttestSaved,List.length_cons,List.length_append,List.length_nil];omega)
      hecopy hview (by omega) hlo hh hfree (by rw [easPatchedValidJumps v];jump_dest) r1
    rcases hcopy with ⟨m2,a2,k2,C2,next,hlo2,hh2,hp2,hv2,hf2,hs2,r2⟩ | ⟨hs2,hrev⟩
    · let L2 := multiAttestCopyLocals L1 next
      have hsol2 : ExecBlock fork config {contract := contract,locals := L1,immutables := immStore v} evm multiDelegatedAttestArrayCopy
          (.ok {contract := contract,locals := L2,immutables := immStore v} evm) :=
        heapResultBlock_ok (result := "allocation") (cursor := "$EAS.freeMemory") hs2 hf1.outer.heap (by decide) (by decide) (by decide)
      exact Or.inl ⟨L2,m2,a2,k2,C2,next,hlo2,hh2,hp2,hv2,hf2,execBlock_append hsol1 hsol2,hf1.copied next,r2⟩
    · exact Or.inr ⟨execBlock_append hsol1 (ExecBlock.consRevert hs2),hrev⟩
  · have hrev : RDrev fork (deployedRuntime v) g s0 := easCopyRequestArrayInvalid evm v
      (by simp only [multiDelegatedAttestCopySaved,multiDelegatedAttestSaved,List.length_cons,List.length_append,List.length_nil];omega)
      hspan hlencap (by omega)
      (by intro t ht;exact ⟨(hgood t (by rw [← hlen];exact ht)).1.2,(delegatedAttestationRecords_get _ _ _ ht).symm⟩)
      (fun h => hv (hiff.mpr h)) hlo hh hfree r1
    refine Or.inr ⟨?_,hrev⟩
    exact execBlock_append_term (ExecBlock.consRevert (stmts := multiDelegatedAttestCopyCheck.tail) (hcheck.2 hv)) (by intros;exact nofun)

end Benchmarks.EAS.EAS
