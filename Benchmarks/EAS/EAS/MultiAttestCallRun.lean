import Benchmarks.EAS.EAS.MultiAttestUpdateSource
import Benchmarks.EAS.EAS.MultiAttestMemory
import Benchmarks.EAS.EAS.MultiAttestUpdate

variable {fork : Ethereum.Fork}
open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables Benchmarks.EAS.EAS.Immutables
namespace Benchmarks.EAS.EAS
set_option maxRecDepth 10000

theorem multiAttestCallUpdateRun {L : Store} {evm : EVM.State} {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C n i : Nat}
    {schema data base table available heap : UInt256} {requests : List Value}
    {rs : List AttestationRequestRecord} {groups : List (List UInt256)} {R : List UInt256}
    (v : EASImmutables) (hstack : R.length+48 ≤ 1024) (hstate : SourceState s0 ee σ evm)
    (hf : MultiAttestLocals L requests groups available heap.toNat i)
    (hm : MultiAttestMemory mem table groups i heap.toNat) (hh : heap.toNat ≤ 2^64-1)
    (hi : i < n) (hn : n < UInt256.size) (hg : groups.length = n)
    (hrow : L.get? "multiRequest" = some (multiRequestTuple schema rs))
    (hlast : L.get? "last" = some (.bool (decide (i=n-1))))
    (hd : AttestationRequestArrayRegion mem data rs 224 heap.toNat)
    (hsize : ee.calldata.size < UInt256.size)
    (rd : RD fork (deployedRuntime v) ee g s0 ⟨9856⟩
      (schema::data::UInt256.ofNat ee.source.val::available::multiAttestLastWord n i::⟨3131⟩::
        multiAttestSaved n i base table available (UInt256.ofNat groups.flatten.length) R) mem aw rdata σ k C) :
    (∃ (L' : Store) (evm' : EVM.State) (σ' : AccountMap) (mem' out : ByteArray) (aw' : UInt256)
        (k' C' next : Nat) (words : List UInt256) (used : UInt256),
      SourceState s0 ee σ' evm' ∧ heap.toNat ≤ next ∧ next ≤ 2^64-1 ∧
      MultiAttestLocals L' requests (groups.set i words) (UInt256.sub available used) next (i+1) ∧
      MultiAttestMemory mem' table (groups.set i words) (i+1) next ∧
      ExecBlock fork config {contract := contract,locals := L,immutables := immStore v} evm (multiAttestCall++multiAttestUpdate)
        (.ok {contract := contract,locals := L',immutables := immStore v} evm') ∧
      RD fork (deployedRuntime v) ee g s0 ⟨3767⟩
        (multiAttestLoopStack n (i+1) base table (UInt256.sub available used)
          (UInt256.ofNat (groups.set i words).flatten.length) R) mem' aw' out σ' k' C') ∨
    (ExecBlock fork config {contract := contract,locals := L,immutables := immStore v} evm (multiAttestCall++multiAttestUpdate) .reverted ∧
      RDrev fork (deployedRuntime v) g s0) ∨
    (ExecBlock fork config {contract := contract,locals := L,immutables := immStore v} evm (multiAttestCall++multiAttestUpdate) .staticViolation ∧
      RDstatic fork (deployedRuntime v) g s0) := by
  have he : evalExprs? config {contract := contract,locals := L,immutables := immStore v} evm multiAttestCallArgs =
      .ok [wordBytes32Value schema,.array (rs.map AttestationRequestRecord.tuple),.address ee.source,
        .int (Int.ofNat available.toNat),.bool (decide (i=n-1)),.int (Int.ofNat heap.toNat)] := by
    simp only [multiAttestCallArgs,evalExprs?,evalExpr?,hrow,hf.available,hlast,hf.heap,multiRequestTuple,
      EvalResult.ofOption,bind,EvalResult.bind,pure,envValue,hstate.env]
    rfl
  have hfree : memLoad (UInt256.ofNat 64) mem = heap := by simpa only [u256_ofNat_toNat] using hm.free
  have hr := attestCallRun (retVar := "res$allocation") (ret := ⟨3131⟩)
    (R := multiAttestSaved n i base table available (UInt256.ofNat groups.flatten.length) R) v .many he
    (by simp only [multiAttestSaved,List.length_cons]; omega) hstate hd hh hfree hm.zero (by intro h; cases h)
    hsize (by rw [easPatchedValidJumps v]; jump_dest)
    (by simpa only [attestEntryStack,AttestCallKind.entryPC,multiAttestLastWord_eq hi hn] using rd)
  rcases hr with ⟨e1,σ1,m1,out,a1,j1,D1,next,words,used,hs1,hlo,hb,_,hu,hp,hv,hfree1,hcall,r1⟩ |
    ⟨hcall,hrev⟩ | ⟨hcall,hstatic⟩
  · let L1 := multiAttestCallLocals L words used next
    let L2 := multiAttestNextLocals L1 groups words available used i
    let uid := UInt256.ofNat (allocateNext heap.toNat 128)
    let m2 := Reasoning.Theory.writeWord m1 (table.toNat+32+32*i) uid
    have hb' : next < UInt256.size := by change next < 2^256; omega
    have hi' : i < groups.length := by omega
    obtain ⟨hm1,hend⟩ := multiAttestReturnedMemory hm hh hd hp hv hlo hb hfree1
    have hm2 : MultiAttestMemory m2 table (groups.set i words) (i+1) next :=
      hm1.set hi' hv.uids (by dsimp only [uid]; have := hv.span; omega) hb'
    have hcount := flattenLength_set_empty groups words i hi' (hm.empty i hi' (le_refl _))
    have hc : groups.flatten.length+words.length < UInt256.size := by
      rw [← hcount]
      exact hm2.flatten_fit hb
    have hf1 : MultiAttestLocals L1 requests groups available next i := hf.called words used next
    have hres : L1.get? "res" = some (attestationsResultValue words used) := heapResultLocals_result _ _ _ _ _ _ (by decide)
    have hsol1 : ExecBlock fork config {contract := contract,locals := L,immutables := immStore v} evm multiAttestCall
        (.ok {contract := contract,locals := L1,immutables := immStore v} e1) :=
      heapResultBlock_ok hcall hf.heap (by decide) (by decide) (by decide)
    have hsol2 := multiAttestUpdateSource (fork := fork) (evm := e1) (imms := immStore v) hf1 hres hi' (by omega) hc hu
    obtain ⟨a2,j2,D2,r2⟩ := easMultiAttestUpdate (R := R) v (by omega) hi (by simpa only [hg] using hend) hb' hv
      (by simpa only [hg] using hm1.view.length) hu r1
    have hcountWord : UInt256.ofNat words.length+UInt256.ofNat groups.flatten.length =
        UInt256.ofNat (groups.set i words).flatten.length := by
      apply u256_inj
      rw [uadd_toNat,ulit_toNat' words.length (by omega),ulit_toNat' groups.flatten.length (by omega),
        Nat.mod_eq_of_lt (by omega),hcount,ulit_toNat' _ hc]
      omega
    refine Or.inl ⟨L2,e1,σ1,m2,out,a2,j2,D2,next,words,used,hs1,hlo,hb,
      hf1.next words used hi' (hm.empty i hi' (le_refl _)),hm2,execBlock_append hsol1 hsol2,?_⟩
    simpa only [hcountWord] using r2
  · refine Or.inr (Or.inl ⟨?_,hrev⟩)
    exact execBlock_append_term (ExecBlock.consRevert hcall) (by intros; exact nofun)
  · refine Or.inr (Or.inr ⟨?_,hstatic⟩)
    exact execBlock_append_term (ExecBlock.consStatic hcall) (by intros; exact nofun)

end Benchmarks.EAS.EAS
