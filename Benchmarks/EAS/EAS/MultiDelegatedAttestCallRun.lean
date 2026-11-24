import Benchmarks.EAS.EAS.MultiDelegatedAttestCallSource
import Benchmarks.EAS.EAS.MultiAttestMemory
import Benchmarks.EAS.EAS.MultiDelegatedAttestUpdate

variable {fork : Ethereum.Fork}
open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables Benchmarks.EAS.EAS.Immutables
namespace Benchmarks.EAS.EAS
set_option maxRecDepth 10000

theorem multiDelegatedAttestCallUpdateRun {L : Store} {evm : EVM.State} {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C n i : Nat}
    {root data base table available heap : UInt256} {requests : List Value}
    {rs : List AttestationRequestRecord} {groups : List (List UInt256)} {R : List UInt256}
    (v : EASImmutables) (hstack : R.length+48 ≤ 1024) (hstate : SourceState s0 ee σ evm)
    (hf : MultiDelegatedAttestLocals L requests groups available heap.toNat i)
    (hm : MultiAttestMemory mem table groups i heap.toNat) (hh : heap.toNat ≤ 2^64-1)
    (hi : i < n) (hn : n < UInt256.size) (hg : groups.length = n)
    (hrow : L.get? "multiDelegatedRequest" = some (delegatedAttestationTuple ee.calldata root))
    (hdata : L.get? "data"=some (.array (rs.map AttestationRequestRecord.tuple)))
    (ha : delegatedBatchAddressClean ee.calldata root)
    (hlast : L.get? "last" = some (.bool (decide (i=n-1))))
    (hd : AttestationRequestArrayRegion mem data rs 224 heap.toNat)
    (hsize : ee.calldata.size < UInt256.size)
    (rd : RD fork (deployedRuntime v) ee g s0 ⟨9856⟩
      (calldataWord ee.calldata root.toNat::data::calldataWord ee.calldata (root+UInt256.ofNat 96).toNat::available::multiAttestLastWord n i::⟨3131⟩::
        multiDelegatedAttestSaved n i base table available (UInt256.ofNat groups.flatten.length) R) mem aw rdata σ k C) :
    (∃ (L' : Store) (evm' : EVM.State) (σ' : AccountMap) (mem' out : ByteArray) (aw' : UInt256)
        (k' C' next : Nat) (words : List UInt256) (used : UInt256),
      SourceState s0 ee σ' evm' ∧ heap.toNat ≤ next ∧ next ≤ 2^64-1 ∧
      MultiDelegatedAttestLocals L' requests (groups.set i words) (UInt256.sub available used) next (i+1) ∧
      MultiAttestMemory mem' table (groups.set i words) (i+1) next ∧
      ExecBlock fork config {contract := contract,locals := L,immutables := immStore v} evm (multiDelegatedAttestCall++multiAttestUpdate)
        (.ok {contract := contract,locals := L',immutables := immStore v} evm') ∧
      RD fork (deployedRuntime v) ee g s0 ⟨2777⟩
        (multiDelegatedAttestLoopStack n (i+1) base (UInt256.sub available used)
          (UInt256.ofNat (groups.set i words).flatten.length) table R) mem' aw' out σ' k' C') ∨
    (ExecBlock fork config {contract := contract,locals := L,immutables := immStore v} evm (multiDelegatedAttestCall++multiAttestUpdate) .reverted ∧
      RDrev fork (deployedRuntime v) g s0) ∨
    (ExecBlock fork config {contract := contract,locals := L,immutables := immStore v} evm (multiDelegatedAttestCall++multiAttestUpdate) .staticViolation ∧
      RDstatic fork (deployedRuntime v) g s0) := by
  have he := multiDelegatedAttestCallArgs_eval (imms := immStore v) (evm := evm) hrow hdata ha hf.available hlast hf.heap
  have haword := delegatedAttestationAttester_word ha
  rw [← haword] at rd
  have hfree : memLoad (UInt256.ofNat 64) mem = heap := by simpa only [u256_ofNat_toNat] using hm.free
  have hr := attestCallRun (retVar := "res$allocation") (ret := ⟨3131⟩)
    (R := multiDelegatedAttestSaved n i base table available (UInt256.ofNat groups.flatten.length) R) v .many he
    (by simp only [multiDelegatedAttestSaved,List.length_cons,List.length_append,List.length_nil]; omega) hstate hd hh hfree hm.zero (by intro h; cases h)
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
    have hf1 : MultiDelegatedAttestLocals L1 requests groups available next i := hf.called words used next
    have hres : L1.get? "res" = some (attestationsResultValue words used) := heapResultLocals_result _ _ _ _ _ _ (by decide)
    have hsol1 : ExecBlock fork config {contract := contract,locals := L,immutables := immStore v} evm multiDelegatedAttestCall
        (.ok {contract := contract,locals := L1,immutables := immStore v} e1) :=
      heapResultBlock_ok hcall hf.heap (by decide) (by decide) (by decide)
    have hsol2 := multiAttestUpdateSourceOfFields (fork := fork) (evm := e1) (imms := immStore v) hf1.groups hf1.count hf1.available hf1.index hres hi' (by omega) hc hu
    obtain ⟨a2,j2,D2,r2⟩ := easMultiDelegatedAttestUpdate (R := R) v (by omega) hi (by simpa only [hg] using hend) hb' hv
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
