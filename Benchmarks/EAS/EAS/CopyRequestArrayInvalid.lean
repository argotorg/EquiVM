import Benchmarks.EAS.EAS.CopyRequestArrayStep

variable {fork : Ethereum.Fork}
open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables Benchmarks.EAS.EAS.Immutables
namespace Benchmarks.EAS.EAS
set_option maxRecDepth 10000

theorem copyRequestArrayLoopInvalid {L : Store} (evm : EVM.State) {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem : ByteArray} {aw : UInt256} {out : ByteArray} {σ : AccountMap} {k C : Nat}
    {offset array heap ret : UInt256} {rs : List AttestationRequestRecord} {i : Nat} {R : List UInt256}
    (v : EASImmutables) (hstack : R.length+23≤1024)
    (hcb : offset.toNat+32*rs.length≤ee.calldata.size) (hsize : ee.calldata.size<2^255+4)
    (hrequests : ∀ t (ht : t<rs.length), requestDataValid ee.calldata (requestArrayElement ee.calldata offset t) ∧
      requestDataRecord ee.calldata (requestArrayElement ee.calldata offset t)=rs[t])
    (n : Nat) (hn : i+n=rs.length)
    (hbad : ∃ t, i≤t ∧ t<rs.length ∧ ¬(calldataWord ee.calldata (offset.toNat+32*t)).toNat≤2^64-1)
    (hf : CopyRequestArrayLocals L rs heap.toNat i) (hm : CopyRequestArrayMemory mem array rs i heap.toNat)
    (hh : heap.toNat≤2^64-1) (hfree : memLoad (UInt256.ofNat 64) mem=heap)
    (rd : RD fork (deployedRuntime v) ee g s0 ⟨5594⟩
      (UInt256.ofNat (array.toNat+32+32*i)::UInt256.ofNat (offset.toNat+32*i)::offset::
        UInt256.ofNat (offset.toNat+32*rs.length)::UInt256.ofNat ee.calldata.size::ret::array::R) mem aw out σ k C) :
    RDrev fork (deployedRuntime v) g s0 := by
  induction n generalizing i L mem aw heap k C with
  | zero => obtain ⟨t,ht,hlt,_⟩ := hbad;omega
  | succ n ih =>
    have hi : i<rs.length := by omega
    by_cases ho : (calldataWord ee.calldata (offset.toNat+32*i)).toNat≤2^64-1
    · rcases copyRequestArrayStepOfElement (evm := evm) v hstack hf hm hcb hi ⟨ho,hrequests i hi⟩ hh hfree hsize rd with
        ⟨L1,m1,a1,k1,C1,next,_,hhi,_,hf1,hm1,hfree1,_,r1⟩ | ⟨_,hrev⟩
      · have hword : (UInt256.ofNat next).toNat=next := ulit_toNat' _ (by change next<2^256;omega)
        apply ih (by omega) ?_ (by rw [hword];exact hf1) (by rw [hword];exact hm1) (by rw [hword];exact hhi) hfree1 r1
        obtain ⟨t,ht,hlt,hbad⟩ := hbad
        refine ⟨t,?_,hlt,hbad⟩
        have hne : i≠t := by intro he;subst t;exact hbad ho
        omega
      · exact hrev
    · apply (easCopyRequestArrayRead v (by omega) ?_ rd).2
      · have hs : (UInt256.ofNat (offset.toNat+32*i)).toNat=offset.toNat+32*i := ulit_toNat' _ (by change _<2^256;omega)
        simpa only [hs] using ho
      · rw [ulit_toNat' _ (by change offset.toNat+32*i<2^256;omega),
          ulit_toNat' _ (by change offset.toNat+32*rs.length<2^256;omega)]
        omega

set_option maxHeartbeats 700000 in
theorem easCopyRequestArrayInvalid (evm : EVM.State) {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem : ByteArray} {aw : UInt256} {out : ByteArray} {σ : AccountMap} {k C : Nat}
    {offset heap ret : UInt256} {rs : List AttestationRequestRecord} {R : List UInt256}
    (v : EASImmutables) (hstack : R.length+23≤1024)
    (hspan : offset.toNat+32*rs.length<UInt256.size) (hlen : rs.length≤2^64-1) (hsize : ee.calldata.size<2^255+4)
    (hrequests : ∀ t (ht : t<rs.length), requestDataValid ee.calldata (requestArrayElement ee.calldata offset t) ∧
      requestDataRecord ee.calldata (requestArrayElement ee.calldata offset t)=rs[t])
    (hbad : ¬(offset.toNat+32*rs.length≤ee.calldata.size ∧
      ∀ t, t<rs.length → (calldataWord ee.calldata (offset.toNat+32*t)).toNat≤2^64-1))
    (hlo : 96≤heap.toNat) (hh : heap.toNat≤2^64-1) (hfree : memLoad (UInt256.ofNat 64) mem=heap)
    (rd : RD fork (deployedRuntime v) ee g s0 ⟨5544⟩
      (offset::UInt256.ofNat rs.length::UInt256.ofNat ee.calldata.size::ret::R) mem aw out σ k C) :
    RDrev fork (deployedRuntime v) g s0 := by
  have hn : (UInt256.ofNat rs.length).toNat=rs.length := ulit_toNat' _ (by change _<2^256;omega)
  have he : offset+UInt256.shiftLeft (UInt256.ofNat rs.length) (UInt256.ofNat 5)=UInt256.ofNat (offset.toNat+32*rs.length) := by
    have hs : UInt256.shiftLeft (UInt256.ofNat rs.length) (UInt256.ofNat 5)=UInt256.ofNat (32*rs.length) := shiftLeft5_ofNat_eq (by change _<2^256;omega)
    rw [hs]
    apply u256_inj
    rw [uadd_word_ofNat_toNat _ _ hspan,ulit_toNat' _ hspan]
  have hhead := easCopyRequestArrayHead v (by omega) hfree rd
  by_cases hv : requestArrayHeadValid offset (UInt256.ofNat rs.length) (UInt256.ofNat ee.calldata.size) heap
  · have hg := hv.2.2
    rw [he] at hg
    have hcb : offset.toNat+32*rs.length≤ee.calldata.size := by
      have hg1 := ugt_eq_zero_to_le hg
      rw [ulit_toNat' _ hspan,ulit_toNat' _ (by change ee.calldata.size<2^256;omega)] at hg1
      exact hg1
    have ha := hv.2.1
    rw [hn] at ha
    obtain ⟨a1,k1,C1,r1⟩ := hhead.1 hv
    rw [hn,he] at r1
    let next := allocateNext heap.toNat (32+32*rs.length)
    let L0 := copyRequestArrayArgs rs heap.toNat
    let L1 := (allocateBlockLocals L0 next).insert "i" (.int 0)
    have hnext : (UInt256.ofNat next).toNat=next := ulit_toNat' _ (by change next<2^256;have hcap : next≤2^64-1 := ha.1;omega)
    have hdptr : heap+UInt256.ofNat 32=UInt256.ofNat (heap.toNat+32) := by
      apply u256_inj
      rw [uadd_word_ofNat_toNat _ _ (by change _<2^256;omega),ulit_toNat' _ (by change _<2^256;omega)]
    rw [hdptr] at r1
    have hr1 : RD fork (deployedRuntime v) ee g s0 ⟨5594⟩
        (UInt256.ofNat (heap.toNat+32+32*0)::UInt256.ofNat (offset.toNat+32*0)::offset::
          UInt256.ofNat (offset.toNat+32*rs.length)::UInt256.ofNat ee.calldata.size::ret::heap::R)
        (arrayAllocationHeaderMemory mem heap rs.length) a1 out σ k1 C1 := by
      simpa only [Nat.mul_zero,Nat.add_zero,u256_ofNat_toNat] using r1
    obtain ⟨_,hm0,hf0⟩ := copyRequestArrayMemory_init mem heap rs hlo hh hlen
    have hf1 : CopyRequestArrayLocals L1 rs (UInt256.ofNat next).toNat 0 := by
      rw [hnext]
      constructor
      · simp (disch := decide) only [L1,L0,copyRequestArrayArgs,allocateBlockLocals,unpackHeapLocals,store_get_ne,store_get_self]
      · simp (disch := decide) only [L1,allocateBlockLocals,unpackHeapLocals,store_get_ne,store_get_self]
      · exact store_get_self _ _ _
    apply copyRequestArrayLoopInvalid evm v hstack hcb hsize hrequests rs.length (by omega) ?_ hf1
      (by rw [hnext];exact hm0) (by rw [hnext];exact ha.1) hf0 hr1
    have hnot : ¬∀ t, t<rs.length → (calldataWord ee.calldata (offset.toNat+32*t)).toNat≤2^64-1 := fun h => hbad ⟨hcb,h⟩
    push_neg at hnot
    obtain ⟨t,ht,hbad⟩ := hnot
    exact ⟨t,Nat.zero_le _,ht,by omega⟩
  · exact hhead.2 hv

end Benchmarks.EAS.EAS
