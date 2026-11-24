import Benchmarks.EAS.EAS.TryRecoverControl

variable {fork : Ethereum.Fork}
open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables Benchmarks.EAS.EAS.Immutables
namespace Benchmarks.EAS.EAS
set_option maxRecDepth 10000

def tryRecoverOutputMemory (mem : ByteArray) (heap hash sigV r s : UInt256) (out : ByteArray) : ByteArray :=
  callOutputMem (tryRecoverInputMemory mem heap hash sigV r s) out ⟨0⟩ ⟨32⟩

theorem tryRecoverLowEVM {ee : ExecutionEnv} {g : Sat256} {s0 evm : EVM.State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : Nat}
    {heap hash sigV r s ret : UInt256} {R : List UInt256} (v : EASImmutables)
    (hstack : R.length+11 ≤ 1024) (hi : ¬ ecdsaHalfOrder < s.toNat)
    (hs : SourceState s0 ee σ evm) (hh : memLoad (UInt256.ofNat 64) mem = heap)
    (hmem : 96 ≤ mem.size) (hv : sigV.toNat < 2^8)
    (hlo : 96 ≤ heap.toNat) (hb : heap.toNat+128 < UInt256.size)
    (hret : (D_J (deployedRuntime v) 0).contains ret = true)
    (rd : RD fork (deployedRuntime v) ee g s0 ⟨16645⟩ (hash::sigV::r::s::ret::R) mem aw rdata σ k C) :
    ∃ (evm' : EVM.State) (σ' : AccountMap) (success : Bool) (out : ByteArray) (a : AccountAddress),
      callViaEVM fork evm (AccountAddress.ofUInt256 (⟨1⟩ : UInt256)) 0 (tryRecoverPayload hash sigV r s)
        (success,evm',out) false ∧ SourceState s0 ee σ' evm' ∧
      ((out = ByteArray.empty ∧ a = 0) ∨ out = (UInt256.ofNat a.val).toByteArray) ∧
      MemoryPrefix mem (tryRecoverOutputMemory mem heap hash sigV r s out) heap.toNat ∧
      memLoad (UInt256.ofNat 64) (tryRecoverOutputMemory mem heap hash sigV r s out) = heap ∧
      (if success then ∃ aw' k' C', RD fork (deployedRuntime v) ee g s0 ret
        (UInt256.ofNat (recoveryError a)::UInt256.ofNat a.val::R)
        (tryRecoverOutputMemory mem heap hash sigV r s out) aw' out σ' k' C'
       else RDrev fork (deployedRuntime v) g s0) := by
  obtain ⟨gasArg,aw1,k1,C1,r1⟩ := tryRecoverStart v hstack hi hh hv hb rd
  obtain ⟨evm',σ',success,out,k2,C2,hcall,hs',r2,_⟩ :=
    staticcallBridge r1 hs (tryRecoverCall_decode v) (tryRecoverInputMemory_read hlo)
      (by simp only [tryRecoverPayload,wordBytes_size,List.length_cons,List.length_nil]; decide +kernel)
      (by simp only [List.length_cons]; omega)
  obtain ⟨a,hout⟩ : ∃ a : AccountAddress,
      (out = ByteArray.empty ∧ a = 0) ∨ out = (UInt256.ofNat a.val).toByteArray := by
    rcases ecrecoverOutput_call hcall with he | ⟨a,he⟩
    · exact ⟨0,Or.inl ⟨he,rfl⟩⟩
    · exact ⟨a,Or.inr he⟩
  have hzero : memLoad ⟨0⟩ (tryRecoverInputMemory mem heap hash sigV r s) = ⟨0⟩ := by
    apply mloadWordValue_of_readWithPadding
    · change 0 < (Reasoning.Theory.writeWord _ 0 ⟨0⟩).size
      rw [writeWord_sparse_size]
      omega
    exact writeWord_sparse_read_back _ _ _
  have hc := tryRecoverInputMemory_covers mem heap hash sigV r s
  have ⟨ha,hprefix,hfree⟩ := ecrecoverOutputMemory (limit := heap.toNat) hout hzero (by omega)
  refine ⟨evm',σ',success,out,a,hcall,hs',hout,
    (tryRecoverInputMemory_prefix mem heap hash sigV r s).trans hprefix,?_,?_⟩
  · exact hfree.trans (tryRecoverInputMemory_free hlo hmem hh)
  · exact tryRecoverFinish v success (by omega) ha hret r2

end Benchmarks.EAS.EAS
