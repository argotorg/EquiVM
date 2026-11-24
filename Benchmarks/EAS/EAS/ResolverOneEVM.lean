import Benchmarks.EAS.EAS.ResolverCallData
import Benchmarks.EAS.EAS.ResolverReturn
import Benchmarks.EAS.EAS.ResolverCallSites

variable {fork : Ethereum.Fork}
open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables Benchmarks.EAS.EAS.Immutables
namespace Benchmarks.EAS.EAS
set_option maxRecDepth 10000

def resolverOneEntryPC (rev : Bool) : UInt256 := if rev then ⟨15794⟩ else ⟨16004⟩
abbrev resolverOnePreparePC (rev : Bool) : UInt256 := resolverPreparePC false rev
abbrev resolverOneCallPC (rev : Bool) : UInt256 := resolverCallPC false rev

theorem resolverOneStart {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap}
    {k C : Nat} {src ptr target value : UInt256} {R : List UInt256} (v : EASImmutables) (rev : Bool)
    (hstack : R.length+12 ≤ 1024) (hb : ptr.toNat+36 < UInt256.size)
    (hh : memLoad (UInt256.ofNat 64) mem = ptr)
    (rd : RD fork (deployedRuntime v) ee g s0 (resolverOneEntryPC rev) (target::src::⟨32⟩::value::R) mem aw rdata σ k C) :
    ∃ aw' k' C', RD fork (deployedRuntime v) ee g s0 ⟨4502⟩
      (src::(ptr+UInt256.ofNat 36)::resolverOnePreparePC rev::ptr::value::ptr::target::ptr::⟨32⟩::ptr::R)
      (resolverOneHeaderMemory mem ptr rev) aw' rdata σ k' C' := by
  have hm := resolverOneHeaderMemory_eq mem ptr rev hh hb
  cases rev with
  | false =>
    obtain ⟨aw1,k1,C1,rd1⟩ := easBlocks.eas_block_16004_packed (immWords := wordsOf (immStore v)) hstack
      (by rw [easPatchedValidJumpsRuntime v]; jump_dest) rd
    refine ⟨aw1,k1,C1,?_⟩
    rw [← hm]
    simpa only [easBlocks.eas_block_16004_stack, hh, resolverOnePreparePC, resolverPreparePC,
      Bool.false_eq_true, if_false] using rd1
  | true =>
    obtain ⟨aw1,k1,C1,rd1⟩ := easBlocks.eas_block_15794_packed (immWords := wordsOf (immStore v)) hstack
      (by rw [easPatchedValidJumpsRuntime v]; jump_dest) rd
    refine ⟨aw1,k1,C1,?_⟩
    rw [← hm]
    simpa only [easBlocks.eas_block_15794_stack, hh, resolverOnePreparePC, resolverPreparePC, if_true] using rd1

theorem resolverOnePrepare {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap}
    {k C : Nat} {finish ptr target value : UInt256} {R : List UInt256} (v : EASImmutables) (rev : Bool)
    (hstack : R.length+8 ≤ 1024)
    (rd : RD fork (deployedRuntime v) ee g s0 (resolverOnePreparePC rev)
      (finish::ptr::value::ptr::target::ptr::⟨32⟩::ptr::R) mem aw rdata σ k C) :
    ∃ gasArg aw' k' C', RD fork (deployedRuntime v) ee g s0 (resolverOneCallPC rev)
      (gasArg::target::value::ptr::UInt256.sub finish ptr::ptr::⟨32⟩::ptr::R) mem aw' rdata σ k' C' := by
  exact resolverPrepare v false rev hstack rd

theorem resolverOneCall_decode (v : EASImmutables) (rev : Bool) :
    decode (deployedRuntime v) (resolverOneCallPC rev) = some (.CALL, none) := by
  exact resolverCall_decode v false rev

def resolverOneCallOutput (mem : ByteArray) (src ptr dataPtr : UInt256) (rev : Bool) (out : ByteArray) : ByteArray :=
  resolverReturnMemory (callOutputMem (resolverOneEncodedMemory mem src ptr dataPtr rev) out ptr ⟨32⟩) ptr out

theorem resolverOneEVM {ee : ExecutionEnv} {g : Sat256} {s0 evm : EVM.State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap}
    {k C : Nat} {src ptr dataPtr target value : UInt256} {R : List UInt256}
    {a : AttestationRecord} (v : EASImmutables) (rev : Bool)
    (hstack : R.length+22 ≤ 1024) (hperm : ee.perm = true)
    (hstate : SourceState s0 ee σ evm) (hview : AttestationMemoryView mem src dataPtr a)
    (hs : src.toNat+320 ≤ ptr.toNat) (hd : dataPtr.toNat+32+32*((a.data.size+31)/32) ≤ ptr.toNat)
    (hheap : ptr.toNat ≤ 2^64-1) (hh : memLoad (UInt256.ofNat 64) mem = ptr)
    (rd : RD fork (deployedRuntime v) ee g s0 (resolverOneEntryPC rev)
      (target::src::⟨32⟩::value::R) mem aw rdata σ k C) :
    ∃ (evm' : EVM.State) (σ' : AccountMap) (success : Bool) (out : ByteArray),
      callViaEVM fork evm (AccountAddress.ofUInt256 target) (Int.ofNat value.toNat) (resolverOnePayload a rev) (success, evm', out) ∧
      SourceState s0 ee σ' evm' ∧ out.size < 2^138 ∧
      (if resolverCallValid ptr.toNat success out then
        ∃ aw' k' C', RD fork (deployedRuntime v) ee g s0 (resolverOneDonePC rev)
          (UInt256.ofNat (deployedRuntime v).size::calldataWord out 0::R)
          (resolverOneCallOutput mem src ptr dataPtr rev out) aw' out σ' k' C'
       else RDrev fork (deployedRuntime v) g s0) := by
  let head := resolverOneHeaderMemory mem ptr rev
  let dst := ptr+UInt256.ofNat 36
  have hb : ptr.toNat+420+32*((a.data.size+31)/32) < UInt256.size := by
    change ptr.toNat+420+32*((a.data.size+31)/32) < 2^256
    omega
  have hdst : dst.toNat = ptr.toNat+36 := uadd_word_ofNat_toNat ptr 36 (by omega)
  have hv : AttestationMemoryView head src dataPtr a := resolverOneHeaderMemory_view hview hs hd
  have hbound : dst.toNat+384+32*((a.data.size+31)/32) < UInt256.size := by rw [hdst]; omega
  have hdisj : dataPtr.toNat+32+32*((a.data.size+31)/32) ≤ dst.toNat := by rw [hdst]; omega
  have hret : (D_J (deployedRuntime v) 0).contains (resolverOnePreparePC rev) = true := by
    cases rev <;> rw [easPatchedValidJumps v] <;> unfold resolverOnePreparePC <;> jump_dest
  obtain ⟨aw1,k1,C1,rd1⟩ := resolverOneStart v rev (by omega) (by omega) hh rd
  obtain ⟨aw2,k2,C2,rd2⟩ := easEncodeAttestation v (by simp only [List.length_cons]; omega)
    hv.sourceLow hv.dataLow (by rw [hdst]; omega) hv.sourceCovered hdisj hv.dataCovered hv.pointer hv.length hbound hret rd1
  obtain ⟨gasArg,aw3,k3,C3,rd3⟩ := resolverOnePrepare v rev (by omega) rd2
  have hlen : (UInt256.sub (UInt256.ofNat (dst.toNat+352+32*((a.data.size+31)/32))) ptr).toNat =
      (resolverOnePayload a rev).size := by
    rw [usub_ofNat_word_toNat (by rw [hdst]; omega) (by omega), resolverOnePayload_size, a.encoding_size, hdst]
    omega
  have hinput : (resolverOneEncodedMemory mem src ptr dataPtr rev).readWithPadding ptr.toNat
      (UInt256.sub (UInt256.ofNat (dst.toNat+352+32*((a.data.size+31)/32))) ptr).toNat = resolverOnePayload a rev := by
    rw [hlen]
    exact resolverOneEncodedMemory_read hview hs hd hb
  have hsmall : (resolverOnePayload a rev).size ≤ Ethereum.EVM.maxReturnDataSizeByGas := by
    have hmax : 2^65 ≤ Ethereum.EVM.maxReturnDataSizeByGas := by decide +kernel
    apply le_trans (b := 2^65) _ hmax
    rw [resolverOnePayload_size, a.encoding_size]
    omega
  obtain ⟨evm',σ',success,out,k4,C4,hcall,hstate',rd4,hout⟩ :=
    callBridge (calldata := resolverOnePayload a rev) rd3 hstate hperm (resolverOneCall_decode v rev) hinput hsmall
      (by simp only [List.length_cons]; omega)
  have hpc : resolverOneCallPC rev + (⟨1⟩ : UInt256) = resolverOneAfterCallPC rev := by cases rev <;> rfl
  change RD fork (deployedRuntime v) ee g s0 (resolverOneCallPC rev + (⟨1⟩ : UInt256))
    ((if success then ⟨1⟩ else ⟨0⟩)::ptr::R)
    (callOutputMem (resolverOneEncodedMemory mem src ptr dataPtr rev) out ptr ⟨32⟩) _ out σ' k4 C4 at rd4
  rw [hpc] at rd4
  have hc : ptr.toNat+32 ≤ (resolverOneEncodedMemory mem src ptr dataPtr rev).size := by
    have hc := attestationEncodedMemory_covers head src dst dataPtr a.data.size hv.dataLow hdisj hv.dataCovered hv.length hbound
    change dst.toNat+352+32*((a.data.size+31)/32) ≤ (resolverOneEncodedMemory mem src ptr dataPtr rev).size at hc
    rw [hdst] at hc
    omega
  have hbout : out.size < UInt256.size := by change out.size < 2^256; omega
  refine ⟨evm',σ',success,out,hcall,hstate',hout,?_⟩
  exact resolverOneReturn v rev success (by omega) hbout (by have h := hview.sourceLow; omega)
    (by rw [callOutput32_size _ _ _ hbout hc]; exact hc) (by omega)
    (fun hl => callOutput32_load_word _ _ _ hbout hl hc) rd4

theorem resolverOneCallOutput_prefix {mem : ByteArray} {src ptr dataPtr : UInt256} {rev : Bool} {a : AttestationRecord}
    (hv : AttestationMemoryView mem src dataPtr a)
    (hs : src.toNat+320 ≤ ptr.toNat) (hd : dataPtr.toNat+32+32*((a.data.size+31)/32) ≤ ptr.toNat)
    (hb : ptr.toNat+420+32*((a.data.size+31)/32) < UInt256.size) (out : ByteArray) (hout : out.size < UInt256.size) :
    MemoryPrefix mem (resolverOneCallOutput mem src ptr dataPtr rev out) ptr.toNat := by
  let head := resolverOneHeaderMemory mem ptr rev
  let dst := ptr+UInt256.ofNat 36
  have hdst : dst.toNat = ptr.toNat+36 := uadd_word_ofNat_toNat ptr 36 (by omega)
  have hv' : AttestationMemoryView head src dataPtr a := resolverOneHeaderMemory_view hv hs hd
  have hbound : dst.toNat+384+32*((a.data.size+31)/32) < UInt256.size := by rw [hdst]; omega
  have hdisj : dataPtr.toNat+32+32*((a.data.size+31)/32) ≤ dst.toNat := by rw [hdst]; omega
  have hh : MemoryPrefix mem head ptr.toNat := selectorArgumentMemory_prefix mem ptr.toNat _ _
  have he := attestationEncodedMemory_prefix head src dst dataPtr a.data.size hv'.dataLow hdisj hv'.dataCovered hv'.length hbound
  have hc : ptr.toNat+32 ≤ (resolverOneEncodedMemory mem src ptr dataPtr rev).size := by
    have h := attestationEncodedMemory_covers head src dst dataPtr a.data.size hv'.dataLow hdisj hv'.dataCovered hv'.length hbound
    change dst.toNat+352+32*((a.data.size+31)/32) ≤ (resolverOneEncodedMemory mem src ptr dataPtr rev).size at h
    rw [hdst] at h
    omega
  exact (hh.trans (he.mono (by rw [hdst]; omega))).trans
    ((callOutput32_prefix _ out ptr hout hc).trans (memoryPrefix_sparse_writeWord _ 64 ptr.toNat _ (Or.inr (by decide))))

theorem resolverOneCallOutput_heap (mem : ByteArray) (src ptr dataPtr : UInt256) (rev : Bool) (out : ByteArray) :
    memLoad (UInt256.ofNat 64) (resolverOneCallOutput mem src ptr dataPtr rev out) =
      UInt256.ofNat (allocateNext ptr.toNat (min out.size 32)) := by
  exact resolverReturnMemory_heap _ _ _

end Benchmarks.EAS.EAS
