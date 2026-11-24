import Benchmarks.EAS.EAS.PayableSites

variable {fork : Ethereum.Fork}
open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables Benchmarks.EAS.EAS.Immutables
namespace Benchmarks.EAS.EAS
set_option maxRecDepth 10000

theorem payableReturn {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem : ByteArray} {aw : UInt256} {out : ByteArray} {σ : AccountMap} {k C : Nat}
    {ptr a b c d e target : UInt256} {R : List UInt256} (v : EASImmutables) (site : PayableSite) (success : Bool)
    (hstack : R.length+16 ≤ 1024) (hb : out.size < UInt256.size)
    (hlo : 96 ≤ ptr.toNat) (hin : ptr.toNat+32 ≤ mem.size) (hbound : ptr.toNat+32 < UInt256.size)
    (hword : 32 ≤ out.size → memLoad ptr mem = calldataWord out 0)
    (rd : RD fork (deployedRuntime v) ee g s0 (payableAfterCallPC site)
      ((if success then ⟨1⟩ else ⟨0⟩)::ptr::payableSavedTail site a b c d e target R) mem aw out σ k C) :
    if resolverCallValid ptr.toNat success out then
      ∃ aw' k' C', RD fork (deployedRuntime v) ee g s0 (payableDonePC site)
        (UInt256.ofNat (deployedRuntime v).size::calldataWord out 0::payableSavedTail site a b c d e target R)
        (resolverReturnMemory mem ptr out) aw' out σ k' C'
    else RDrev fork (deployedRuntime v) g s0 := by
  cases success with
  | false =>
    rw [if_neg (show ¬ resolverCallValid ptr.toNat false out from fun h => Bool.noConfusion h.1)]
    exact payableReturn_failure v site (by omega) hb rd
  | true =>
    obtain ⟨aw1,k1,C1,rd1⟩ := payableReturn_success v site (by omega) rd
    exact payableCopyReturn v site
      (by have h := payableSavedTail_length site a b c d e target R; omega) hb
      (by intro he; subst site; simp only [payableSavedTail, List.length_cons]; omega)
      hlo hin hbound hword rd1

def payableOutputMemory (mem : ByteArray) (ptr : UInt256) (out : ByteArray) : ByteArray :=
  resolverReturnMemory (callOutputMem (payableHeaderMemory mem ptr) out ptr ⟨32⟩) ptr out

theorem payableOutputMemory_prefix (mem : ByteArray) (ptr : UInt256) (out : ByteArray)
    (hout : out.size < UInt256.size) : MemoryPrefix mem (payableOutputMemory mem ptr out) ptr.toNat := by
  have hh : MemoryPrefix mem (payableHeaderMemory mem ptr) ptr.toNat :=
    memoryPrefix_sparse_writeWord mem ptr.toNat ptr.toNat _ (Or.inl (le_refl _))
  exact hh.trans ((callOutput32_prefix _ out ptr hout (payableHeaderMemory_covers mem ptr)).trans
    (memoryPrefix_sparse_writeWord _ 64 ptr.toNat _ (Or.inr (by decide))))

theorem payableOutputMemory_heap (mem : ByteArray) (ptr : UInt256) (out : ByteArray) :
    memLoad (UInt256.ofNat 64) (payableOutputMemory mem ptr out) =
      UInt256.ofNat (allocateNext ptr.toNat (min out.size 32)) := by
  exact resolverReturnMemory_heap _ _ _

theorem payableEVM {ee : ExecutionEnv} {g : Sat256} {s0 evm : EVM.State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : Nat}
    {ptr junk a b c d e target : UInt256} {R : List UInt256} (v : EASImmutables) (site : PayableSite)
    (hstack : R.length+16 ≤ 1024) (hs : SourceState s0 ee σ evm)
    (hheap : ptr.toNat ≤ 2^64-1) (hlo : 96 ≤ ptr.toNat) (hh : memLoad (UInt256.ofNat 64) mem = ptr)
    (rd : RD fork (deployedRuntime v) ee g s0 (payableEntryPC site)
      (junk::payableSavedTail site a b c d e target R) mem aw rdata σ k C) :
    ∃ (evm' : EVM.State) (σ' : AccountMap) (success : Bool) (out : ByteArray),
      callViaEVM fork evm (AccountAddress.ofUInt256 target) 0 payablePayload (success,evm',out) false ∧
      SourceState s0 ee σ' evm' ∧ out.size < 2^138 ∧
      (if resolverCallValid ptr.toNat success out then
        ∃ aw' k' C', RD fork (deployedRuntime v) ee g s0 (payableDonePC site)
          (UInt256.ofNat (deployedRuntime v).size::calldataWord out 0::payableSavedTail site a b c d e target R)
          (payableOutputMemory mem ptr out) aw' out σ' k' C'
       else RDrev fork (deployedRuntime v) g s0) := by
  obtain ⟨gasArg,aw1,k1,C1,rd1⟩ := payableStart v site (by omega) hh rd
  obtain ⟨evm',σ',success,out,k2,C2,hcall,hs',rd2,hout⟩ :=
    staticcallBridge (calldata := payablePayload) rd1 hs (payableCall_decode v site)
      (payableHeaderMemory_read mem ptr) (by rw [payablePayload_size]; decide +kernel)
      (by simp only [List.length_cons]; have h := payableSavedTail_length site a b c d e target R; omega)
  have hpc : payableCallPC site + (⟨1⟩ : UInt256) = payableAfterCallPC site := by cases site <;> rfl
  rw [hpc] at rd2
  have hbout : out.size < UInt256.size := by change out.size < 2^256; omega
  have hc := payableHeaderMemory_covers mem ptr
  refine ⟨evm',σ',success,out,hcall,hs',hout,?_⟩
  exact payableReturn v site success hstack hbout hlo
    (by rw [callOutput32_size _ _ _ hbout hc]; exact hc)
    (by change ptr.toNat+32 < 2^256; omega)
    (fun hl => callOutput32_load_word _ _ _ hbout hl hc) rd2

end Benchmarks.EAS.EAS
