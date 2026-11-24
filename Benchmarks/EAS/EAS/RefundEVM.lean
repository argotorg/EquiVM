import Benchmarks.EAS.EAS.RefundSource
import Benchmarks.EAS.EAS.RefundReturn
import Benchmarks.EAS.EAS.RuntimeBlocks_052

variable {fork : Ethereum.Fork}
open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables Benchmarks.EAS.EAS.Immutables
namespace Benchmarks.EAS.EAS
set_option maxRecDepth 10000

theorem refundBalance_source {s0 : EVM.State} {ee : ExecutionEnv} {σ : AccountMap} {evm : EVM.State}
    (hs : SourceState s0 ee σ evm) : refundBalance evm = (σ.get? ee.codeOwner |>.elim ⟨0⟩ (·.balance)) := by
  simp only [refundBalance, State.lookupAccount, hs.env, ← hs.accounts]
  cases σ.get? ee.codeOwner <;> rfl

theorem refundEVM_zero {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap}
    {k C : Nat} {ret : UInt256} {R : List UInt256} (v : EASImmutables)
    (hstack : R.length+4 ≤ 1024) (hvalid : (D_J (deployedRuntime v) 0).contains ret = true)
    (rd : RD fork (deployedRuntime v) ee g s0 ⟨16342⟩ (⟨0⟩::ret::R) mem aw rdata σ k C) :
    ∃ aw' k' C', RD fork (deployedRuntime v) ee g s0 ret R mem aw' rdata σ k' C' := by
  obtain ⟨aw1,k1,C1,rd1⟩ := easBlocks.eas_block_16342_fallthrough_packed (immWords := wordsOf (immStore v))
    (by simp only [List.length_cons]; omega) rfl rd
  exact easBlocks.eas_block_16348_packed (immWords := wordsOf (immStore v)) (by omega) hvalid rd1

theorem refundBalanceEntry {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap}
    {k C : Nat} {value ret : UInt256} {R : List UInt256} (v : EASImmutables)
    (hstack : R.length+4 ≤ 1024) (hn : value ≠ ⟨0⟩)
    (rd : RD fork (deployedRuntime v) ee g s0 ⟨16342⟩ (value::ret::R) mem aw rdata σ k C) :
    ∃ aw' k' C', RD fork (deployedRuntime v) ee g s0 ⟨16353⟩
      ((σ.get? ee.codeOwner |>.elim ⟨0⟩ (·.balance))::value::value::ret::R) mem aw' rdata σ k' C' := by
  obtain ⟨aw1,k1,C1,rd1⟩ := easBlocks.eas_block_16342_taken_packed (immWords := wordsOf (immStore v))
    (by simp only [List.length_cons]; omega) hn (by rw [easPatchedValidJumpsRuntime v]; jump_dest) rd
  obtain ⟨aw2,k2,C2,rd2⟩ := easBlocks.eas_block_16350_packed (immWords := wordsOf (immStore v))
    (by simp only [List.length_cons]; omega) rd1
  have rd3 := RD.selfbalance rd2
    (by immutable_decode(immutableLayout, easBytecode, wordsOf (immStore v), (⟨16352⟩ : UInt256), UInt8.ofNat 71,
      .SELFBALANCE, none, easBlocks.immutableLayout_inBounds, easBlocks.immutableTemplate_size64))
    (by simp only [easBlocks.eas_block_16350_stack, List.length_cons]; omega)
  exact ⟨aw2,_,_,rd3⟩

theorem refundEVM_insufficient {ee : ExecutionEnv} {g : Sat256} {s0 evm : EVM.State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap}
    {k C : Nat} {value ret : UInt256} {R : List UInt256} (v : EASImmutables)
    (hstack : R.length+7 ≤ 1024) (hstate : SourceState s0 ee σ evm) (hn : value ≠ ⟨0⟩)
    (hb : ¬ value.toNat ≤ (refundBalance evm).toNat)
    (rd : RD fork (deployedRuntime v) ee g s0 ⟨16342⟩ (value::ret::R) mem aw rdata σ k C) :
    RDrev fork (deployedRuntime v) g s0 := by
  obtain ⟨aw1,k1,C1,rd1⟩ := refundBalanceEntry v (by omega) hn rd
  rw [refundBalance_source hstate] at hb
  obtain ⟨aw2,k2,C2,rd2⟩ := easBlocks.eas_block_16353_taken_packed (immWords := wordsOf (immStore v))
    (by simp only [List.length_cons]; omega) (by rw [ult_one (by omega)]; decide)
    (by rw [easPatchedValidJumpsRuntime v]; jump_dest) rd1
  exact easBlocks.eas_block_16551 (immWords := wordsOf (immStore v))
    (by simp only [easBlocks.eas_block_16353_taken_stack, List.length_cons]; omega) rd2

theorem refundCallEntry {ee : ExecutionEnv} {g : Sat256} {s0 evm : EVM.State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap}
    {k C : Nat} {value ret : UInt256} {R : List UInt256} (v : EASImmutables)
    (hstack : R.length+12 ≤ 1024) (hstate : SourceState s0 ee σ evm)
    (hn : value ≠ ⟨0⟩) (hb : value.toNat ≤ (refundBalance evm).toNat)
    (rd : RD fork (deployedRuntime v) ee g s0 ⟨16342⟩ (value::ret::R) mem aw rdata σ k C) :
    ∃ gasArg aw' k' C', RD fork (deployedRuntime v) ee g s0 ⟨16366⟩
      (gasArg::UInt256.ofNat ee.source.val::value::⟨0⟩::⟨0⟩::⟨0⟩::⟨0⟩::ret::R) mem aw' rdata σ k' C' := by
  obtain ⟨aw1,k1,C1,rd1⟩ := refundBalanceEntry v (by omega) hn rd
  have hbal : value.toNat ≤ (σ.get? ee.codeOwner |>.elim ⟨0⟩ (·.balance)).toNat := by
    simpa only [refundBalance_source hstate] using hb
  obtain ⟨aw2,k2,C2,rd2⟩ := easBlocks.eas_block_16353_fallthrough_packed (immWords := wordsOf (immStore v))
    (by simp only [List.length_cons]; omega) (ult_zero hbal) rd1
  obtain ⟨aw3,k3,C3,rd3⟩ := easBlocks.eas_block_16358_packed (immWords := wordsOf (immStore v))
    (by simp only [easBlocks.eas_block_16353_fallthrough_stack, List.length_cons]; omega) rd2
  exact ⟨_,aw3,k3,C3,rd3⟩

theorem refundEVM {ee : ExecutionEnv} {g : Sat256} {s0 evm : EVM.State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap}
    {k C : Nat} {value ptr ret : UInt256} {R : List UInt256} (v : EASImmutables)
    (hstack : R.length+12 ≤ 1024) (hperm : ee.perm = true) (hstate : SourceState s0 ee σ evm)
    (hn : value ≠ ⟨0⟩) (hb : value.toNat ≤ (refundBalance evm).toNat)
    (hheap : ptr.toNat ≤ 2^64-1) (hh : memLoad (UInt256.ofNat 64) mem = ptr)
    (hvalid : (D_J (deployedRuntime v) 0).contains ret = true)
    (rd : RD fork (deployedRuntime v) ee g s0 ⟨16342⟩ (value::ret::R) mem aw rdata σ k C) :
    ∃ (evm' : EVM.State) (σ' : AccountMap) (success : Bool) (out : ByteArray),
      callViaEVM fork evm evm.executionEnv.source (Int.ofNat value.toNat) ByteArray.empty (success,evm',out) ∧
      SourceState s0 ee σ' evm' ∧ out.size < 2^138 ∧
      (if refundResultValid ptr.toNat success out then
        ∃ aw' k' C', RD fork (deployedRuntime v) ee g s0 ret R (refundMemory mem ptr out) aw' out σ' k' C'
       else RDrev fork (deployedRuntime v) g s0) := by
  obtain ⟨gasArg,aw3,k3,C3,rd3⟩ := refundCallEntry v hstack hstate hn hb rd
  obtain ⟨evm',σ',success,out,k4,C4,hcall,hstate',rd4,hout⟩ := callBridge (calldata := ByteArray.empty)
    rd3 hstate hperm
    (by immutable_decode(immutableLayout, easBytecode, wordsOf (immStore v), (⟨16366⟩ : UInt256), UInt8.ofNat 241,
      .CALL, none, easBlocks.immutableLayout_inBounds, easBlocks.immutableTemplate_size64))
    (byteArray_readWithPadding_zero _ _) (by decide) (by simp only [List.length_cons]; omega)
  simp only [accountAddress_roundtrip, ← hstate.env] at hcall
  change RD fork (deployedRuntime v) ee g s0 ⟨16367⟩ ((if success then ⟨1⟩ else ⟨0⟩)::ret::R)
    (callOutputMem mem out ⟨0⟩ ⟨0⟩) _ out σ' k4 C4 at rd4
  rw [callOutputMem_zero] at rd4
  exact ⟨evm',σ',success,out,hcall,hstate',hout,
    refundReturnEVM v success hstack (by change out.size < 2^256; omega) hheap hh hvalid rd4⟩

end Benchmarks.EAS.EAS
