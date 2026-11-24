import Benchmarks.EAS.EAS.PayableCheck
import Benchmarks.EAS.EAS.ResolverOneEVM
import Benchmarks.EAS.EAS.RefundEVM

variable {fork : Ethereum.Fork}
open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables Benchmarks.EAS.EAS.Immutables
namespace Benchmarks.EAS.EAS
set_option maxRecDepth 10000

theorem resolveOneStart {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : Nat}
    {schemaPtr src rev target last available value : UInt256} {R : List UInt256} (v : EASImmutables)
    (hstack : R.length+8 ≤ 1024)
    (ht : UInt256.land (memLoad (schemaPtr+UInt256.ofNat 32) mem) (UInt256.ofNat 1461501637330902918203684832716283019655932542975) = target)
    (rd : RD fork (deployedRuntime v) ee g s0 ⟨15724⟩ (schemaPtr::src::value::rev::available::last::R) mem aw rdata σ k C) :
    ∃ aw' k' C', RD fork (deployedRuntime v) ee g s0 (if target = ⟨0⟩ then ⟨16328⟩ else ⟨15764⟩)
      (src::rev::target::last::available::value::R) mem aw' rdata σ k' C' := by
  by_cases hz : target = ⟨0⟩
  · rw [if_pos hz]
    obtain ⟨aw1,k1,C1,rd1⟩ := easBlocks.eas_block_15724_taken_packed (immWords := wordsOf (immStore v)) hstack
      (by change UInt256.isZero (UInt256.land _ (UInt256.ofNat 1461501637330902918203684832716283019655932542975)) ≠ ⟨0⟩; rw [ht,hz]; decide)
      (by rw [easPatchedValidJumpsRuntime v]; jump_dest) rd
    refine ⟨aw1,k1,C1,?_⟩
    simpa only [easBlocks.eas_block_15724_taken_stack, ht] using rd1
  · rw [if_neg hz]
    obtain ⟨aw1,k1,C1,rd1⟩ := easBlocks.eas_block_15724_fallthrough_packed (immWords := wordsOf (immStore v)) hstack
      (by change UInt256.isZero (UInt256.land _ (UInt256.ofNat 1461501637330902918203684832716283019655932542975)) = ⟨0⟩; rw [ht]; exact isZero_eq_zero_of_ne hz) rd
    refine ⟨aw1,k1,C1,?_⟩
    simpa only [easBlocks.eas_block_15724_fallthrough_stack, ht] using rd1

theorem resolveOneZero {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : Nat}
    {src rev target last available value ret : UInt256} {R : List UInt256} (v : EASImmutables)
    (hstack : R.length+7 ≤ 1024) (hret : (D_J (deployedRuntime v) 0).contains ret = true)
    (rd : RD fork (deployedRuntime v) ee g s0 ⟨16328⟩ (src::rev::target::last::available::value::ret::R) mem aw rdata σ k C) :
    if value = ⟨0⟩ then ∃ aw' k' C', RD fork (deployedRuntime v) ee g s0 ret (⟨0⟩::R) mem aw' rdata σ k' C'
    else RDrev fork (deployedRuntime v) g s0 := by
  by_cases hz : value = ⟨0⟩
  · rw [if_pos hz]
    obtain ⟨aw1,k1,C1,rd1⟩ := easBlocks.eas_block_16328_fallthrough_packed (immWords := wordsOf (immStore v))
      (by simp only [List.length_cons]; omega) hz rd
    exact easBlocks.eas_block_16338_packed (immWords := wordsOf (immStore v)) (by omega) hret rd1
  · rw [if_neg hz]
    obtain ⟨aw1,k1,C1,rd1⟩ := easBlocks.eas_block_16328_taken_packed (immWords := wordsOf (immStore v))
      (by simp only [List.length_cons]; omega) hz (by rw [easPatchedValidJumpsRuntime v]; jump_dest) rd
    exact easBlocks.eas_block_15407 (immWords := wordsOf (immStore v))
      (by simp only [easBlocks.eas_block_16328_taken_stack, List.length_cons]; omega) rd1

theorem resolveOneNoPayment {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : Nat}
    {src rev target last available : UInt256} {R : List UInt256} (v : EASImmutables)
    (hstack : R.length+9 ≤ 1024)
    (rd : RD fork (deployedRuntime v) ee g s0 ⟨15764⟩ (src::rev::target::last::available::⟨0⟩::R) mem aw rdata σ k C) :
    ∃ aw' k' C', RD fork (deployedRuntime v) ee g s0 ⟨15777⟩ (src::rev::target::last::available::⟨0⟩::R) mem aw' rdata σ k' C' := by
  obtain ⟨aw1,k1,C1,rd1⟩ := easBlocks.eas_block_15764_fallthrough_packed (immWords := wordsOf (immStore v)) hstack (by decide) rd
  exact easBlocks.eas_block_15772_fallthrough_packed (immWords := wordsOf (immStore v))
    (by simp only [List.length_cons]; omega) (by decide) rd1

theorem resolveOnePaymentEntry {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : Nat}
    {src rev target last available value : UInt256} {R : List UInt256} (v : EASImmutables)
    (hstack : R.length+9 ≤ 1024) (hn : value ≠ ⟨0⟩)
    (rd : RD fork (deployedRuntime v) ee g s0 ⟨15764⟩ (src::rev::target::last::available::value::R) mem aw rdata σ k C) :
    ∃ aw' k' C', RD fork (deployedRuntime v) ee g s0 (payableEntryPC .single)
      (⟨1⟩::src::rev::target::last::available::value::R) mem aw' rdata σ k' C' := by
  have hz : UInt256.isZero (UInt256.isZero value) = ⟨1⟩ := by rw [isZero_eq_zero_of_ne hn]; rfl
  obtain ⟨aw1,k1,C1,rd1⟩ := easBlocks.eas_block_15764_taken_packed (immWords := wordsOf (immStore v)) hstack
    (by rw [hz]; decide) (by rw [easPatchedValidJumpsRuntime v]; jump_dest) rd
  exact ⟨aw1,k1,C1,by simpa only [easBlocks.eas_block_15764_taken_stack, hz] using rd1⟩

theorem resolveOneAmount {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : Nat}
    {src rev target last available value : UInt256} {R : List UInt256} (v : EASImmutables)
    (hstack : R.length+8 ≤ 1024)
    (rd : RD fork (deployedRuntime v) ee g s0 ⟨15777⟩ (src::rev::target::last::available::value::R) mem aw rdata σ k C) :
    if value.toNat ≤ available.toNat then
      ∃ aw' k' C', RD fork (deployedRuntime v) ee g s0 ⟨15784⟩ (src::rev::target::last::available::value::R) mem aw' rdata σ k' C'
    else RDrev fork (deployedRuntime v) g s0 := by
  by_cases hb : value.toNat ≤ available.toNat
  · rw [if_pos hb]
    exact easBlocks.eas_block_15777_fallthrough_packed (immWords := wordsOf (immStore v)) hstack (ugt_zero hb) rd
  · rw [if_neg hb]
    obtain ⟨aw1,k1,C1,rd1⟩ := easBlocks.eas_block_15777_taken_packed (immWords := wordsOf (immStore v)) hstack
      (by rw [ugt_one (by omega : available.toNat < value.toNat)]; decide)
      (by rw [easPatchedValidJumpsRuntime v]; jump_dest) rd
    exact easBlocks.eas_block_15365 (immWords := wordsOf (immStore v))
      (by simp only [List.length_cons]; omega) rd1

theorem resolveOneChoose {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : Nat}
    {src target last available value : UInt256} {R : List UInt256} (v : EASImmutables) (rev : Bool)
    (hstack : R.length+9 ≤ 1024)
    (rd : RD fork (deployedRuntime v) ee g s0 ⟨15784⟩ (src::rev.toUInt256::target::last::available::value::R) mem aw rdata σ k C) :
    ∃ aw' k' C', RD fork (deployedRuntime v) ee g s0 (resolverOneEntryPC rev)
      (target::src::⟨32⟩::value::last::available::value::R) mem aw' rdata σ k' C' := by
  cases rev with
  | false =>
    exact easBlocks.eas_block_15784_taken_packed (immWords := wordsOf (immStore v)) hstack (by decide)
      (by rw [easPatchedValidJumpsRuntime v]; jump_dest) rd
  | true => exact easBlocks.eas_block_15784_fallthrough_packed (immWords := wordsOf (immStore v)) hstack (by decide) rd

theorem resolveOneAccepted {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : Nat}
    {junk word last available value : UInt256} {R : List UInt256} (v : EASImmutables) (rev : Bool)
    (hstack : R.length+5 ≤ 1024)
    (rd : RD fork (deployedRuntime v) ee g s0 (resolverOneDonePC rev)
      (junk::word::last::available::value::R) mem aw rdata σ k C) :
    if word ≠ ⟨0⟩ then
      ∃ aw' k' C', RD fork (deployedRuntime v) ee g s0 ⟨15885⟩ (last::value::available::value::R) mem aw' rdata σ k' C'
    else RDrev fork (deployedRuntime v) g s0 := by
  by_cases hn : word ≠ ⟨0⟩
  · rw [if_pos hn]
    cases rev with
    | false =>
      obtain ⟨aw1,k1,C1,rd1⟩ := easBlocks.eas_block_16087_fallthrough_packed (immWords := wordsOf (immStore v))
        (by simp only [List.length_cons]; omega) (isZero_eq_zero_of_ne hn) rd
      exact easBlocks.eas_block_16094_packed (immWords := wordsOf (immStore v)) hstack
        (by rw [easPatchedValidJumpsRuntime v]; jump_dest) rd1
    | true =>
      obtain ⟨aw1,k1,C1,rd1⟩ := easBlocks.eas_block_15876_fallthrough_packed (immWords := wordsOf (immStore v))
        (by simp only [List.length_cons]; omega) (isZero_eq_zero_of_ne hn) rd
      exact easBlocks.eas_block_15883_packed (immWords := wordsOf (immStore v)) (by omega) rd1
  · rw [if_neg hn]
    have hz : UInt256.isZero word ≠ ⟨0⟩ := by rw [not_ne_iff.mp hn]; decide
    cases rev with
    | false =>
      obtain ⟨aw1,k1,C1,rd1⟩ := easBlocks.eas_block_16087_taken_packed (immWords := wordsOf (immStore v))
        (by simp only [List.length_cons]; omega) hz (by rw [easPatchedValidJumpsRuntime v]; jump_dest) rd
      exact easBlocks.eas_block_16100 (immWords := wordsOf (immStore v))
        (by simp only [easBlocks.eas_block_16087_taken_stack, List.length_cons]; omega) rd1
    | true =>
      obtain ⟨aw1,k1,C1,rd1⟩ := easBlocks.eas_block_15876_taken_packed (immWords := wordsOf (immStore v))
        (by simp only [List.length_cons]; omega) hz (by rw [easPatchedValidJumpsRuntime v]; jump_dest) rd
      exact easBlocks.eas_block_15904 (immWords := wordsOf (immStore v))
        (by simp only [easBlocks.eas_block_15876_taken_stack, List.length_cons]; omega) rd1

theorem resolveOneFinish {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : Nat}
    {available value ret : UInt256} {R : List UInt256} (v : EASImmutables) (last : Bool)
    (hstack : R.length+6 ≤ 1024) (hret : (D_J (deployedRuntime v) 0).contains ret = true)
    (rd : RD fork (deployedRuntime v) ee g s0 ⟨15885⟩ (last.toUInt256::value::available::value::ret::R) mem aw rdata σ k C) :
    if last then
      ∃ aw' k' C', RD fork (deployedRuntime v) ee g s0 ⟨16342⟩
        (UInt256.sub available value::⟨4692⟩::value::ret::R) mem aw' rdata σ k' C'
    else ∃ aw' k' C', RD fork (deployedRuntime v) ee g s0 ret (value::R) mem aw' rdata σ k' C' := by
  cases last with
  | false =>
    obtain ⟨aw1,k1,C1,rd1⟩ := easBlocks.eas_block_15885_fallthrough_packed (immWords := wordsOf (immStore v))
      (by simp only [List.length_cons]; omega) (by rfl) rd
    exact easBlocks.eas_block_15890_packed (immWords := wordsOf (immStore v)) (by omega) hret rd1
  | true =>
    obtain ⟨aw1,k1,C1,rd1⟩ := easBlocks.eas_block_15885_taken_packed (immWords := wordsOf (immStore v))
      (by simp only [List.length_cons]; omega) (by decide) (by rw [easPatchedValidJumpsRuntime v]; jump_dest) rd
    exact easBlocks.eas_block_15894_packed (immWords := wordsOf (immStore v))
      (by simp only [List.length_cons]; omega) (by rw [easPatchedValidJumpsRuntime v]; jump_dest) rd1

end Benchmarks.EAS.EAS
