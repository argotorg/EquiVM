import Benchmarks.EAS.EAS.PayableDecode
import Benchmarks.EAS.EAS.PayableSource

variable {fork : Ethereum.Fork}
open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables Benchmarks.EAS.EAS.Immutables
namespace Benchmarks.EAS.EAS
set_option maxRecDepth 10000

def payableEntryPC : PayableSite → UInt256
  | .single => ⟨16200⟩ | .multiAttest => ⟨14835⟩ | .multiRevoke => ⟨15449⟩
def payableCallPC : PayableSite → UInt256
  | .single => ⟨16248⟩ | .multiAttest => ⟨14883⟩ | .multiRevoke => ⟨15497⟩
def payableAfterCallPC : PayableSite → UInt256
  | .single => ⟨16249⟩ | .multiAttest => ⟨14884⟩ | .multiRevoke => ⟨15498⟩

def payableSavedTail (site : PayableSite) (a b c d e target : UInt256) (R : List UInt256) : List UInt256 :=
  match site with
  | .single => a::b::target::R
  | .multiAttest => a::b::c::⟨0⟩::e::target::R
  | .multiRevoke => a::b::c::d::target::R

theorem payableSavedTail_length (site : PayableSite) (a b c d e target : UInt256) (R : List UInt256) :
    (payableSavedTail site a b c d e target R).length ≤ R.length+6 := by
  cases site <;> simp only [payableSavedTail, List.length_cons] <;> omega

def payableSelectorWord : UInt256 := ⟨0xce46e04600000000000000000000000000000000000000000000000000000000⟩
def payableHeaderMemory (mem : ByteArray) (ptr : UInt256) : ByteArray := writeWord mem ptr.toNat payableSelectorWord

theorem payableHeaderMemory_read (mem : ByteArray) (ptr : UInt256) :
    (payableHeaderMemory mem ptr).readWithPadding ptr.toNat 4 = payablePayload := by
  have hs : payableSelectorWord.toByteArray.extract 0 4 = payablePayload := by decide +kernel
  simpa only [payableHeaderMemory, Nat.add_zero, Nat.zero_add, hs] using
    writeWord_sparse_read_window mem ptr.toNat 0 4 payableSelectorWord (by decide) (by decide) (by decide)

theorem payableHeaderMemory_covers (mem : ByteArray) (ptr : UInt256) :
    ptr.toNat+32 ≤ (payableHeaderMemory mem ptr).size := by
  rw [payableHeaderMemory, writeWord_sparse_size]
  exact Nat.le_max_right _ _

theorem payableStart {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : Nat}
    {ptr junk a b c d e target : UInt256} {R : List UInt256} (v : EASImmutables) (site : PayableSite)
    (hstack : R.length+13 ≤ 1024) (hh : memLoad (UInt256.ofNat 64) mem = ptr)
    (rd : RD fork (deployedRuntime v) ee g s0 (payableEntryPC site)
      (junk::payableSavedTail site a b c d e target R) mem aw rdata σ k C) :
    ∃ gasArg aw' k' C', RD fork (deployedRuntime v) ee g s0 (payableCallPC site)
      (gasArg::target::ptr::⟨4⟩::ptr::⟨32⟩::ptr::payableSavedTail site a b c d e target R)
      (payableHeaderMemory mem ptr) aw' rdata σ k' C' := by
  cases site with
  | single =>
    obtain ⟨aw1,k1,C1,rd1⟩ := easBlocks.eas_block_16200_packed (immWords := wordsOf (immStore v)) (by omega) rd
    simp only [easBlocks.eas_block_16200_stack, easBlocks.eas_block_16200_memory, hh] at rd1
    exact ⟨_,aw1,k1,C1,rd1⟩
  | multiAttest =>
    obtain ⟨aw1,k1,C1,rd1⟩ := easBlocks.eas_block_14835_packed (immWords := wordsOf (immStore v)) hstack rd
    simp only [easBlocks.eas_block_14835_stack, easBlocks.eas_block_14835_memory, hh] at rd1
    exact ⟨_,aw1,k1,C1,rd1⟩
  | multiRevoke =>
    obtain ⟨aw1,k1,C1,rd1⟩ := easBlocks.eas_block_15449_packed (immWords := wordsOf (immStore v)) (by omega) rd
    simp only [easBlocks.eas_block_15449_stack, easBlocks.eas_block_15449_memory, hh] at rd1
    exact ⟨_,aw1,k1,C1,rd1⟩

theorem payableCall_decode (v : EASImmutables) (site : PayableSite) :
    decode (deployedRuntime v) (payableCallPC site) = some (.STATICCALL, none) := by
  cases site with
  | single =>
    change decode (immutableLayout.runtime easBytecode (wordsOf (immStore v))) (UInt256.ofNat 16248) = _
    immutable_decode(immutableLayout, easBytecode, wordsOf (immStore v), (⟨16248⟩ : UInt256), UInt8.ofNat 250,
      .STATICCALL, none, easBlocks.immutableLayout_inBounds, easBlocks.immutableTemplate_size64)
  | multiAttest =>
    change decode (immutableLayout.runtime easBytecode (wordsOf (immStore v))) (UInt256.ofNat 14883) = _
    immutable_decode(immutableLayout, easBytecode, wordsOf (immStore v), (⟨14883⟩ : UInt256), UInt8.ofNat 250,
      .STATICCALL, none, easBlocks.immutableLayout_inBounds, easBlocks.immutableTemplate_size64)
  | multiRevoke =>
    change decode (immutableLayout.runtime easBytecode (wordsOf (immStore v))) (UInt256.ofNat 15497) = _
    immutable_decode(immutableLayout, easBytecode, wordsOf (immStore v), (⟨15497⟩ : UInt256), UInt8.ofNat 250,
      .STATICCALL, none, easBlocks.immutableLayout_inBounds, easBlocks.immutableTemplate_size64)

theorem payableReturn_success {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem : ByteArray} {aw : UInt256} {out : ByteArray} {σ : AccountMap} {k C : Nat}
    {ptr a b c d e target : UInt256} {R : List UInt256} (v : EASImmutables) (site : PayableSite)
    (hstack : R.length+10 ≤ 1024)
    (rd : RD fork (deployedRuntime v) ee g s0 (payableAfterCallPC site)
      (⟨1⟩::ptr::payableSavedTail site a b c d e target R) mem aw out σ k C) :
    ∃ aw' k' C', RD fork (deployedRuntime v) ee g s0 (payableCopyPC site)
      (ptr::⟨0⟩::payableSavedTail site a b c d e target R) mem aw' out σ k' C' := by
  cases site with
  | single =>
    obtain ⟨aw1,k1,C1,rd1⟩ := easBlocks.eas_block_16249_fallthrough_packed (immWords := wordsOf (immStore v))
      (by simp only [payableSavedTail, List.length_cons]; omega) (by decide) rd
    exact easBlocks.eas_block_16256_taken_packed (immWords := wordsOf (immStore v))
      (by simp only [payableSavedTail, List.length_cons]; omega) (by decide)
      (by rw [easPatchedValidJumpsRuntime v]; jump_dest) rd1
  | multiAttest =>
    obtain ⟨aw1,k1,C1,rd1⟩ := easBlocks.eas_block_14884_fallthrough_packed (immWords := wordsOf (immStore v))
      (by simp only [payableSavedTail, List.length_cons]; omega) (by decide) rd
    exact easBlocks.eas_block_14891_taken_packed (immWords := wordsOf (immStore v))
      (by simp only [List.length_cons]; omega) (by decide)
      (by rw [easPatchedValidJumpsRuntime v]; jump_dest) rd1
  | multiRevoke =>
    obtain ⟨aw1,k1,C1,rd1⟩ := easBlocks.eas_block_15498_fallthrough_packed (immWords := wordsOf (immStore v))
      (by simp only [payableSavedTail, List.length_cons]; omega) (by decide) rd
    exact easBlocks.eas_block_15505_taken_packed (immWords := wordsOf (immStore v))
      (by simp only [payableSavedTail, List.length_cons]; omega) (by decide)
      (by rw [easPatchedValidJumpsRuntime v]; jump_dest) rd1

theorem payableReturn_failure {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem : ByteArray} {aw : UInt256} {out : ByteArray} {σ : AccountMap} {k C : Nat}
    {ptr a b c d e target : UInt256} {R : List UInt256} (v : EASImmutables) (site : PayableSite)
    (hstack : R.length+12 ≤ 1024) (hb : out.size < UInt256.size)
    (rd : RD fork (deployedRuntime v) ee g s0 (payableAfterCallPC site)
      (⟨0⟩::ptr::payableSavedTail site a b c d e target R) mem aw out σ k C) :
    RDrev fork (deployedRuntime v) g s0 := by
  have hg : (UInt256.ofNat 0).toNat+(UInt256.ofNat out.size).toNat ≤ out.size := by
    rw [ulit_toNat' _ hb]
    change 0+out.size ≤ out.size
    omega
  cases site with
  | single =>
    obtain ⟨aw1,k1,C1,rd1⟩ := easBlocks.eas_block_16249_taken_packed (immWords := wordsOf (immStore v))
      (by simp only [payableSavedTail, List.length_cons]; omega) (by decide)
      (by rw [easPatchedValidJumpsRuntime v]; jump_dest) rd
    exact easBlocks.eas_block_9844 (immWords := wordsOf (immStore v))
      (by simp only [easBlocks.eas_block_16249_taken_stack, payableSavedTail, List.length_cons]; omega) hg rd1
  | multiAttest =>
    obtain ⟨aw1,k1,C1,rd1⟩ := easBlocks.eas_block_14884_taken_packed (immWords := wordsOf (immStore v))
      (by simp only [payableSavedTail, List.length_cons]; omega) (by decide)
      (by rw [easPatchedValidJumpsRuntime v]; jump_dest) rd
    exact easBlocks.eas_block_14965 (immWords := wordsOf (immStore v)) (R := e::target::R)
      (by simp only [List.length_cons]; omega) hg rd1
  | multiRevoke =>
    obtain ⟨aw1,k1,C1,rd1⟩ := easBlocks.eas_block_15498_taken_packed (immWords := wordsOf (immStore v))
      (by simp only [payableSavedTail, List.length_cons]; omega) (by decide)
      (by rw [easPatchedValidJumpsRuntime v]; jump_dest) rd
    exact easBlocks.eas_block_9844 (immWords := wordsOf (immStore v))
      (by simp only [easBlocks.eas_block_15498_taken_stack, payableSavedTail, List.length_cons]; omega) hg rd1

end Benchmarks.EAS.EAS
