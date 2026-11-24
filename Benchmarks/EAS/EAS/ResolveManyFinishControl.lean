import Benchmarks.EAS.EAS.ResolveManyPayableEVM
import Benchmarks.EAS.EAS.ResolverManyEVM

variable {fork : Ethereum.Fork}
open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables Benchmarks.EAS.EAS.Immutables
namespace Benchmarks.EAS.EAS
set_option maxRecDepth 10000

def resolveManyFinishPC (rev : Bool) : UInt256 := if rev then ⟨15209⟩ else ⟨14588⟩

theorem resolveManyAccepted {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : Nat}
    {junk word : UInt256} {R : List UInt256} (v : EASImmutables) (rev : Bool)
    (hstack : R.length+5 ≤ 1024)
    (rd : RD fork (deployedRuntime v) ee g s0 (resolverDonePC true rev) (junk::word::R) mem aw rdata σ k C) :
    if word ≠ ⟨0⟩ then ∃ aw' k' C', RD fork (deployedRuntime v) ee g s0 (resolveManyFinishPC rev) R mem aw' rdata σ k' C'
    else RDrev fork (deployedRuntime v) g s0 := by
  by_cases hn : word ≠ ⟨0⟩
  · rw [if_pos hn]
    cases rev with
    | false => exact easBlocks.eas_block_14581_fallthrough_packed (immWords := wordsOf (immStore v)) (by omega) (isZero_eq_zero_of_ne hn) rd
    | true => exact easBlocks.eas_block_15202_fallthrough_packed (immWords := wordsOf (immStore v)) (by omega) (isZero_eq_zero_of_ne hn) rd
  · rw [if_neg hn]
    have hz : UInt256.isZero word ≠ ⟨0⟩ := by rw [not_ne_iff.mp hn]; decide
    cases rev with
    | false =>
      obtain ⟨a,j,D,hr⟩ := easBlocks.eas_block_14581_taken_packed (immWords := wordsOf (immStore v)) (by omega) hz
        (by rw [easPatchedValidJumpsRuntime v]; jump_dest) rd
      exact easBlocks.eas_block_14604 (immWords := wordsOf (immStore v)) (by change R.length+2 ≤ 1024; omega) hr
    | true =>
      obtain ⟨a,j,D,hr⟩ := easBlocks.eas_block_15202_taken_packed (immWords := wordsOf (immStore v)) (by omega) hz
        (by rw [easPatchedValidJumpsRuntime v]; jump_dest) rd
      exact easBlocks.eas_block_15216 (immWords := wordsOf (immStore v)) (by change R.length+2 ≤ 1024; omega) hr

theorem resolveManyFinish {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : Nat}
    {available total ret : UInt256} {R : List UInt256} (v : EASImmutables) (rev last : Bool)
    (hstack : R.length+5 ≤ 1024) (hret : (D_J (deployedRuntime v) 0).contains ret = true)
    (rd : RD fork (deployedRuntime v) ee g s0 (resolveManyFinishPC rev)
      (last.toUInt256::available::total::ret::R) mem aw rdata σ k C) :
    if last then
      ∃ aw' k' C', RD fork (deployedRuntime v) ee g s0 ⟨16342⟩ (available::⟨4692⟩::total::ret::R) mem aw' rdata σ k' C'
    else ∃ aw' k' C', RD fork (deployedRuntime v) ee g s0 ret (total::R) mem aw' rdata σ k' C' := by
  cases last with
  | false =>
    cases rev with
    | false =>
      obtain ⟨a,j,D,hr⟩ := easBlocks.eas_block_14588_fallthrough_packed (immWords := wordsOf (immStore v))
        (by simp only [List.length_cons]; omega) rfl rd
      exact easBlocks.eas_block_14592_packed (immWords := wordsOf (immStore v)) (by omega) hret hr
    | true =>
      obtain ⟨a,j,D,hr⟩ := easBlocks.eas_block_15209_fallthrough_packed (immWords := wordsOf (immStore v))
        (by simp only [List.length_cons]; omega) rfl rd
      exact easBlocks.eas_block_15213_packed (immWords := wordsOf (immStore v)) (by omega) hret hr
  | true =>
    have hmid : ∃ a j D, RD fork (deployedRuntime v) ee g s0 ⟨14595⟩ (available::total::ret::R) mem a rdata σ j D := by
      cases rev with
      | false =>
        exact easBlocks.eas_block_14588_taken_packed (immWords := wordsOf (immStore v))
          (by simp only [List.length_cons]; omega) (by decide) (by rw [easPatchedValidJumpsRuntime v]; jump_dest) rd
      | true =>
        exact easBlocks.eas_block_15209_taken_packed (immWords := wordsOf (immStore v))
          (by simp only [List.length_cons]; omega) (by decide) (by rw [easPatchedValidJumpsRuntime v]; jump_dest) rd
    obtain ⟨a,j,D,hr⟩ := hmid
    exact easBlocks.eas_block_14595_packed (immWords := wordsOf (immStore v))
      (by simp only [List.length_cons]; omega) (by rw [easPatchedValidJumpsRuntime v]; jump_dest) hr

theorem resolveManyLoopDone {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C len : Nat}
    {array target values available last total : UInt256} {R : List UInt256} (v : EASImmutables) (rev : Bool)
    (hstack : R.length+11 ≤ 1024)
    (rd : RD fork (deployedRuntime v) ee g s0 (resolveManyLoopPC rev)
      (resolveManyLoopStack rev len array target values available last total len R) mem aw rdata σ k C) :
    ∃ aw' k' C', RD fork (deployedRuntime v) ee g s0 (resolverManyEntryPC rev)
      (resolverManyEntryStack rev (UInt256.ofNat len) (UInt256.ofNat len) ⟨0⟩ array target values last available total R)
      mem aw' rdata σ k' C' := by
  have hg : UInt256.lt (UInt256.ofNat len) (UInt256.ofNat len) = ⟨0⟩ := ult_zero (le_refl _)
  cases rev with
  | false =>
    simp only [resolveManyLoopPC,resolveManyLoopStack,Bool.false_eq_true,if_false] at rd
    exact easBlocks.eas_block_14489_fallthrough_packed (immWords := wordsOf (immStore v))
      (by simp only [List.length_cons]; omega) hg rd
  | true =>
    simp only [resolveManyLoopPC,resolveManyLoopStack,if_true] at rd
    exact easBlocks.eas_block_15112_fallthrough_packed (immWords := wordsOf (immStore v))
      (by simp only [List.length_cons]; omega) hg rd

end Benchmarks.EAS.EAS
