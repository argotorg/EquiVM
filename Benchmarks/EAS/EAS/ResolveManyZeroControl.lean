import Benchmarks.EAS.EAS.MemoryArrayIndex

variable {fork : Ethereum.Fork}
open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables Benchmarks.EAS.EAS.Immutables
namespace Benchmarks.EAS.EAS
set_option maxRecDepth 10000

def resolveManyZeroPC (rev : Bool) : UInt256 := if rev then ⟨15584⟩ else ⟨14985⟩
def resolveManyZeroStack (rev : Bool) (i : Nat) (values : UInt256) (len : Nat) (R : List UInt256) : List UInt256 :=
  UInt256.ofNat i::values::UInt256.ofNat len::(if rev then R else ⟨0⟩::R)

theorem resolveManyZeroStep {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : Nat}
    {values : UInt256} {words : List UInt256} {i limit : Nat} {R : List UInt256} (v : EASImmutables) (rev : Bool)
    (hstack : R.length+10 ≤ 1024) (hv : WordArrayMemoryView mem values words limit)
    (hi : i < words.length) (hlimit : limit < UInt256.size)
    (rd : RD fork (deployedRuntime v) ee g s0 (resolveManyZeroPC rev)
      (resolveManyZeroStack rev i values words.length R) mem aw rdata σ k C) :
    if words[i] = ⟨0⟩ then
      ∃ aw' k' C', RD fork (deployedRuntime v) ee g s0 (resolveManyZeroPC rev)
        (resolveManyZeroStack rev (i+1) values words.length R) mem aw' rdata σ k' C'
    else RDrev fork (deployedRuntime v) g s0 := by
  have hlen : words.length < UInt256.size := by have := hv.span; omega
  have hprod : 32*i < UInt256.size := by have := hv.span; omega
  have hguard : UInt256.lt (UInt256.ofNat i) (UInt256.ofNat words.length) ≠ ⟨0⟩ := by
    rw [ult_one (by rw [ulit_toNat' _ (by omega),ulit_toNat' _ hlen]; exact hi)]
    decide
  have hw := hv.get i hi
  have hinc : UInt256.ofNat 1+UInt256.ofNat i = UInt256.ofNat (i+1) := u256_one_add_ofNat i
  cases rev with
  | false =>
    simp -failIfUnchanged only [resolveManyZeroPC,resolveManyZeroStack,Bool.false_eq_true,if_false] at rd ⊢
    obtain ⟨aw1,k1,C1,rd1⟩ := easBlocks.eas_block_14985_taken_packed (immWords := wordsOf (immStore v))
      (by simp -failIfUnchanged only [List.length_cons, Bool.false_eq_true, if_false, if_true]; omega) hguard (by rw [easPatchedValidJumpsRuntime v]; jump_dest) rd
    obtain ⟨aw2,k2,C2,rd2⟩ := easBlocks.eas_block_14998_packed (immWords := wordsOf (immStore v))
      (by simp -failIfUnchanged only [List.length_cons, Bool.false_eq_true, if_false, if_true]; omega) (by rw [easPatchedValidJumpsRuntime v]; jump_dest) rd1
    obtain ⟨aw3,k3,C3,rd3⟩ := easMemoryArrayIndex v
      (by simp -failIfUnchanged only [List.length_cons, Bool.false_eq_true, if_false, if_true]; omega) hi hlen hprod hv.length
      (by rw [easPatchedValidJumps]; jump_dest) rd2
    by_cases hz : words[i] = ⟨0⟩
    · rw [if_pos hz]
      obtain ⟨aw4,k4,C4,rd4⟩ := easBlocks.eas_block_15008_fallthrough_packed (immWords := wordsOf (immStore v))
        (by simp -failIfUnchanged only [List.length_cons, Bool.false_eq_true, if_false, if_true]; omega) (hw.trans hz) rd3
      obtain ⟨aw5,k5,C5,rd5⟩ := easBlocks.eas_block_15014_packed (immWords := wordsOf (immStore v))
        (by simp -failIfUnchanged only [List.length_cons, Bool.false_eq_true, if_false, if_true]; omega) (by rw [easPatchedValidJumpsRuntime v]; jump_dest) rd4
      exact ⟨aw5,k5,C5,by simpa only [easBlocks.eas_block_15014_stack,hinc] using rd5⟩
    · rw [if_neg hz]
      obtain ⟨aw4,k4,C4,rd4⟩ := easBlocks.eas_block_15008_taken_packed (immWords := wordsOf (immStore v))
        (by simp -failIfUnchanged only [List.length_cons, Bool.false_eq_true, if_false, if_true]; omega) (by rw [hw]; exact hz)
        (by rw [easPatchedValidJumpsRuntime v]; jump_dest) rd3
      exact easBlocks.eas_block_14795 (immWords := wordsOf (immStore v))
        (by omega) rd4
  | true =>
    simp -failIfUnchanged only [resolveManyZeroPC,resolveManyZeroStack,if_true] at rd ⊢
    obtain ⟨aw1,k1,C1,rd1⟩ := easBlocks.eas_block_15584_taken_packed (immWords := wordsOf (immStore v))
      (by simp -failIfUnchanged only [List.length_cons, Bool.false_eq_true, if_false, if_true]; omega) hguard (by rw [easPatchedValidJumpsRuntime v]; jump_dest) rd
    obtain ⟨aw2,k2,C2,rd2⟩ := easBlocks.eas_block_15599_packed (immWords := wordsOf (immStore v))
      (by simp -failIfUnchanged only [List.length_cons, Bool.false_eq_true, if_false, if_true]; omega) (by rw [easPatchedValidJumpsRuntime v]; jump_dest) rd1
    obtain ⟨aw3,k3,C3,rd3⟩ := easMemoryArrayIndex v
      (by simp -failIfUnchanged only [List.length_cons, Bool.false_eq_true, if_false, if_true]; omega) hi hlen hprod hv.length
      (by rw [easPatchedValidJumps]; jump_dest) rd2
    by_cases hz : words[i] = ⟨0⟩
    · rw [if_pos hz]
      obtain ⟨aw4,k4,C4,rd4⟩ := easBlocks.eas_block_15609_fallthrough_packed (immWords := wordsOf (immStore v))
        (by simp -failIfUnchanged only [List.length_cons, Bool.false_eq_true, if_false, if_true]; omega) (hw.trans hz) rd3
      obtain ⟨aw5,k5,C5,rd5⟩ := easBlocks.eas_block_15615_packed (immWords := wordsOf (immStore v))
        (by simp -failIfUnchanged only [List.length_cons, Bool.false_eq_true, if_false, if_true]; omega) (by rw [easPatchedValidJumpsRuntime v]; jump_dest) rd4
      exact ⟨aw5,k5,C5,by simpa only [easBlocks.eas_block_15615_stack,hinc] using rd5⟩
    · rw [if_neg hz]
      obtain ⟨aw4,k4,C4,rd4⟩ := easBlocks.eas_block_15609_taken_packed (immWords := wordsOf (immStore v))
        (by simp -failIfUnchanged only [List.length_cons, Bool.false_eq_true, if_false, if_true]; omega) (by rw [hw]; exact hz)
        (by rw [easPatchedValidJumpsRuntime v]; jump_dest) rd3
      exact easBlocks.eas_block_15407 (immWords := wordsOf (immStore v))
        (by simp only [easBlocks.eas_block_15609_taken_stack,List.length_cons]; omega) rd4

theorem resolveManyZeroDone {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C len : Nat}
    {values ret : UInt256} {R : List UInt256} (v : EASImmutables) (rev : Bool)
    (hstack : R.length+7 ≤ 1024) (hret : (D_J (deployedRuntime v) 0).contains ret = true)
    (rd : RD fork (deployedRuntime v) ee g s0 (resolveManyZeroPC rev)
      (resolveManyZeroStack rev len values len (ret::R)) mem aw rdata σ k C) :
    ∃ aw' k' C', RD fork (deployedRuntime v) ee g s0 ret (⟨0⟩::R) mem aw' rdata σ k' C' := by
  have hg : UInt256.lt (UInt256.ofNat len) (UInt256.ofNat len) = ⟨0⟩ := ult_zero (le_refl _)
  cases rev with
  | false =>
    simp -failIfUnchanged only [resolveManyZeroPC,resolveManyZeroStack,Bool.false_eq_true,if_false] at rd ⊢
    obtain ⟨aw1,k1,C1,rd1⟩ := easBlocks.eas_block_14985_fallthrough_packed (immWords := wordsOf (immStore v))
      (by simp -failIfUnchanged only [List.length_cons, Bool.false_eq_true, if_false, if_true]; omega) hg rd
    exact easBlocks.eas_block_14993_packed (immWords := wordsOf (immStore v)) (by omega) hret rd1
  | true =>
    simp -failIfUnchanged only [resolveManyZeroPC,resolveManyZeroStack,if_true] at rd ⊢
    obtain ⟨aw1,k1,C1,rd1⟩ := easBlocks.eas_block_15584_fallthrough_packed (immWords := wordsOf (immStore v))
      (by simp -failIfUnchanged only [List.length_cons, Bool.false_eq_true, if_false, if_true]; omega) hg rd
    exact easBlocks.eas_block_15592_packed (immWords := wordsOf (immStore v)) (by omega) hret rd1

end Benchmarks.EAS.EAS
