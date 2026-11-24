import Benchmarks.EAS.EAS.ResolveManyLoad

variable {fork : Ethereum.Fork}
open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables Benchmarks.EAS.EAS.Immutables
namespace Benchmarks.EAS.EAS
set_option maxRecDepth 10000

def resolveManyPayableSite (rev : Bool) : PayableSite := if rev then .multiRevoke else .multiAttest
def resolveManyCheckedStack (rev : Bool) (i : Nat) (array target values available last total value : UInt256)
    (len : Nat) (R : List UInt256) : List UInt256 :=
  if rev then value::available::UInt256.ofNat len::array::target::values::last::total::UInt256.ofNat i::R
  else available::value::UInt256.ofNat len::⟨0⟩::array::target::values::last::total::UInt256.ofNat i::R

theorem resolveManyRead {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : Nat}
    {array target values available last total : UInt256} {words : List UInt256} {i limit : Nat} {R : List UInt256}
    (v : EASImmutables) (rev : Bool) (hstack : R.length+16 ≤ 1024)
    (hv : WordArrayMemoryView mem values words limit) (hi : i < words.length) (hlimit : limit < UInt256.size)
    (rd : RD fork (deployedRuntime v) ee g s0 (resolveManyLoopPC rev)
      (resolveManyLoopStack rev i array target values available last total words.length R) mem aw rdata σ k C) :
    if words[i] = ⟨0⟩ then
      ∃ aw' k' C', RD fork (deployedRuntime v) ee g s0 (payableCheckedPC (resolveManyPayableSite rev))
        (resolveManyCheckedStack rev i array target values available last total words[i] words.length R) mem aw' rdata σ k' C'
    else ∃ aw' k' C', RD fork (deployedRuntime v) ee g s0 (payableEntryPC (resolveManyPayableSite rev))
        (⟨1⟩::resolveManyCheckedStack rev i array target values available last total words[i] words.length R) mem aw' rdata σ k' C' := by
  have hlen : words.length < UInt256.size := by have := hv.span; omega
  have hprod : 32*i < UInt256.size := by have := hv.span; omega
  have hg : UInt256.lt (UInt256.ofNat i) (UInt256.ofNat words.length) ≠ ⟨0⟩ := by
    rw [ult_one (by rw [ulit_toNat' _ (by omega),ulit_toNat' _ hlen]; exact hi)]
    decide
  have hw := hv.get i hi
  cases rev with
  | false =>
    simp only [resolveManyLoopPC,resolveManyLoopStack,Bool.false_eq_true,if_false] at rd
    obtain ⟨a1,k1,C1,r1⟩ := easBlocks.eas_block_14489_taken_packed (immWords := wordsOf (immStore v))
      (by simp only [List.length_cons]; omega) hg (by rw [easPatchedValidJumpsRuntime v]; jump_dest) rd
    obtain ⟨a2,k2,C2,r2⟩ := easBlocks.eas_block_14704_packed (immWords := wordsOf (immStore v)) (by omega)
      (by rw [easPatchedValidJumpsRuntime v]; jump_dest) r1
    obtain ⟨a3,k3,C3,r3⟩ := easMemoryArrayIndex v (by simp only [List.length_cons]; omega)
      hi hlen hprod hv.length (by rw [easPatchedValidJumps]; jump_dest) r2
    by_cases hz : words[i] = ⟨0⟩
    · rw [if_pos hz]
      obtain ⟨a4,k4,C4,r4⟩ := easBlocks.eas_block_14717_fallthrough_packed (immWords := wordsOf (immStore v))
        (by simp only [List.length_cons]; omega) (by rw [hw,hz]; rfl) r3
      obtain ⟨a5,k5,C5,r5⟩ := easBlocks.eas_block_14728_fallthrough_packed (immWords := wordsOf (immStore v))
        (by simp only [List.length_cons]; omega) (by rw [hw,hz]; rfl) r4
      exact ⟨a5,k5,C5,by simpa only [easBlocks.eas_block_14728_fallthrough_stack,hw] using r5⟩
    · rw [if_neg hz]
      have hn : UInt256.isZero (UInt256.isZero (memLoad (UInt256.ofNat (values.toNat+32+32*i)) mem)) = ⟨1⟩ := by
        rw [hw,isZero_eq_zero_of_ne hz]; rfl
      obtain ⟨a4,k4,C4,r4⟩ := easBlocks.eas_block_14717_taken_packed (immWords := wordsOf (immStore v))
        (by simp only [List.length_cons]; omega) (by rw [hn]; decide)
        (by rw [easPatchedValidJumpsRuntime v]; jump_dest) r3
      exact ⟨a4,k4,C4,by simpa only [easBlocks.eas_block_14717_taken_stack,hw,isZero_eq_zero_of_ne hz] using r4⟩
  | true =>
    simp only [resolveManyLoopPC,resolveManyLoopStack,if_true] at rd
    obtain ⟨a1,k1,C1,r1⟩ := easBlocks.eas_block_15112_taken_packed (immWords := wordsOf (immStore v))
      (by simp only [List.length_cons]; omega) hg (by rw [easPatchedValidJumpsRuntime v]; jump_dest) rd
    obtain ⟨a2,k2,C2,r2⟩ := easBlocks.eas_block_15316_packed (immWords := wordsOf (immStore v)) (by omega)
      (by rw [easPatchedValidJumpsRuntime v]; jump_dest) r1
    obtain ⟨a3,k3,C3,r3⟩ := easMemoryArrayIndex v (by simp only [List.length_cons]; omega)
      hi hlen hprod hv.length (by rw [easPatchedValidJumps]; jump_dest) r2
    by_cases hz : words[i] = ⟨0⟩
    · rw [if_pos hz]
      obtain ⟨a4,k4,C4,r4⟩ := easBlocks.eas_block_15329_fallthrough_packed (immWords := wordsOf (immStore v))
        (by simp only [List.length_cons]; omega) (by rw [hw,hz]; rfl) r3
      obtain ⟨a5,k5,C5,r5⟩ := easBlocks.eas_block_15339_fallthrough_packed (immWords := wordsOf (immStore v))
        (by simp only [List.length_cons]; omega) (by rw [hw,hz]; rfl) r4
      exact ⟨a5,k5,C5,by simpa only [easBlocks.eas_block_15339_fallthrough_stack,hw] using r5⟩
    · rw [if_neg hz]
      have hn : UInt256.isZero (UInt256.isZero (memLoad (UInt256.ofNat (values.toNat+32+32*i)) mem)) = ⟨1⟩ := by
        rw [hw,isZero_eq_zero_of_ne hz]; rfl
      obtain ⟨a4,k4,C4,r4⟩ := easBlocks.eas_block_15329_taken_packed (immWords := wordsOf (immStore v))
        (by simp only [List.length_cons]; omega) (by rw [hn]; decide)
        (by rw [easPatchedValidJumpsRuntime v]; jump_dest) r3
      exact ⟨a4,k4,C4,by simpa only [easBlocks.eas_block_15329_taken_stack,hw,isZero_eq_zero_of_ne hz] using r4⟩

theorem resolveManyAmount {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C i len : Nat}
    {array target values available last total value : UInt256} {R : List UInt256} (v : EASImmutables) (rev : Bool)
    (hstack : R.length+14 ≤ 1024)
    (rd : RD fork (deployedRuntime v) ee g s0 (payableCheckedPC (resolveManyPayableSite rev))
      (resolveManyCheckedStack rev i array target values available last total value len R) mem aw rdata σ k C) :
    if value.toNat ≤ available.toNat then
      ∃ aw' k' C', RD fork (deployedRuntime v) ee g s0 (resolveManyLoopPC rev)
        (resolveManyLoopStack rev (i+1) array target values (UInt256.sub available value) last (total+value) len R)
        mem aw' rdata σ k' C'
    else RDrev fork (deployedRuntime v) g s0 := by
  have hi : UInt256.ofNat i+UInt256.ofNat 1 = UInt256.ofNat (i+1) := by
    rw [u256_add_comm]; exact u256_one_add_ofNat i
  by_cases hb : value.toNat ≤ available.toNat
  · rw [if_pos hb]
    cases rev with
    | false =>
      simp only [payableCheckedPC,resolveManyPayableSite,resolveManyCheckedStack,Bool.false_eq_true,if_false] at rd
      obtain ⟨a1,k1,C1,r1⟩ := easBlocks.eas_block_14733_fallthrough_packed (immWords := wordsOf (immStore v))
        (by simp only [List.length_cons]; omega) (ugt_zero hb) rd
      obtain ⟨a2,k2,C2,r2⟩ := easBlocks.eas_block_14740_packed (immWords := wordsOf (immStore v)) (by omega)
        (by rw [easPatchedValidJumpsRuntime v]; jump_dest) r1
      exact ⟨a2,k2,C2,by simpa only [easBlocks.eas_block_14740_stack,hi] using r2⟩
    | true =>
      simp only [payableCheckedPC,resolveManyPayableSite,resolveManyCheckedStack,if_true] at rd
      obtain ⟨a1,k1,C1,r1⟩ := easBlocks.eas_block_15344_fallthrough_packed (immWords := wordsOf (immStore v))
        (by simp only [List.length_cons]; omega) (ugt_zero hb) rd
      obtain ⟨a2,k2,C2,r2⟩ := easBlocks.eas_block_15351_packed (immWords := wordsOf (immStore v)) (by omega)
        (by rw [easPatchedValidJumpsRuntime v]; jump_dest) r1
      exact ⟨a2,k2,C2,by simpa only [easBlocks.eas_block_15351_stack,hi,u256_add_comm value total] using r2⟩
  · rw [if_neg hb]
    have hg : UInt256.gt value available ≠ ⟨0⟩ := by rw [ugt_one (by omega : available.toNat < value.toNat)]; decide
    cases rev with
    | false =>
      simp only [payableCheckedPC,resolveManyPayableSite,resolveManyCheckedStack,Bool.false_eq_true,if_false] at rd
      obtain ⟨a1,k1,C1,r1⟩ := easBlocks.eas_block_14733_taken_packed (immWords := wordsOf (immStore v))
        (by simp only [List.length_cons]; omega) hg (by rw [easPatchedValidJumpsRuntime v]; jump_dest) rd
      exact easBlocks.eas_block_14755 (immWords := wordsOf (immStore v))
        (by simp only [List.length_cons]; omega) r1
    | true =>
      simp only [payableCheckedPC,resolveManyPayableSite,resolveManyCheckedStack,if_true] at rd
      obtain ⟨a1,k1,C1,r1⟩ := easBlocks.eas_block_15344_taken_packed (immWords := wordsOf (immStore v))
        (by simp only [List.length_cons]; omega) hg (by rw [easPatchedValidJumpsRuntime v]; jump_dest) rd
      exact easBlocks.eas_block_15365 (immWords := wordsOf (immStore v))
        (by simp only [List.length_cons]; omega) r1

end Benchmarks.EAS.EAS
