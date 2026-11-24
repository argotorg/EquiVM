import Benchmarks.EAS.EAS.ResolveManyEntry
import Benchmarks.EAS.EAS.ResolveManyZeroControl

variable {fork : Ethereum.Fork}
open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables Benchmarks.EAS.EAS.Immutables
namespace Benchmarks.EAS.EAS
set_option maxRecDepth 10000

def resolveManyZeroInitPC (rev : Bool) : UInt256 := if rev then ⟨15576⟩ else ⟨14976⟩
def resolveManyInitPC (rev : Bool) : UInt256 := if rev then ⟨15106⟩ else ⟨14485⟩
def resolveManyLoopPC (rev : Bool) : UInt256 := if rev then ⟨15112⟩ else ⟨14489⟩
def resolveManyLoadedStack (rev : Bool) (array target values available last len : UInt256) (R : List UInt256) : List UInt256 :=
  if rev then array::target::values::last::available::len::R else ⟨0⟩::array::target::values::last::available::len::R
def resolveManyLoopStack (rev : Bool) (i : Nat) (array target values available last total : UInt256)
    (len : Nat) (R : List UInt256) : List UInt256 :=
  if rev then UInt256.ofNat len::UInt256.ofNat i::array::target::values::last::available::total::R
  else UInt256.ofNat len::UInt256.ofNat i::⟨0⟩::array::target::values::last::available::total::R

theorem resolveManyLoad {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : Nat}
    {schema array target values available last len : UInt256} {R : List UInt256} (v : EASImmutables) (rev : Bool)
    (hstack : R.length+9 ≤ 1024)
    (ht : UInt256.land (memLoad (schema+UInt256.ofNat 32) mem) solcAddrMask = target)
    (rd : RD fork (deployedRuntime v) ee g s0 (resolveManyLoadPC rev)
      (resolveManyHeadStack rev schema array values available last len R) mem aw rdata σ k C) :
    ∃ aw' k' C', RD fork (deployedRuntime v) ee g s0
      (if target=⟨0⟩ then resolveManyZeroInitPC rev else resolveManyInitPC rev)
      (resolveManyLoadedStack rev array target values available last len R) mem aw' rdata σ k' C' := by
  have ht' : UInt256.land (UInt256.ofNat 1461501637330902918203684832716283019655932542975)
      (memLoad (UInt256.ofNat 32+schema) mem) = target := by
    rw [u256_add_comm, u256_land_comm]
    exact ht
  by_cases hz : target=⟨0⟩
  · rw [if_pos hz]
    have hg : UInt256.isZero (UInt256.land (UInt256.ofNat 1461501637330902918203684832716283019655932542975)
        (memLoad (UInt256.ofNat 32+schema) mem)) ≠ ⟨0⟩ := by rw [ht',hz]; decide
    cases rev with
    | false =>
      simp only [resolveManyLoadPC,resolveManyHeadStack,Bool.false_eq_true,if_false] at rd
      obtain ⟨aw1,k1,C1,rd1⟩ := easBlocks.eas_block_14452_taken_packed (immWords := wordsOf (immStore v))
        (by simp only [List.length_cons]; omega) hg (by rw [easPatchedValidJumpsRuntime v]; jump_dest) rd
      exact ⟨aw1,k1,C1,by simpa only [easBlocks.eas_block_14452_taken_stack,ht'] using rd1⟩
    | true =>
      simp only [resolveManyLoadPC,resolveManyHeadStack,if_true] at rd
      obtain ⟨aw1,k1,C1,rd1⟩ := easBlocks.eas_block_15073_taken_packed (immWords := wordsOf (immStore v))
        (by simp only [List.length_cons]; omega) hg (by rw [easPatchedValidJumpsRuntime v]; jump_dest) rd
      exact ⟨aw1,k1,C1,by simpa only [easBlocks.eas_block_15073_taken_stack,ht'] using rd1⟩
  · rw [if_neg hz]
    have hg : UInt256.isZero (UInt256.land (UInt256.ofNat 1461501637330902918203684832716283019655932542975)
        (memLoad (UInt256.ofNat 32+schema) mem)) = ⟨0⟩ := by rw [ht']; exact isZero_eq_zero_of_ne hz
    cases rev with
    | false =>
      simp only [resolveManyLoadPC,resolveManyHeadStack,Bool.false_eq_true,if_false] at rd
      obtain ⟨aw1,k1,C1,rd1⟩ := easBlocks.eas_block_14452_fallthrough_packed (immWords := wordsOf (immStore v))
        (by simp only [List.length_cons]; omega) hg rd
      exact ⟨aw1,k1,C1,by simpa only [easBlocks.eas_block_14452_fallthrough_stack,ht'] using rd1⟩
    | true =>
      simp only [resolveManyLoadPC,resolveManyHeadStack,if_true] at rd
      obtain ⟨aw1,k1,C1,rd1⟩ := easBlocks.eas_block_15073_fallthrough_packed (immWords := wordsOf (immStore v))
        (by simp only [List.length_cons]; omega) hg rd
      exact ⟨aw1,k1,C1,by simpa only [easBlocks.eas_block_15073_fallthrough_stack,ht'] using rd1⟩

theorem resolveManyInitZero {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C len : Nat}
    {array target values available last : UInt256} {R : List UInt256} (v : EASImmutables) (rev : Bool)
    (hstack : R.length+7 ≤ 1024)
    (rd : RD fork (deployedRuntime v) ee g s0 (resolveManyZeroInitPC rev)
      (resolveManyLoadedStack rev array target values available last (UInt256.ofNat len) R) mem aw rdata σ k C) :
    ∃ aw' k' C', RD fork (deployedRuntime v) ee g s0 (resolveManyZeroPC rev)
      (resolveManyZeroStack rev 0 values len R) mem aw' rdata σ k' C' := by
  cases rev with
  | false => exact easBlocks.eas_block_14976_packed (immWords := wordsOf (immStore v)) hstack rd
  | true => exact easBlocks.eas_block_15576_packed (immWords := wordsOf (immStore v)) (by simp only [List.length_cons,if_true]; omega) rd

theorem resolveManyInitLoop {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C len : Nat}
    {array target values available last : UInt256} {R : List UInt256} (v : EASImmutables) (rev : Bool)
    (hstack : R.length+9 ≤ 1024)
    (rd : RD fork (deployedRuntime v) ee g s0 (resolveManyInitPC rev)
      (resolveManyLoadedStack rev array target values available last (UInt256.ofNat len) R) mem aw rdata σ k C) :
    ∃ aw' k' C', RD fork (deployedRuntime v) ee g s0 (resolveManyLoopPC rev)
      (resolveManyLoopStack rev 0 array target values available last ⟨0⟩ len R) mem aw' rdata σ k' C' := by
  cases rev with
  | false => exact easBlocks.eas_block_14485_packed (immWords := wordsOf (immStore v)) hstack rd
  | true => exact easBlocks.eas_block_15106_packed (immWords := wordsOf (immStore v)) (by omega) rd

end Benchmarks.EAS.EAS
