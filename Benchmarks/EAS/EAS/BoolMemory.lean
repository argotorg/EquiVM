import Benchmarks.EAS.EAS.StructEncodeViews
import Benchmarks.EAS.EAS.ReturnDecode

variable {fork : Ethereum.Fork}
open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables Benchmarks.EAS.EAS.Immutables
namespace Benchmarks.EAS.EAS
set_option maxRecDepth 10000

-- LIBRARY CANDIDATE: a complete one-word call result loads as the first returned ABI word.
theorem callOutput32_load_word (mem out : ByteArray) (ptr : UInt256)
    (hb : out.size < UInt256.size) (hs : 32 ≤ out.size) (hin : ptr.toNat+32 ≤ mem.size) :
    memLoad ptr (callOutputMem mem out ptr ⟨32⟩) = calldataWord out 0 := by
  apply mloadWordValue_of_readWithPadding
  · rw [callOutput32_size mem out ptr hb hin]; omega
  · exact callOutput32_read_word mem out ptr hb hs (by omega)

theorem easDecodeBoolMemory {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap}
    {k C : Nat} {ptr ret : UInt256} {R : List UInt256} (v : EASImmutables)
    (hstack : R.length+4 ≤ 1024)
    (hvalid : (D_J (deployedRuntime v) 0).contains ret = true)
    (rd : RD fork (deployedRuntime v) ee g s0 ⟨7319⟩ (ptr::ret::R) mem aw rdata σ k C) :
    if memLoad ptr mem = ⟨0⟩ ∨ memLoad ptr mem = ⟨1⟩ then
      ∃ aw' k' C', RD fork (deployedRuntime v) ee g s0 ret (memLoad ptr mem :: R) mem aw' rdata σ k' C'
    else RDrev fork (deployedRuntime v) g s0 := by
  by_cases hb : memLoad ptr mem = ⟨0⟩ ∨ memLoad ptr mem = ⟨1⟩
  · rw [if_pos hb]
    have hc : UInt256.sub (memLoad ptr mem) (UInt256.isZero (UInt256.isZero (memLoad ptr mem))) = ⟨0⟩ := by
      rw [(boolWordClean_iff _).mpr hb, u256_sub_self]
    obtain ⟨aw1,k1,C1,rd1⟩ := easBlocks.eas_block_7319_fallthrough_packed (immWords := wordsOf (immStore v)) hstack hc rd
    exact easBlocks.eas_block_7331_packed (immWords := wordsOf (immStore v))
      (by simp only [List.length_cons]; omega) hvalid rd1
  · rw [if_neg hb]
    have hc : UInt256.sub (memLoad ptr mem) (UInt256.isZero (UInt256.isZero (memLoad ptr mem))) ≠ ⟨0⟩ := by
      intro he
      exact hb ((boolWordClean_iff _).mp (u256_sub_eq_zero_iff_eq.mp he).symm)
    obtain ⟨aw1,k1,C1,rd1⟩ := easBlocks.eas_block_7319_taken_packed (immWords := wordsOf (immStore v)) hstack hc
      (by rw [easPatchedValidJumpsRuntime v]; jump_dest) rd
    exact easBlocks.eas_block_402 (immWords := wordsOf (immStore v))
      (by simp only [easBlocks.eas_block_7319_taken_stack, List.length_cons]; omega) rd1

end Benchmarks.EAS.EAS
