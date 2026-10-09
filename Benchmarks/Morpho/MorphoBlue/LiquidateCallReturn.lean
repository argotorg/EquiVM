import Benchmarks.Morpho.MorphoBlue.Allocation
import Benchmarks.Morpho.MorphoBlue.LiquidateGuards

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables
open Benchmarks.Morpho.MorphoBlue.Immutables
namespace Benchmarks.Morpho.MorphoBlue
set_option maxRecDepth 1000

section Routines
variable {v : MorphoImmutables} {ee : ExecutionEnv} {g : Sat256} {s0 : State}
  {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : Nat}
  {ptr id seized shares srcOff len : UInt256} {R : List UInt256}

theorem morphoLiquidateDecodeResume (n : Nat) (hn : n ≤ 32)
    (hstack : R.length + 20 ≤ 1024) (hfit : ptr.toNat + 63 ≤ 2 ^ 64 - 1)
    (h : RD (deployedRuntime v) ee g s0 (UInt256.ofNat 3678)
      ([ptr, UInt256.ofNat n, ptr] ++ liquidateGuardTail id seized shares srcOff len R) mem aw rdata σ k C) :
    if n = 32 then
      ∃ aw' k' C', RD (deployedRuntime v) ee g s0 (UInt256.ofNat 14189)
        ([UInt256.ofNat 128, id, calldataWord ee.calldata 164, memLoad ptr (returnReserveMem mem ptr 32), UInt256.ofNat 1577,
          UInt256.ofNat 1638, memLoad ptr (returnReserveMem mem ptr 32)] ++ liquidateGuardTail id seized shares srcOff len R)
        (returnReserveMem mem ptr 32) aw' rdata σ k' C'
    else RDrev (deployedRuntime v) g s0 := by
  have rd1 := morphoBlocks.morpho_block_3678 (immWords := wordsOf (immStore v))
    (by simp only [liquidateGuardTail, List.length_append, List.length_nil, List.append, List.length_cons]; omega)
    (by rw [morphoPatchedValidJumpsRuntime v]; jump_dest) h
  obtain ⟨aw2, k2, C2, rd2⟩ := morphoAllocDynamic (v := v) n
    (by simp only [morphoBlocks.morpho_block_3678_stack, liquidateGuardTail, List.length_append, List.length_nil, List.append, List.length_cons]; omega)
    (by rw [morphoPatchedValidJumps v]; jump_dest) (by omega) rd1
  by_cases heq : n = 32
  · rw [if_pos heq]
    subst n
    have rd3 := morphoBlocks.morpho_block_3691_fallthrough (immWords := wordsOf (immStore v))
      (by simp only [liquidateGuardTail, List.length_append, List.length_nil, List.append, List.length_cons]; omega)
      (by rw [word_add_sub_left]; decide) rd2
    obtain ⟨aw4, k4, C4, rd4⟩ := morphoBlocks.morpho_block_3700_packed
      (immWords := wordsOf (immStore v)) (by simp only [liquidateGuardTail, List.length_append, List.length_nil, List.append, List.length_cons]; omega)
      (by rw [morphoPatchedValidJumpsRuntime v]; jump_dest) rd3
    have rd5 := morphoBlocks.morpho_block_1559 (immWords := wordsOf (immStore v))
      (by simp only [liquidateGuardTail, List.length_append, List.length_nil, List.append, List.length_cons]; omega)
      (by rw [morphoPatchedValidJumpsRuntime v]; jump_dest) rd4
    exact ⟨aw4, _, _, rd5⟩
  · rw [if_neg heq]
    have rd3 := morphoBlocks.morpho_block_3691_taken (immWords := wordsOf (immStore v))
      (by simp only [liquidateGuardTail, List.length_append, List.length_nil, List.append, List.length_cons]; omega)
      (by rw [word_add_sub_left, slt_ofNat_lit_one_low (by norm_num) (by omega)]; decide)
      (by rw [morphoPatchedValidJumpsRuntime v]; jump_dest) rd2
    exact morphoBlocks.morpho_block_712 (immWords := wordsOf (immStore v))
      (by simp only [morphoBlocks.morpho_block_3691_taken_stack, liquidateGuardTail, List.length_append, List.length_nil, List.append, List.length_cons]; omega) rd3

theorem morphoLiquidateCallFalse (hstack : R.length + 20 ≤ 1024)
    (hsize : rdata.size < UInt256.size)
    (h : RD (deployedRuntime v) ee g s0 (UInt256.ofNat 1546)
      ([UInt256.ofNat 0, ptr] ++ liquidateGuardTail id seized shares srcOff len R)
      mem aw rdata σ k C) : RDrev (deployedRuntime v) g s0 := by
  have rd1 := morphoBlocks.morpho_block_1546_taken (immWords := wordsOf (immStore v))
    (by simp only [liquidateGuardTail, List.length_append, List.length_nil, List.append, List.length_cons]; omega) (by decide) (by rw [morphoPatchedValidJumpsRuntime v]; jump_dest) h
  exact morphoBlocks.morpho_block_3714 (immWords := wordsOf (immStore v))
    (by simp only [liquidateGuardTail, List.length_append, List.length_nil, List.append, List.length_cons]; omega)
    (by rw [UInt256.toNat_ofNat_of_lt hsize]; change 0 + rdata.size ≤ rdata.size; omega) rd1

theorem morphoLiquidateCallTrue (hstack : R.length + 20 ≤ 1024)
    (hsize : rdata.size < UInt256.size) (hfit : ptr.toNat + 63 ≤ 2 ^ 64 - 1)
    (h : RD (deployedRuntime v) ee g s0 (UInt256.ofNat 1546)
      ([UInt256.ofNat 1, ptr] ++ liquidateGuardTail id seized shares srcOff len R)
      mem aw rdata σ k C) :
    if 32 ≤ rdata.size then
      ∃ aw' k' C', RD (deployedRuntime v) ee g s0 (UInt256.ofNat 14189)
        ([UInt256.ofNat 128, id, calldataWord ee.calldata 164, memLoad ptr (returnReserveMem mem ptr 32), UInt256.ofNat 1577,
          UInt256.ofNat 1638, memLoad ptr (returnReserveMem mem ptr 32)] ++ liquidateGuardTail id seized shares srcOff len R)
        (returnReserveMem mem ptr 32) aw' rdata σ k' C'
    else RDrev (deployedRuntime v) g s0 := by
  have rd1 := morphoBlocks.morpho_block_1546_fallthrough (immWords := wordsOf (immStore v))
    (by simp only [liquidateGuardTail, List.length_append, List.length_nil, List.append, List.length_cons]; omega) (by decide) h
  have rd2 := morphoBlocks.morpho_block_1553_taken (immWords := wordsOf (immStore v))
    (by simp only [liquidateGuardTail, List.length_append, List.length_nil, List.append, List.length_cons]; omega) (by decide) (by rw [morphoPatchedValidJumpsRuntime v]; jump_dest) rd1
  by_cases hlen : 32 ≤ rdata.size
  · rw [if_pos hlen]
    have rd3 := morphoBlocks.morpho_block_3664_fallthrough (immWords := wordsOf (immStore v))
      (by simp only [liquidateGuardTail, List.length_append, List.length_nil, List.append, List.length_cons]; omega) (ugt_zero (by rw [UInt256.toNat_ofNat_of_lt hsize]; exact hlen)) rd2
    simpa only [if_pos rfl] using morphoLiquidateDecodeResume (v := v) 32 (by omega) hstack hfit rd3
  · rw [if_neg hlen]
    have rd3 := morphoBlocks.morpho_block_3664_taken (immWords := wordsOf (immStore v))
      (by simp only [liquidateGuardTail, List.length_append, List.length_nil, List.append, List.length_cons]; omega)
      (by rw [ugt_one (by rw [UInt256.toNat_ofNat_of_lt hsize]; change rdata.size < 32; omega)]; decide)
      (by rw [morphoPatchedValidJumpsRuntime v]; jump_dest) rd2
    have rd4 := morphoBlocks.morpho_block_3706 (immWords := wordsOf (immStore v))
      (by simp only [liquidateGuardTail, List.length_append, List.length_nil, List.append, List.length_cons]; omega)
      (by rw [morphoPatchedValidJumpsRuntime v]; jump_dest) rd3
    simpa only [if_neg (show rdata.size ≠ 32 by omega)] using
      morphoLiquidateDecodeResume (v := v) rdata.size (by omega) hstack hfit rd4

end Routines
end Benchmarks.Morpho.MorphoBlue
