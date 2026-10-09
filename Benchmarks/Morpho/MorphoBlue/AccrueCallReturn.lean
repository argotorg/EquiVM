import Benchmarks.Morpho.MorphoBlue.Allocation
import Benchmarks.Morpho.MorphoBlue.Dispatch

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables
open Benchmarks.Morpho.MorphoBlue.Immutables
namespace Benchmarks.Morpho.MorphoBlue
set_option maxRecDepth 1000

section Routines
variable {v : MorphoImmutables} {ee : ExecutionEnv} {g : Sat256} {s0 : State}
  {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : Nat}
  {ptr ret id elapsed : UInt256} {R : List UInt256}

theorem morphoAccrueDecodeResume (n : Nat) (hn : n ≤ 32)
    (hstack : R.length + 22 ≤ 1024) (hfit : ptr.toNat + 63 ≤ 2 ^ 64 - 1)
    (h : RD (deployedRuntime v) ee g s0 (UInt256.ofNat 13893)
      ([UInt256.ofNat n, ptr, UInt256.ofNat 32, ptr, solcAddrMask, id,
        UInt256.ofNat 32, UInt256.ofNat 3, UInt256.ofNat 0, UInt256.ofNat 64,
        uint128Mask, ret, elapsed] ++ R) mem aw rdata σ k C) :
    if n = 32 then
      ∃ aw' k' C', RD (deployedRuntime v) ee g s0 (UInt256.ofNat 13407)
        ([UInt256.ofNat 96, elapsed, solcAddrMask, id, UInt256.ofNat 32,
          UInt256.ofNat 3, UInt256.ofNat 0, UInt256.ofNat 64, uint128Mask, ret,
          memLoad ptr (returnReserveMem mem ptr 32)] ++ R)
        (returnReserveMem mem ptr 32) aw' rdata σ k' C'
    else RDrev (deployedRuntime v) g s0 := by
  have rd1 := morphoBlocks.morpho_block_13893 (immWords := wordsOf (immStore v))
    (by simp only [List.append, List.length_cons]; omega)
    (by rw [morphoPatchedValidJumpsRuntime v]; jump_dest) h
  obtain ⟨aw2, k2, C2, rd2⟩ := morphoAllocDynamic (v := v) n
    (by simp only [morphoBlocks.morpho_block_13893_stack, List.append, List.length_cons]; omega)
    (by rw [morphoPatchedValidJumps v]; jump_dest) (by omega) rd1
  by_cases heq : n = 32
  · rw [if_pos heq]
    subst n
    have rd3 := morphoBlocks.morpho_block_13903_fallthrough (immWords := wordsOf (immStore v))
      (by simp only [List.append, List.length_cons]; omega)
      (by rw [word_add_sub_left]; decide) rd2
    obtain ⟨aw4, k4, C4, rd4⟩ := morphoBlocks.morpho_block_13912_packed
      (immWords := wordsOf (immStore v)) (by simp only [List.append, List.length_cons]; omega)
      (by rw [morphoPatchedValidJumpsRuntime v]; jump_dest) rd3
    exact ⟨aw4, k4, C4, rd4⟩
  · rw [if_neg heq]
    have rd3 := morphoBlocks.morpho_block_13903_taken (immWords := wordsOf (immStore v))
      (by simp only [List.append, List.length_cons]; omega)
      (by rw [word_add_sub_left, slt_ofNat_lit_one_low (by norm_num) (by omega)]; decide)
      (by rw [morphoPatchedValidJumpsRuntime v]; jump_dest) rd2
    exact morphoBlocks.morpho_block_7120 (immWords := wordsOf (immStore v))
      (by simp only [List.append, List.length_cons]; omega) rd3

theorem morphoAccrueCallFalse (hstack : R.length + 22 ≤ 1024)
    (hsize : rdata.size < UInt256.size)
    (h : RD (deployedRuntime v) ee g s0 (UInt256.ofNat 13394)
      ([UInt256.ofNat 0, elapsed, solcAddrMask, id, UInt256.ofNat 32,
        UInt256.ofNat 3, UInt256.ofNat 0, UInt256.ofNat 64, uint128Mask, ret, ptr] ++ R)
      mem aw rdata σ k C) : RDrev (deployedRuntime v) g s0 := by
  have rd1 := morphoBlocks.morpho_block_13394_taken (immWords := wordsOf (immStore v))
    (by simp only [List.append, List.length_cons]; omega) (by decide) (by rw [morphoPatchedValidJumpsRuntime v]; jump_dest) h
  exact morphoBlocks.morpho_block_13927 (immWords := wordsOf (immStore v))
    (by simp only [List.append, List.length_cons]; omega)
    (by rw [UInt256.toNat_ofNat_of_lt hsize]; change 0 + rdata.size ≤ rdata.size; omega) rd1

theorem morphoAccrueCallTrue (hstack : R.length + 22 ≤ 1024)
    (hsize : rdata.size < UInt256.size) (hfit : ptr.toNat + 63 ≤ 2 ^ 64 - 1)
    (h : RD (deployedRuntime v) ee g s0 (UInt256.ofNat 13394)
      ([UInt256.ofNat 1, elapsed, solcAddrMask, id, UInt256.ofNat 32,
        UInt256.ofNat 3, UInt256.ofNat 0, UInt256.ofNat 64, uint128Mask, ret, ptr] ++ R)
      mem aw rdata σ k C) :
    if 32 ≤ rdata.size then
      ∃ aw' k' C', RD (deployedRuntime v) ee g s0 (UInt256.ofNat 13407)
        ([UInt256.ofNat 96, elapsed, solcAddrMask, id, UInt256.ofNat 32,
          UInt256.ofNat 3, UInt256.ofNat 0, UInt256.ofNat 64, uint128Mask, ret,
          memLoad ptr (returnReserveMem mem ptr 32)] ++ R)
        (returnReserveMem mem ptr 32) aw' rdata σ k' C'
    else RDrev (deployedRuntime v) g s0 := by
  have rd1 := morphoBlocks.morpho_block_13394_fallthrough (immWords := wordsOf (immStore v))
    (by simp only [List.append, List.length_cons]; omega) (by decide) h
  have rd2 := morphoBlocks.morpho_block_13401_taken (immWords := wordsOf (immStore v))
    (by simp only [List.append, List.length_cons]; omega) (by decide) (by rw [morphoPatchedValidJumpsRuntime v]; jump_dest) rd1
  by_cases hlen : 32 ≤ rdata.size
  · rw [if_pos hlen]
    have rd3 := morphoBlocks.morpho_block_13879_fallthrough (immWords := wordsOf (immStore v))
      (by simp only [List.append, List.length_cons]; omega) (ugt_zero (by rw [UInt256.toNat_ofNat_of_lt hsize]; exact hlen)) rd2
    simpa only [if_pos rfl] using morphoAccrueDecodeResume (v := v) 32 (by omega) hstack hfit rd3
  · rw [if_neg hlen]
    have rd3 := morphoBlocks.morpho_block_13879_taken (immWords := wordsOf (immStore v))
      (by simp only [List.append, List.length_cons]; omega)
      (by rw [ugt_one (by rw [UInt256.toNat_ofNat_of_lt hsize]; change rdata.size < 32; omega)]; decide)
      (by rw [morphoPatchedValidJumpsRuntime v]; jump_dest) rd2
    have rd4 := morphoBlocks.morpho_block_13920 (immWords := wordsOf (immStore v))
      (by simp only [List.append, List.length_cons]; omega)
      (by rw [morphoPatchedValidJumpsRuntime v]; jump_dest) rd3
    simpa only [if_neg (show rdata.size ≠ 32 by omega)] using
      morphoAccrueDecodeResume (v := v) rdata.size (by omega) hstack hfit rd4

end Routines
end Benchmarks.Morpho.MorphoBlue
