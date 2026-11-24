import Benchmarks.EAS.EAS.Common
import Benchmarks.EAS.EAS.RuntimeBlocks_054
import Benchmarks.EAS.EAS.RuntimeBlocks_055

variable {fork : Ethereum.Fork}
open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables Benchmarks.EAS.EAS.Immutables
namespace Benchmarks.EAS.EAS
set_option maxRecDepth 10000

theorem easECDSAError {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap}
    {k C n : Nat} {ret : UInt256} {R : List UInt256} (v : EASImmutables)
    (hstack : R.length + 7 ≤ 1024) (hnat : n < UInt256.size)
    (hret : (D_J (deployedRuntime v) 0).contains ret = true)
    (rd : RD fork (deployedRuntime v) ee g s0 ⟨16786⟩ (UInt256.ofNat n::ret::R) mem aw rdata σ k C) :
    if n = 0 ∨ n = 4 then
      ∃ k' C', RD fork (deployedRuntime v) ee g s0 ret R mem aw rdata σ k' C'
    else RDrev fork (deployedRuntime v) g s0 := by
  by_cases hn : n < 5
  · have hc : UInt256.lt (UInt256.ofNat n) (UInt256.ofNat 5) = ⟨1⟩ :=
      ult_one (by simpa only [ulit_toNat' n hnat] using hn)
    have r1 := easBlocks.eas_block_16786_fallthrough (immWords := wordsOf (immStore v))
      (by simp only [List.length_cons]; omega) (by rw [hc]; decide) rd
    interval_cases n
    · rw [if_pos (Or.inl rfl)]
      have r2 := easBlocks.eas_block_16796_fallthrough (immWords := wordsOf (immStore v))
        (by simp only [List.length_cons]; omega) rfl r1
      have r3 := easBlocks.eas_block_16801 (immWords := wordsOf (immStore v)) (by omega) hret r2
      exact ⟨_,_,r3⟩
    · rw [if_neg (by decide)]
      have r2 := easBlocks.eas_block_16796_taken (immWords := wordsOf (immStore v))
        (by simp only [List.length_cons]; omega) (by decide)
        (by rw [easPatchedValidJumpsRuntime v]; jump_dest) r1
      have r3 := easBlocks.eas_block_16803_fallthrough (immWords := wordsOf (immStore v))
        (by simp only [List.length_cons]; omega) (by decide) r2
      exact easBlocks.eas_block_16812 (immWords := wordsOf (immStore v))
        (by simp only [List.length_cons]; omega) r3
    · rw [if_neg (by decide)]
      have r2 := easBlocks.eas_block_16796_taken (immWords := wordsOf (immStore v))
        (by simp only [List.length_cons]; omega) (by decide)
        (by rw [easPatchedValidJumpsRuntime v]; jump_dest) r1
      have r3 := easBlocks.eas_block_16803_taken (immWords := wordsOf (immStore v))
        (by simp only [List.length_cons]; omega) (by decide)
        (by rw [easPatchedValidJumpsRuntime v]; jump_dest) r2
      have r4 := easBlocks.eas_block_16905_fallthrough (immWords := wordsOf (immStore v))
        (by simp only [List.length_cons]; omega) (by decide) r3
      exact easBlocks.eas_block_16914 (immWords := wordsOf (immStore v))
        (by simp only [List.length_cons]; omega) r4
    · rw [if_neg (by decide)]
      have r2 := easBlocks.eas_block_16796_taken (immWords := wordsOf (immStore v))
        (by simp only [List.length_cons]; omega) (by decide)
        (by rw [easPatchedValidJumpsRuntime v]; jump_dest) r1
      have r3 := easBlocks.eas_block_16803_taken (immWords := wordsOf (immStore v))
        (by simp only [List.length_cons]; omega) (by decide)
        (by rw [easPatchedValidJumpsRuntime v]; jump_dest) r2
      have r4 := easBlocks.eas_block_16905_taken (immWords := wordsOf (immStore v))
        (by simp only [List.length_cons]; omega) (by decide)
        (by rw [easPatchedValidJumpsRuntime v]; jump_dest) r3
      have r5 := easBlocks.eas_block_17007_taken (immWords := wordsOf (immStore v))
        (by simp only [List.length_cons]; omega) (by decide)
        (by rw [easPatchedValidJumpsRuntime v]; jump_dest) r4
      exact easBlocks.eas_block_17016 (immWords := wordsOf (immStore v))
        (by simp only [easBlocks.eas_block_17007_taken_stack,List.length_cons]; omega) r5
    · rw [if_pos (Or.inr rfl)]
      have r2 := easBlocks.eas_block_16796_taken (immWords := wordsOf (immStore v))
        (by simp only [List.length_cons]; omega) (by decide)
        (by rw [easPatchedValidJumpsRuntime v]; jump_dest) r1
      have r3 := easBlocks.eas_block_16803_taken (immWords := wordsOf (immStore v))
        (by simp only [List.length_cons]; omega) (by decide)
        (by rw [easPatchedValidJumpsRuntime v]; jump_dest) r2
      have r4 := easBlocks.eas_block_16905_taken (immWords := wordsOf (immStore v))
        (by simp only [List.length_cons]; omega) (by decide)
        (by rw [easPatchedValidJumpsRuntime v]; jump_dest) r3
      have r5 := easBlocks.eas_block_17007_fallthrough (immWords := wordsOf (immStore v))
        (by simp only [List.length_cons]; omega) (by decide) r4
      have r6 := easBlocks.eas_block_17015 (immWords := wordsOf (immStore v))
        (by omega) hret r5
      exact ⟨_,_,r6⟩
  · rw [if_neg (by omega)]
    have hc : UInt256.lt (UInt256.ofNat n) (UInt256.ofNat 5) = ⟨0⟩ :=
      ult_zero (by simpa only [ulit_toNat' n hnat] using Nat.le_of_not_gt hn)
    have r1 := easBlocks.eas_block_16786_taken (immWords := wordsOf (immStore v))
      (by simp only [List.length_cons]; omega) (by rw [hc]; decide)
      (by rw [easPatchedValidJumpsRuntime v]; jump_dest) rd
    exact easBlocks.eas_block_17148 (immWords := wordsOf (immStore v))
      (by simp only [List.length_cons]; omega) r1

end Benchmarks.EAS.EAS
