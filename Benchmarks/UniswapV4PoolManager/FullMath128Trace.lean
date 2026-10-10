import Benchmarks.UniswapV4PoolManager.FullMathWords
import Benchmarks.UniswapV4PoolManager.EntryTrace
import Benchmarks.UniswapV4PoolManager.RuntimeBlocks_063

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables
open Benchmarks.UniswapV4PoolManager.Immutables
namespace Benchmarks.UniswapV4PoolManager
set_option maxRecDepth 5000

theorem fullMath128Trace {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem rdata : ByteArray} {aw a b ret : UInt256} {σ : AccountMap} {k C : Nat} {R : List UInt256}
    (v : PoolManagerImmutables) (hstack : R.length+9 ≤ 1024)
    (hret : (D_J (deployedRuntime v) 0).contains ret = true)
    (h : RD (deployedRuntime v) I g s0 ⟨22275⟩ (a :: b :: ret :: R) mem aw rdata σ k C) :
    if fullMath128Fits a b then ∃ k' C', RD (deployedRuntime v) I g s0 ret
      (fullMath128Word a b :: R) mem aw rdata σ k' C'
    else RDrev (deployedRuntime v) g s0 := by
  by_cases hfit : fullMath128Fits a b
  · rw [if_pos hfit]
    have hgt : UInt256.gt fullMathQ128 (fullMathHigh a b) = ⟨1⟩ :=
      ugt_one (by rw [fullMathQ128_toNat]; exact hfit)
    have rd1 := poolManagerBlocks.poolManager_block_22275_fallthrough (by simp only [List.length_cons]; omega)
      (by change UInt256.isZero (UInt256.gt fullMathQ128 (fullMathHigh a b)) = ⟨0⟩; rw [hgt]; rfl) h
    simp only [poolManagerBlocks.poolManager_block_22275_fallthrough_stack] at rd1
    by_cases hz : fullMathHigh a b = ⟨0⟩
    · have heq : UInt256.sub (fullMathMM a b) (fullMathLow a b) =
          UInt256.lt (fullMathMM a b) (fullMathLow a b) := u256_sub_eq_zero_iff_eq.mp hz
      have rd2 := poolManagerBlocks.poolManager_block_22354_taken
        (by simp only [List.length_cons]; omega)
        (by change UInt256.eq (UInt256.sub (fullMathMM a b) (fullMathLow a b))
              (UInt256.lt (fullMathMM a b) (fullMathLow a b)) ≠ ⟨0⟩
            rw [heq, uInt256_eq_self]; decide)
        (by rw [poolManagerPatchedValidJumpsRuntime v]; jump_dest) rd1
      have rd3 := poolManagerBlocks.poolManager_block_22396
        (by change R.length+5 ≤ 1024; omega) hret rd2
      simp only [poolManagerBlocks.poolManager_block_22396_stack] at rd3
      rw [fullMath128Word, if_pos hz, fullMath128_div]
      exact ⟨_, _, rd3⟩
    · have heq : UInt256.sub (fullMathMM a b) (fullMathLow a b) ≠
          UInt256.lt (fullMathMM a b) (fullMathLow a b) := fun he => hz (u256_sub_eq_zero_iff_eq.mpr he)
      have rd2 := poolManagerBlocks.poolManager_block_22354_fallthrough
        (by simp only [List.length_cons]; omega)
        (uInt256_eq_zero_of_ne (fun he => heq (uInt256_eq_one_eq he))) rd1
      have rd3 := poolManagerBlocks.poolManager_block_22359
        (by change R.length+6 ≤ 1024; omega) hret rd2
      simp only [poolManagerBlocks.poolManager_block_22359_stack] at rd3
      rw [fullMath128Word, if_neg hz, fullMath128Wide, fullMath128_div, fullMath128_mul]
      exact ⟨_, _, rd3⟩
  · rw [if_neg hfit]
    have hgt : UInt256.gt fullMathQ128 (fullMathHigh a b) = ⟨0⟩ :=
      ugt_zero (by rw [fullMathQ128_toNat]; exact Nat.le_of_not_gt hfit)
    have rd1 := poolManagerBlocks.poolManager_block_22275_taken (by simp only [List.length_cons]; omega)
      (by change UInt256.isZero (UInt256.gt fullMathQ128 (fullMathHigh a b)) ≠ ⟨0⟩; rw [hgt]; decide)
      (by rw [poolManagerPatchedValidJumpsRuntime v]; jump_dest) h
    exact emptyRevert v (by change R.length+9 ≤ 1024; exact hstack) rd1

end Benchmarks.UniswapV4PoolManager
