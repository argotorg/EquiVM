import Benchmarks.UniswapV4PoolManager.FullMath96Words
import Benchmarks.UniswapV4PoolManager.EntryTrace
import Benchmarks.UniswapV4PoolManager.RuntimeBlocks_064

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables
open Benchmarks.UniswapV4PoolManager.Immutables
namespace Benchmarks.UniswapV4PoolManager
set_option maxRecDepth 5000

theorem fullMath96Trace {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem rdata : ByteArray} {aw a b ret : UInt256} {σ : AccountMap} {k C : Nat} {R : List UInt256}
    (v : PoolManagerImmutables) (hstack : R.length+9 ≤ 1024)
    (hret : (D_J (deployedRuntime v) 0).contains ret = true)
    (h : RD (deployedRuntime v) I g s0 ⟨22544⟩ (a :: b :: ret :: R) mem aw rdata σ k C) :
    if fullMathFits a b fullMathQ96 then ∃ k' C', RD (deployedRuntime v) I g s0 ret
      (fullMathWord a b fullMathQ96 :: R) mem aw rdata σ k' C'
    else RDrev (deployedRuntime v) g s0 := by
  by_cases hfit : fullMathFits a b fullMathQ96
  · rw [if_pos hfit]
    have hgt : UInt256.gt fullMathQ96 (fullMathHigh a b) = ⟨1⟩ :=
      ugt_one hfit
    have rd1 := poolManagerBlocks.poolManager_block_22544_fallthrough (by simp only [List.length_cons]; omega)
      (by change UInt256.isZero (UInt256.gt fullMathQ96 (fullMathHigh a b)) = ⟨0⟩; rw [hgt]; rfl) h
    simp only [poolManagerBlocks.poolManager_block_22544_fallthrough_stack] at rd1
    by_cases hz : fullMathHigh a b = ⟨0⟩
    · have heq : UInt256.sub (fullMathMM a b) (fullMathLow a b) =
          UInt256.lt (fullMathMM a b) (fullMathLow a b) := u256_sub_eq_zero_iff_eq.mp hz
      have rd2 := poolManagerBlocks.poolManager_block_22619_taken
        (by simp only [List.length_cons]; omega)
        (by change UInt256.eq (UInt256.sub (fullMathMM a b) (fullMathLow a b))
              (UInt256.lt (fullMathMM a b) (fullMathLow a b)) ≠ ⟨0⟩
            rw [heq, uInt256_eq_self]; decide)
        (by rw [poolManagerPatchedValidJumpsRuntime v]; jump_dest) rd1
      have rd3 := poolManagerBlocks.poolManager_block_22657
        (by change R.length+5 ≤ 1024; omega) hret rd2
      simp only [poolManagerBlocks.poolManager_block_22657_stack] at rd3
      rw [fullMath96Word_eq, if_pos hz]
      exact ⟨_, _, rd3⟩
    · have heq : UInt256.sub (fullMathMM a b) (fullMathLow a b) ≠
          UInt256.lt (fullMathMM a b) (fullMathLow a b) := fun he => hz (u256_sub_eq_zero_iff_eq.mpr he)
      have rd2 := poolManagerBlocks.poolManager_block_22619_fallthrough
        (by simp only [List.length_cons]; omega)
        (uInt256_eq_zero_of_ne (fun he => heq (uInt256_eq_one_eq he))) rd1
      have rd3 := poolManagerBlocks.poolManager_block_22624
        (by change R.length+6 ≤ 1024; omega) hret rd2
      simp only [poolManagerBlocks.poolManager_block_22624_stack] at rd3
      rw [fullMath96Word_eq, if_neg hz]
      exact ⟨_, _, rd3⟩
  · rw [if_neg hfit]
    have hgt : UInt256.gt fullMathQ96 (fullMathHigh a b) = ⟨0⟩ :=
      ugt_zero (Nat.le_of_not_gt hfit)
    have rd1 := poolManagerBlocks.poolManager_block_22544_taken (by simp only [List.length_cons]; omega)
      (by change UInt256.isZero (UInt256.gt fullMathQ96 (fullMathHigh a b)) ≠ ⟨0⟩; rw [hgt]; decide)
      (by rw [poolManagerPatchedValidJumpsRuntime v]; jump_dest) h
    exact emptyRevert v (by change R.length+9 ≤ 1024; exact hstack) rd1

end Benchmarks.UniswapV4PoolManager
