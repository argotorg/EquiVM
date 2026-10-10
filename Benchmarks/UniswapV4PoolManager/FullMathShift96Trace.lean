import Benchmarks.UniswapV4PoolManager.FullMath96Words
import Benchmarks.UniswapV4PoolManager.WordPow2
import Benchmarks.UniswapV4PoolManager.EntryTrace
import Benchmarks.UniswapV4PoolManager.RuntimeBlocks_064

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables
open Benchmarks.UniswapV4PoolManager.Immutables
namespace Benchmarks.UniswapV4PoolManager
set_option maxRecDepth 5000

theorem fullMathLow_shift96 (a : UInt256) :
    fullMathLow a fullMathQ96 = UInt256.shiftLeft a (UInt256.ofNat 96) :=
  wordMulPow2 a (n := 96) (by decide)

theorem fullMathShift96CostTrace {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem rdata : ByteArray} {aw a d ret : UInt256} {σ : AccountMap} {k C : Nat} {R : List UInt256}
    (v : PoolManagerImmutables) (hstack : R.length+10 ≤ 1024)
    (hret : (D_J (deployedRuntime v) 0).contains ret = true)
    (h : RD (deployedRuntime v) I g s0 ⟨22666⟩ (a :: d :: ret :: R) mem aw rdata σ k C) :
    if fullMathFits a fullMathQ96 d then ∃ k' C', C ≤ C' ∧
      RD (deployedRuntime v) I g s0 ret (fullMathWord a fullMathQ96 d :: R) mem aw rdata σ k' C'
    else RDrev (deployedRuntime v) g s0 := by
  have hl := fullMathLow_shift96 a
  by_cases hfit : fullMathFits a fullMathQ96 d
  · rw [if_pos hfit]
    have hgt : UInt256.gt d (fullMathHigh a fullMathQ96) = ⟨1⟩ := ugt_one hfit
    have hg : UInt256.isZero (UInt256.gt d (fullMathHigh a fullMathQ96)) = ⟨0⟩ := by rw [hgt]; rfl
    simp only [fullMathHigh, hl] at hg
    have rd1 := poolManagerBlocks.poolManager_block_22666_fallthrough
      (by simp only [List.length_cons]; omega) hg h
    simp only [poolManagerBlocks.poolManager_block_22666_fallthrough_stack, ← hl] at rd1
    by_cases hz : fullMathHigh a fullMathQ96 = ⟨0⟩
    · have heq : UInt256.sub (fullMathMM a fullMathQ96) (fullMathLow a fullMathQ96) =
          UInt256.lt (fullMathMM a fullMathQ96) (fullMathLow a fullMathQ96) :=
        u256_sub_eq_zero_iff_eq.mp hz
      have rd2 := poolManagerBlocks.poolManager_block_22742_taken
        (by simp only [List.length_cons]; omega)
        (by change UInt256.eq (UInt256.sub (fullMathMM a fullMathQ96) (fullMathLow a fullMathQ96))
              (UInt256.lt (fullMathMM a fullMathQ96) (fullMathLow a fullMathQ96)) ≠ ⟨0⟩
            rw [heq, uInt256_eq_self]; decide)
        (by rw [poolManagerPatchedValidJumpsRuntime v]; jump_dest) rd1
      have rd3 := poolManagerBlocks.poolManager_block_22844
        (by change R.length+5 ≤ 1024; omega) hret rd2
      rw [fullMathWord, if_pos hz]
      exact ⟨_, _, by omega, rd3⟩
    · have heq : UInt256.sub (fullMathMM a fullMathQ96) (fullMathLow a fullMathQ96) ≠
          UInt256.lt (fullMathMM a fullMathQ96) (fullMathLow a fullMathQ96) :=
        fun he => hz (u256_sub_eq_zero_iff_eq.mpr he)
      have rd2 := poolManagerBlocks.poolManager_block_22742_fallthrough
        (by simp only [List.length_cons]; omega)
        (uInt256_eq_zero_of_ne (fun he => heq (uInt256_eq_one_eq he))) rd1
      have rd3 := poolManagerBlocks.poolManager_block_22747
        (by change R.length+10 ≤ 1024; exact hstack) rd2
      have rd4 := poolManagerBlocks.poolManager_block_22833
        (by change R.length+9 ≤ 1024; omega) hret rd3
      rw [fullMathWord, if_neg hz]
      exact ⟨_, _, by omega, rd4⟩
  · rw [if_neg hfit]
    have hgt : UInt256.gt d (fullMathHigh a fullMathQ96) = ⟨0⟩ := ugt_zero (Nat.le_of_not_gt hfit)
    have hg : UInt256.isZero (UInt256.gt d (fullMathHigh a fullMathQ96)) ≠ ⟨0⟩ := by rw [hgt]; decide
    simp only [fullMathHigh, hl] at hg
    have rd1 := poolManagerBlocks.poolManager_block_22666_taken
      (by simp only [List.length_cons]; omega) hg
      (by rw [poolManagerPatchedValidJumpsRuntime v]; jump_dest) h
    exact emptyRevert v (by change R.length+9 ≤ 1024; omega) rd1

end Benchmarks.UniswapV4PoolManager
