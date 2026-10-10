import Benchmarks.UniswapV4PoolManager.BeforeSwapReturnTrace
import Benchmarks.UniswapV4PoolManager.BeforeSwapAmountSource
import Benchmarks.UniswapV4PoolManager.SignedAddTrace
import Benchmarks.UniswapV4PoolManager.SignedComparison
import Benchmarks.UniswapV4PoolManager.ReachCost
import Benchmarks.UniswapV4PoolManager.RuntimeBlocks_044

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables
open Benchmarks.UniswapV4PoolManager.Immutables
namespace Benchmarks.UniswapV4PoolManager
open poolManagerBlocks
set_option maxRecDepth 5000

theorem beforeSwapDirectionTrace {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem rdata : ByteArray} {aw amount adjusted ret fee hookReturn : UInt256}
    {σ : AccountMap} {k C : Nat} {R : List UInt256}
    (v : PoolManagerImmutables) (hstack : R.length+6 ≤ 1024)
    (h : RD (deployedRuntime v) I g s0 ⟨15541⟩
      (adjusted :: ret :: fee :: hookReturn :: UInt256.slt amount ⟨0⟩ :: R) mem aw rdata σ k C) :
    if beforeSwapDirectionValid amount adjusted then
      ∃ k' C', C ≤ C' ∧ RD (deployedRuntime v) I g s0 ⟨15556⟩
        (ret :: fee :: hookReturn :: adjusted :: R) mem aw rdata σ k' C'
    else RDrev (deployedRuntime v) g s0 := by
  have hcheck : ∃ k1 C1, C ≤ C1 ∧ RD (deployedRuntime v) I g s0 ⟨15551⟩
      (UInt256.fromBool (decide (¬beforeSwapDirectionValid amount adjusted)) ::
        ret :: fee :: hookReturn :: adjusted :: R) mem aw rdata σ k1 C1 := by
    by_cases hn : EVM.signed amount < 0
    · have hc : UInt256.isZero (UInt256.slt amount ⟨0⟩) = ⟨0⟩ := by
        rw [slt_signed, show EVM.signed (⟨0⟩ : UInt256) = 0 from rfl, decide_eq_true hn]; rfl
      have hr := poolManager_block_15541_fallthrough hstack hc h
      have hg := poolManager_block_15548 hstack hr
      have he : UInt256.sgt adjusted ⟨0⟩ = UInt256.fromBool (decide (¬beforeSwapDirectionValid amount adjusted)) := by
        rw [sgt_signed]
        simp only [beforeSwapDirectionValid, if_pos hn, not_le]
        rfl
      simp only [poolManager_block_15548_stack, poolManager_block_15541_fallthrough_stack, he] at hg
      exact ⟨_, _, by omega, hg⟩
    · have hc : UInt256.isZero (UInt256.slt amount ⟨0⟩) ≠ ⟨0⟩ := by
        rw [slt_signed, show EVM.signed (⟨0⟩ : UInt256) = 0 from rfl, decide_eq_false hn]; decide
      have hr := poolManager_block_15541_taken hstack hc
        (by rw [poolManagerPatchedValidJumpsRuntime v]; jump_dest) h
      have hg := poolManager_block_15601 hstack
        (by rw [poolManagerPatchedValidJumpsRuntime v]; jump_dest) hr
      have he : UInt256.slt adjusted ⟨0⟩ = UInt256.fromBool (decide (¬beforeSwapDirectionValid amount adjusted)) := by
        rw [slt_signed]
        simp only [beforeSwapDirectionValid, if_neg hn, not_le]
        rfl
      simp only [poolManager_block_15601_stack, poolManager_block_15541_taken_stack, he] at hg
      exact ⟨_, _, by omega, hg⟩
  obtain ⟨k1, C1, hcost, hguard⟩ := hcheck
  by_cases hv : beforeSwapDirectionValid amount adjusted
  · rw [if_pos hv]
    have hr := poolManager_block_15551_fallthrough (by simp only [List.length_cons]; omega)
      (by rw [decide_eq_false (not_not.mpr hv)]; rfl) hguard
    exact ⟨_, _, by omega, hr⟩
  · rw [if_neg hv]
    have hr := poolManager_block_15551_taken (by simp only [List.length_cons]; omega)
      (by rw [decide_eq_true hv]; decide) (by rw [poolManagerPatchedValidJumpsRuntime v]; jump_dest) hguard
    exact poolManager_block_15561 (by simp only [poolManager_block_15551_taken_stack, List.length_cons]; omega) hr

theorem beforeSwapAmountTrace {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem rdata : ByteArray} {aw amount delta ret fee hookReturn : UInt256}
    {σ : AccountMap} {k C : Nat} {R : List UInt256}
    (v : PoolManagerImmutables) (hstack : R.length+10 ≤ 1024)
    (hret : (D_J (deployedRuntime v) 0).contains ret = true)
    (h : RD (deployedRuntime v) I g s0 ⟨15529⟩
      (delta :: ret :: fee :: hookReturn :: amount :: R) mem aw rdata σ k C) :
    if int256Fits (EVM.signed amount+EVM.signed delta) then
      if beforeSwapDirectionValid amount (amount+delta) then
        ∃ k' C', C ≤ C' ∧ RD (deployedRuntime v) I g s0 ret
          (fee :: hookReturn :: (amount+delta) :: R) mem aw rdata σ k' C'
      else RDrev (deployedRuntime v) g s0
    else RDrev (deployedRuntime v) g s0 := by
  have hstart := poolManager_block_15529 (by omega)
    (by rw [poolManagerPatchedValidJumpsRuntime v]; jump_dest) h
  simp only [poolManager_block_15529_stack] at hstart
  by_cases hf : int256Fits (EVM.signed amount+EVM.signed delta)
  · rw [if_pos hf]
    obtain ⟨k1, C1, hc1, hadd⟩ := RD_retainCost (fun _ _ hin =>
      checkedSignedAddPass v (by simp only [List.length_cons]; omega) hf
        (by rw [deployedRuntime_jumps]; jump_dest) hin) hstart
    have hdir := beforeSwapDirectionTrace v (by omega) hadd
    by_cases hv : beforeSwapDirectionValid amount (amount+delta)
    · rw [if_pos hv] at hdir ⊢
      obtain ⟨k2, C2, hc2, hguard⟩ := hdir
      have hdone := poolManager_block_15556 (by simp only [List.length_cons]; omega)
        (by rw [poolManagerPatchedValidJumpsRuntime v]; jump_dest) hguard
      obtain ⟨k3, C3, hc3, hreturn⟩ := beforeSwapReturnTrace v
        (by simp only [List.length_cons]; omega) hret hdone
      exact ⟨k3, C3, by omega, hreturn⟩
    · rw [if_neg hv] at hdir ⊢
      exact hdir
  · rw [if_neg hf]
    exact checkedSignedAddReverts v (by simp only [List.length_cons]; omega) hf hstart

end Benchmarks.UniswapV4PoolManager
