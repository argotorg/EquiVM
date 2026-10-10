import Benchmarks.UniswapV4PoolManager.BeforeSwapAmountTrace
import Benchmarks.UniswapV4PoolManager.BeforeSwapDeltaSource
import Benchmarks.UniswapV4PoolManager.BytesObjectWord
import Benchmarks.UniswapV4PoolManager.TickNetArithmetic
import Benchmarks.UniswapV4PoolManager.BlockResultTrace

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables
open Benchmarks.UniswapV4PoolManager.Immutables
namespace Benchmarks.UniswapV4PoolManager
open poolManagerBlocks
set_option maxRecDepth 5000

theorem beforeSwapDeltaTrace {I : ExecutionEnv} {g : Sat256} {s0 evm : State}
    {mem out : ByteArray} {aw ptr amount ret fee oldHook : UInt256} {k C : Nat} {R : List UInt256}
    (f : Frame) (v : PoolManagerImmutables) (hstack : R.length+10 ≤ 1024)
    (hview : BytesObjectView mem ptr out) (hsize : 64 ≤ out.size)
    (hfit : ptr.toNat+64 < UInt256.size)
    (hret : (D_J (deployedRuntime v) 0).contains ret = true)
    (h : RD (deployedRuntime v) I g s0 ⟨15508⟩
      (ptr :: ret :: fee :: oldHook :: amount :: R) mem aw out evm.accountMap k C) :
    blockResultTrace (deployedRuntime v) g s0 (fun _ post => post = evm ∧ ∃ aw' k' C',
      C+Cₘ aw' ≤ C'+Cₘ aw ∧ RD (deployedRuntime v) I g s0 ret
        (fee :: calldataWord out 32 :: (amount+beforeSwapSpecified out) :: R) mem aw' out post.accountMap k' C')
      (fun _ _ => False) (beforeSwapDeltaResult f evm amount out) := by
  have hload : memLoad (UInt256.ofNat 64+ptr) mem = calldataWord out 32 := by
    apply hview.loadWord hsize
    rw [u256_add_comm, uadd_word_ofNat_toNat ptr 64 hfit]
  have hclean : UInt256.signextend (UInt256.ofNat 15) (UInt256.sar (UInt256.ofNat 128) (calldataWord out 32)) =
      beforeSwapSpecified out := by
    simpa only [tickNetWord, beforeSwapSpecified] using tickNetWord_signextend (calldataWord out 32)
  rw [beforeSwapDeltaResult]
  generalize hdelta : beforeSwapSpecified out = delta at *
  by_cases hz : delta = ⟨0⟩
  · rw [if_pos hz]
    have hd := poolManager_block_15508_taken (by simp only [List.length_cons]; omega)
      (by rw [hload, hclean, hz]; decide) (by rw [poolManagerPatchedValidJumpsRuntime v]; jump_dest) h
    simp only [poolManager_block_15508_taken_stack, hload, hclean] at hd
    obtain ⟨k1, C1, hc, hr⟩ := beforeSwapReturnTrace v (by simp only [List.length_cons]; omega) hret hd
    refine ⟨rfl, _, k1, C1, ?_, by simpa only [hz, u256_add_zero] using hr⟩
    dsimp only [memExpansionCost] at hc ⊢
    omega
  · rw [if_neg hz]
    have hd := poolManager_block_15508_fallthrough (by simp only [List.length_cons]; omega)
      (by rw [hload, hclean]; exact isZero_eq_zero_of_ne hz) h
    simp only [poolManager_block_15508_fallthrough_stack, hload, hclean] at hd
    have ha := beforeSwapAmountTrace v hstack hret hd
    by_cases hf : int256Fits (EVM.signed amount+EVM.signed delta)
    · rw [if_pos hf] at ha
      rw [beforeSwapAmountResult, if_pos hf]
      by_cases hv : beforeSwapDirectionValid amount (amount+delta)
      · rw [if_pos hv] at ha ⊢
        obtain ⟨k1, C1, hc, hr⟩ := ha
        refine ⟨rfl, _, k1, C1, ?_, hr⟩
        dsimp only [memExpansionCost] at hc ⊢
        omega
      · rw [if_neg hv] at ha ⊢
        exact ha
    · rw [if_neg hf] at ha
      rw [beforeSwapAmountResult, if_neg hf]
      exact ha

end Benchmarks.UniswapV4PoolManager
