import Benchmarks.UniswapV4PoolManager.NextAmount0Source
import Benchmarks.UniswapV4PoolManager.NextAmount0SubTrace
import Benchmarks.UniswapV4PoolManager.NextAmount0AddCoreTrace

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables
open Benchmarks.UniswapV4PoolManager.Immutables
namespace Benchmarks.UniswapV4PoolManager
set_option maxRecDepth 5000

theorem nextAmount0AddTrace {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem rdata : ByteArray} {aw price liquidity amount ret : UInt256}
    {σ : AccountMap} {k C : Nat} {R : List UInt256}
    (v : PoolManagerImmutables) (hstack : R.length+16 ≤ 1024)
    (hp : price.toNat < 2^160) (hl : liquidity.toNat < 2^128) (hprice : price ≠ ⟨0⟩)
    (hret : (D_J (deployedRuntime v) 0).contains ret = true)
    (h : RD (deployedRuntime v) I g s0 ⟨23815⟩ (price :: liquidity :: amount :: ret :: R) mem aw rdata σ k C) :
    if nextAmount0Fits price liquidity amount true then ∃ k' C', C ≤ C' ∧
      RD (deployedRuntime v) I g s0 ret (nextAmount0Word price liquidity amount true :: R) mem aw rdata σ k' C'
    else RDrev (deployedRuntime v) g s0 := by
  have hpc : UInt256.land price (UInt256.ofNat 1461501637330902918203684832716283019655932542975) = price :=
    solcAddrMask_clean hp
  by_cases hz : amount = ⟨0⟩
  · simp only [nextAmount0Fits, hz, true_or, if_true, nextAmount0Word]
    have rd1 := poolManagerBlocks.poolManager_block_23815_taken (by change R.length+6 ≤ 1024; omega)
      (by rw [hz]; decide) (by rw [poolManagerPatchedValidJumpsRuntime v]; jump_dest) h
    have rd2 := poolManagerBlocks.poolManager_block_23957 (by change R.length+4 ≤ 1024; omega) hret rd1
    exact ⟨_, _, by omega, rd2⟩
  · simp only [nextAmount0Fits, hz, false_or, nextAmount0Word, if_false]
    have rd1 := poolManagerBlocks.poolManager_block_23815_fallthrough
      (by change R.length+6 ≤ 1024; omega) (isZero_eq_zero_of_ne hz) h
    have rd2 := poolManagerBlocks.poolManager_block_23824 (by change R.length+11 ≤ 1024; omega)
      (by rw [poolManagerPatchedValidJumpsRuntime v]; jump_dest) rd1
    simp only [poolManagerBlocks.poolManager_block_23824_stack,
      hpc, amount0Numerator1_clean hl] at rd2
    have rd3 := poolManagerBlocks.poolManager_block_18722_fallthrough
      (by change R.length+12 ≤ 1024; omega) (isZero_eq_zero_of_ne hz) rd2
    have rd4 := poolManagerBlocks.poolManager_block_18729 (by change R.length+10 ≤ 1024; omega)
      (by rw [poolManagerPatchedValidJumpsRuntime v]; jump_dest) rd3
    have hr := nextAmount0AddCoreTrace (price := price) (liquidity := liquidity) (amount := amount)
      (ret := ret) (R := R) v hstack hprice hret rd4
    by_cases hf : nextAmount0CoreFits price liquidity amount true
    · rw [if_pos hf] at hr ⊢
      obtain ⟨k5, C5, hC5, rd5⟩ := hr
      exact ⟨k5, C5, by omega, rd5⟩
    · rw [if_neg hf] at hr ⊢
      exact hr

end Benchmarks.UniswapV4PoolManager
