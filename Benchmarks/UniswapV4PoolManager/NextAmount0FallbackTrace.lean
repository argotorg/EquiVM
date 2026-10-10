import Benchmarks.UniswapV4PoolManager.NextAmount0Words
import Benchmarks.UniswapV4PoolManager.Arithmetic
import Benchmarks.UniswapV4PoolManager.ReachCost
import Benchmarks.UniswapV4PoolManager.RuntimeBlocks_052
import Benchmarks.UniswapV4PoolManager.RuntimeBlocks_067

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables
open Benchmarks.UniswapV4PoolManager.Immutables
namespace Benchmarks.UniswapV4PoolManager
set_option maxRecDepth 5000

theorem nextAmount0FallbackTrace {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem rdata : ByteArray} {aw price liquidity amount ret junk : UInt256}
    {σ : AccountMap} {k C : Nat} {R : List UInt256}
    (v : PoolManagerImmutables) (hstack : R.length+10 ≤ 1024) (hp : price ≠ ⟨0⟩)
    (hret : (D_J (deployedRuntime v) 0).contains ret = true)
    (h : RD (deployedRuntime v) I g s0 ⟨23901⟩
      ([junk, price, amount, amount0Numerator1 liquidity, solcAddrMask, ret] ++ R) mem aw rdata σ k C) :
    if nextAmount0FallbackFits price liquidity amount then ∃ k' C', C ≤ C' ∧
      RD (deployedRuntime v) I g s0 ret (nextAmount0FallbackWord price liquidity amount :: R) mem aw rdata σ k' C'
    else RDrev (deployedRuntime v) g s0 := by
  have rd1 := poolManagerBlocks.poolManager_block_23901 (by change R.length+9 ≤ 1024; omega)
    (by rw [poolManagerPatchedValidJumpsRuntime v]; jump_dest) h
  have rd2 := poolManagerBlocks.poolManager_block_18722_fallthrough
    (by change R.length+10 ≤ 1024; exact hstack) (isZero_eq_zero_of_ne hp) rd1
  have rd3 := poolManagerBlocks.poolManager_block_18729 (by change R.length+8 ≤ 1024; omega)
    (by rw [poolManagerPatchedValidJumpsRuntime v]; jump_dest) rd2
  have rd4 := poolManagerBlocks.poolManager_block_23916 (by change R.length+7 ≤ 1024; omega)
    (by rw [poolManagerPatchedValidJumpsRuntime v]; jump_dest) rd3
  by_cases hf : nextAmount0FallbackFits price liquidity amount
  · rw [if_pos hf]
    obtain ⟨k5, C5, hC5, rd5⟩ := RD_retainCost (fun _ _ hin =>
      checkedAddPass v (by change R.length+7 ≤ 1024; omega) hf
        (by rw [deployedRuntime_jumps]; jump_dest) hin) rd4
    have rd6 := poolManagerBlocks.poolManager_block_23921 (by change R.length+6 ≤ 1024; omega) hret rd5
    exact ⟨_, _, by omega, rd6⟩
  · rw [if_neg hf]
    exact checkedAddReverts v (by change R.length+7 ≤ 1024; omega) (Nat.le_of_not_gt hf) rd4

end Benchmarks.UniswapV4PoolManager
