import Benchmarks.UniswapV4PoolManager.SafeCast160Trace
import Benchmarks.UniswapV4PoolManager.Arithmetic
import Benchmarks.UniswapV4PoolManager.ReachCost
import Benchmarks.UniswapV4PoolManager.RuntimeBlocks_059

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables
open Benchmarks.UniswapV4PoolManager.Immutables
namespace Benchmarks.UniswapV4PoolManager
set_option maxRecDepth 5000

theorem nextAmount1AddTailTrace {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem rdata : ByteArray} {aw price q liquidity amount j0 j1 j2 j3 : UInt256}
    {σ : AccountMap} {k C : Nat} {R : List UInt256}
    (v : PoolManagerImmutables) (hstack : R.length+13 ≤ 1024) (hp : price.toNat < 2^160)
    (h : RD (deployedRuntime v) I g s0 ⟨20520⟩
      ([q, ⟨20528⟩, ⟨20533⟩, liquidity, price, j0, j1, j2, j3, amount, solcAddrMask] ++ R)
      mem aw rdata σ k C) :
    if price.toNat+q.toNat < 2^160 then ∃ k' C', C ≤ C' ∧
      RD (deployedRuntime v) I g s0 ⟨20464⟩
        ([price+q, liquidity, price, j0, j1, j2, j3, amount, solcAddrMask] ++ R) mem aw rdata σ k' C'
    else RDrev (deployedRuntime v) g s0 := by
  have rd1 := poolManagerBlocks.poolManager_block_20520 (by change R.length+13 ≤ 1024; exact hstack)
    (by rw [poolManagerPatchedValidJumpsRuntime v]; jump_dest) h
  simp only [poolManagerBlocks.poolManager_block_20520_stack, solcAddrMask_clean hp] at rd1
  by_cases h256 : price.toNat+q.toNat < UInt256.size
  · obtain ⟨k2, C2, hC2, rd2⟩ := RD_retainCost (fun _ _ hin =>
      checkedAddPass v (by change R.length+13 ≤ 1024; exact hstack) h256
        (by rw [deployedRuntime_jumps]; jump_dest) hin) rd1
    have rd3 := poolManagerBlocks.poolManager_block_20528
      (by change R.length+11 ≤ 1024; omega)
      (by rw [poolManagerPatchedValidJumpsRuntime v]; jump_dest) rd2
    have hc := uintToUint160CostTrace v (by change R.length+12 ≤ 1024; omega)
      (by rw [deployedRuntime_jumps]; jump_dest) rd3
    have hr : (price+q).toNat = price.toNat+q.toNat := by rw [uadd_toNat, Nat.mod_eq_of_lt h256]
    rw [hr] at hc
    by_cases h160 : price.toNat+q.toNat < 2^160
    · rw [if_pos h160] at hc ⊢
      obtain ⟨k4, C4, hC4, rd4⟩ := hc
      have rd5 := poolManagerBlocks.poolManager_block_20533
        (by change R.length+10 ≤ 1024; omega)
        (by rw [poolManagerPatchedValidJumpsRuntime v]; jump_dest) rd4
      exact ⟨_, _, by omega, rd5⟩
    · rw [if_neg h160] at hc ⊢
      exact hc
  · have h160 : ¬price.toNat+q.toNat < 2^160 := by
      change ¬price.toNat+q.toNat < 2^256 at h256
      omega
    rw [if_neg h160]
    exact checkedAddReverts v (by change R.length+13 ≤ 1024; exact hstack) (Nat.le_of_not_gt h256) rd1

end Benchmarks.UniswapV4PoolManager
