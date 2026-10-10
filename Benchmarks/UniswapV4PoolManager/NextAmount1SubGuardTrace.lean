import Benchmarks.UniswapV4PoolManager.EntryTrace
import Benchmarks.UniswapV4PoolManager.RuntimeBlocks_060

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables
open Benchmarks.UniswapV4PoolManager.Immutables
namespace Benchmarks.UniswapV4PoolManager
set_option maxRecDepth 5000

theorem nextAmount1SubGuardTrace {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem rdata : ByteArray} {aw price q j0 : UInt256}
    {σ : AccountMap} {k C : Nat} {R : List UInt256}
    (v : PoolManagerImmutables) (hstack : R.length+6 ≤ 1024) (hp : price.toNat < 2^160)
    (h : RD (deployedRuntime v) I g s0 ⟨20808⟩ (q :: j0 :: price :: R) mem aw rdata σ k C) :
    if q.toNat < price.toNat then ∃ k' C', C ≤ C' ∧
      RD (deployedRuntime v) I g s0 ⟨20841⟩ (price :: q :: j0 :: price :: R) mem aw rdata σ k' C'
    else RDrev (deployedRuntime v) g s0 := by
  have hclean := solcAddrMask_clean hp
  by_cases hlt : q.toNat < price.toNat
  · rw [if_pos hlt]
    have hgt : UInt256.gt price q = ⟨1⟩ := ugt_one hlt
    have hg : UInt256.isZero (UInt256.gt (UInt256.land price solcAddrMask) q) = ⟨0⟩ := by
      rw [hclean, hgt]; rfl
    have rd1 := poolManagerBlocks.poolManager_block_20808_fallthrough hstack hg h
    simp only [poolManagerBlocks.poolManager_block_20808_fallthrough_stack] at rd1
    change RD _ _ _ _ _ (price :: q :: j0 :: UInt256.land price solcAddrMask :: R) mem aw rdata σ _ _ at rd1
    rw [hclean] at rd1
    exact ⟨_, _, by omega, rd1⟩
  · rw [if_neg hlt]
    have hgt : UInt256.gt price q = ⟨0⟩ := ugt_zero (Nat.le_of_not_gt hlt)
    have hg : UInt256.isZero (UInt256.gt (UInt256.land price solcAddrMask) q) ≠ ⟨0⟩ := by
      rw [hclean, hgt]; decide
    have rd1 := poolManagerBlocks.poolManager_block_20808_taken hstack hg
      (by rw [poolManagerPatchedValidJumpsRuntime v]; jump_dest) h
    exact poolManagerBlocks.poolManager_block_20879 (by change R.length+6 ≤ 1024; exact hstack) rd1

end Benchmarks.UniswapV4PoolManager
