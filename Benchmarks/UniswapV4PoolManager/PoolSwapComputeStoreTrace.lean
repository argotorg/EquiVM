import Benchmarks.UniswapV4PoolManager.SwapStepWords
import Benchmarks.UniswapV4PoolManager.SignedComparison
import Benchmarks.UniswapV4PoolManager.RuntimeBlocks_056

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables
open Benchmarks.UniswapV4PoolManager.Immutables
namespace Benchmarks.UniswapV4PoolManager
set_option maxRecDepth 5000

def poolSwapComputeStoreMemory (mem : ByteArray) (step state : UInt256) (w : SwapStepWords) : ByteArray :=
  w.next.toByteArray.write 0
    (w.amountIn.toByteArray.write 0
      (w.amountOut.toByteArray.write 0
        (w.fee.toByteArray.write 0 mem (step+UInt256.ofNat 192).toNat 32)
        (step+UInt256.ofNat 160).toNat 32)
      (step+UInt256.ofNat 128).toNat 32) state.toNat 32

def poolSwapComputeStoreAW (aw step state params : UInt256) : UInt256 :=
  M (M (M (M (M aw (step+UInt256.ofNat 192) ⟨32⟩) (step+UInt256.ofNat 160) ⟨32⟩)
    (step+UInt256.ofNat 128) ⟨32⟩) state ⟨32⟩) params ⟨32⟩

theorem poolSwapComputeStoreTrace {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem rdata : ByteArray} {w : SwapStepWords}
    {aw step state params remaining x1 specified fee protocol amountToProtocol dir pool x3 x4 : UInt256}
    {σ : AccountMap} {k C : Nat} {R : List UInt256}
    (v : PoolManagerImmutables) (hstack : R.length+21 ≤ 1024) (hn : w.next.toNat < 2^160)
    (hs : memLoad params (poolSwapComputeStoreMemory mem step state w) = specified)
    (h : RD (deployedRuntime v) I g s0 ⟨19714⟩
      ([w.fee, step, ⟨160⟩, w.amountOut, w.amountIn, w.next, solcAddrMask,
        remaining, x1, params, x3, x4, fee, protocol, amountToProtocol, dir, step, pool, state] ++ R)
      mem aw rdata σ k C) :
    ∃ C', C ≤ C' ∧ RD (deployedRuntime v) I g s0
      (if 0 < EVM.signed specified then ⟨19740⟩ else ⟨20320⟩)
      ([remaining, x1, params, x3, x4, fee, protocol, amountToProtocol, dir, step, pool, state] ++ R)
      (poolSwapComputeStoreMemory mem step state w) (poolSwapComputeStoreAW aw step state params)
      rdata σ (k+22) C' := by
  have hclean := solcAddrMask_clean hn
  by_cases hpos : 0 < EVM.signed specified
  · rw [if_pos hpos]
    have hg : UInt256.sgt specified ⟨0⟩ = ⟨1⟩ := by
      rw [sgt_signed, decide_eq_true (show EVM.signed (⟨0⟩ : UInt256) < EVM.signed specified from hpos)]
      rfl
    have rd := poolManagerBlocks.poolManager_block_19714_fallthrough hstack
      (by rw [hclean]; change UInt256.eq ⟨0⟩ (UInt256.sgt (memLoad params (poolSwapComputeStoreMemory mem step state w)) ⟨0⟩) = _
          rw [hs, hg]; rfl) h
    simp only [poolManagerBlocks.poolManager_block_19714_fallthrough_stack,
      poolManagerBlocks.poolManager_block_19714_fallthrough_memory, hclean] at rd
    exact ⟨_, by omega, rd⟩
  · rw [if_neg hpos]
    have hg : UInt256.sgt specified ⟨0⟩ = ⟨0⟩ := by
      rw [sgt_signed, decide_eq_false (show ¬EVM.signed (⟨0⟩ : UInt256) < EVM.signed specified from hpos)]
      rfl
    have rd := poolManagerBlocks.poolManager_block_19714_taken hstack
      (by rw [hclean]; change UInt256.eq ⟨0⟩ (UInt256.sgt (memLoad params (poolSwapComputeStoreMemory mem step state w)) ⟨0⟩) ≠ _
          rw [hs, hg]; decide)
      (by rw [poolManagerPatchedValidJumpsRuntime v]; jump_dest) h
    simp only [poolManagerBlocks.poolManager_block_19714_taken_stack,
      poolManagerBlocks.poolManager_block_19714_taken_memory, hclean] at rd
    exact ⟨_, by omega, rd⟩

end Benchmarks.UniswapV4PoolManager
