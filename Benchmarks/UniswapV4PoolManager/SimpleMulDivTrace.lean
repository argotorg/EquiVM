import Benchmarks.UniswapV4PoolManager.SimpleMulDivWords
import Benchmarks.UniswapV4PoolManager.MemoryGas
import Benchmarks.UniswapV4PoolManager.Routines
import Benchmarks.UniswapV4PoolManager.RuntimeBlocks_057

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables
open Benchmarks.UniswapV4PoolManager.Immutables
namespace Benchmarks.UniswapV4PoolManager
set_option maxRecDepth 5000

/-- The Q128 multiply/divide used by the pool loop, followed by its fee-growth store. -/
theorem simpleMulDivFeeGrowthTrace {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem rdata : ByteArray} {aw step fee growth liquidity x1 x2 x3 x4 x5 x6 x7 x8 x9 : UInt256}
    {σ : AccountMap} {k C : Nat} {R : List UInt256}
    (v : PoolManagerImmutables) (hstack : R.length+13 ≤ 1024)
    (hf : memLoad (step+UInt256.ofNat 192) mem = fee)
    (hg : memLoad (step+UInt256.ofNat 224) mem = growth)
    (h : RD (deployedRuntime v) I g s0 ⟨20222⟩
      ([liquidity, x1, x2, x3, x4, x5, x6, x7, x8, x9, step] ++ R) mem aw rdata σ k C) :
    ∃ k' C', C ≤ C' ∧ RD (deployedRuntime v) I g s0 ⟨19833⟩
      ([⟨0⟩, x1, x2, x3, x4, x5, x6, x7, x8, x9, step] ++ R)
      ((growth + simpleMulDiv fee (UInt256.ofNat (2^128)) liquidity).toByteArray.write
        0 mem (step+UInt256.ofNat 224).toNat 32)
      (M (M aw (step+UInt256.ofNat 192) ⟨32⟩) (step+UInt256.ofNat 224) ⟨32⟩) rdata σ k' C' := by
  have rd := poolManagerBlocks.poolManager_block_20222 hstack
    (by rw [poolManagerPatchedValidJumpsRuntime v]; jump_dest) h
  simp only [poolManagerBlocks.poolManager_block_20222_stack,
    poolManagerBlocks.poolManager_block_20222_memory, hf, hg, memoryWords_idem] at rd
  rw [← simpleMulDiv_pow2 fee liquidity (n := 128) (by decide)] at rd
  exact ⟨_, _, by omega, rd⟩

end Benchmarks.UniswapV4PoolManager
