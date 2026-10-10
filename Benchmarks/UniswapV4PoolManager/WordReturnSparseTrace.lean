import Benchmarks.UniswapV4PoolManager.SparseBytesMemory
import Benchmarks.UniswapV4PoolManager.RuntimeBlocks_008

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Benchmarks.UniswapV4PoolManager.Immutables
namespace Benchmarks.UniswapV4PoolManager

/-- The shared single-word return routine also works for sparse memory. -/
theorem wordReturnSparseTrace {I : ExecutionEnv} {g : Sat256} {s0 : State} {mem rdata : ByteArray}
    {aw word : UInt256} {σ : AccountMap} {k C : Nat} {R : List UInt256}
    (v : PoolManagerImmutables) (hstack : R.length+4 ≤ 1024)
    (h : RD (deployedRuntime v) I g s0 ⟨1954⟩ (word :: ⟨32⟩ :: R) mem aw rdata σ k C) :
    RDret (deployedRuntime v) g s0 σ word.toByteArray := by
  have hr := poolManagerBlocks.poolManager_block_1954 hstack h
  change RDret _ _ _ _
    ((writeWord mem (memLoad (UInt256.ofNat 64) mem).toNat word).readWithPadding
      (memLoad (UInt256.ofNat 64) mem).toNat 32) at hr
  rw [writeWord_sparse_read_back] at hr
  exact hr

end Benchmarks.UniswapV4PoolManager
