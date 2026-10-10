import Benchmarks.UniswapV4PoolManager.SparseBytesMemory
import Benchmarks.UniswapV4PoolManager.RuntimeBlocks_015

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables
open Benchmarks.UniswapV4PoolManager.Immutables
namespace Benchmarks.UniswapV4PoolManager

theorem initializeReturnTrace {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem rdata : ByteArray} {aw a b c d tick : UInt256} {σ : AccountMap}
    {k C : Nat} {R : List UInt256} (v : PoolManagerImmutables)
    (hstack : R.length+10 ≤ 1024)
    (h : RD (deployedRuntime v) I g s0 ⟨4586⟩
      (a :: b :: c :: d :: tick :: ⟨32⟩ :: R) mem aw rdata σ k C) :
    RDret (deployedRuntime v) g s0 σ tick.toByteArray := by
  have hr := poolManagerBlocks.poolManager_block_4586 hstack h
  change RDret _ _ _ _
    ((writeWord mem (memLoad (UInt256.ofNat 64) mem).toNat tick).readWithPadding
      (memLoad (UInt256.ofNat 64) mem).toNat 32) at hr
  rw [writeWord_sparse_read_back] at hr
  exact hr

end Benchmarks.UniswapV4PoolManager
