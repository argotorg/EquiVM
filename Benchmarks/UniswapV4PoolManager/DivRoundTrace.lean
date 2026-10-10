import Benchmarks.UniswapV4PoolManager.DivRoundWords
import Benchmarks.UniswapV4PoolManager.EntryTrace
import Benchmarks.UniswapV4PoolManager.RuntimeBlocks_065

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables
open Benchmarks.UniswapV4PoolManager.Immutables
namespace Benchmarks.UniswapV4PoolManager

theorem divRoundTrace {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem rdata : ByteArray} {aw x y ret : UInt256} {σ : AccountMap} {k C : Nat} {R : List UInt256}
    (v : PoolManagerImmutables) (hstack : R.length+5 ≤ 1024)
    (hret : (D_J (deployedRuntime v) 0).contains ret = true)
    (h : RD (deployedRuntime v) I g s0 ⟨23318⟩ (x :: y :: ret :: R) mem aw rdata σ k C) :
    RD (deployedRuntime v) I g s0 ret (divRoundWord x y :: R) mem aw rdata σ (k+12) (C+43) :=
  poolManagerBlocks.poolManager_block_23318 hstack hret h

end Benchmarks.UniswapV4PoolManager
