import Benchmarks.UniswapV4PoolManager.SignedPairABI
import Benchmarks.UniswapV4PoolManager.RuntimeBlocks_019

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Benchmarks.UniswapV4PoolManager.Immutables
namespace Benchmarks.UniswapV4PoolManager

theorem modifyLiquidityReturnTrace {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem rdata : ByteArray} {aw free caller fees : UInt256} {σ : AccountMap} {k C : Nat} {R : List UInt256}
    (v : PoolManagerImmutables) (hstack : R.length+5 ≤ 1024)
    (hf : free.toNat+64 < UInt256.size) (hfree : memLoad (UInt256.ofNat 64) mem = free)
    (h : RD (deployedRuntime v) I g s0 ⟨6240⟩ (fees :: caller :: UInt256.ofNat 64 :: R)
      mem aw rdata σ k C) :
    RDret (deployedRuntime v) g s0 σ (wordBytes [caller, fees]) := by
  have hr := poolManagerBlocks.poolManager_block_6240 hstack h
  have h32 := uadd_word_ofNat_toNat free 32 (by omega)
  rw [hfree, h32] at hr
  change RDret (deployedRuntime v) g s0 σ
    ((wordSequenceMemory mem free.toNat [caller, fees]).readWithPadding free.toNat (32*[caller, fees].length)) at hr
  rw [wordSequenceMemory_read] at hr
  exact hr

end Benchmarks.UniswapV4PoolManager
