import Benchmarks.UniswapV4PoolManager.SwapStepTailDeltaTrace

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables
open Benchmarks.UniswapV4PoolManager.Immutables
namespace Benchmarks.UniswapV4PoolManager

theorem swapStepTailDeltaResultTrace {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem rdata : ByteArray} {aw price next liquidity x0 x1 x2 : UInt256}
    {σ : AccountMap} {k C : Nat} {R : List UInt256}
    (v : PoolManagerImmutables) (input zeroForOne : Bool) (hstack : R.length+19 ≤ 1024)
    (hp : price.toNat < 2^160) (hn : next.toNat < 2^160) (hl : liquidity.toNat < 2^128)
    (h : RD (deployedRuntime v) I g s0 (if input then ⟨20667⟩ else ⟨19697⟩)
      ([if zeroForOne then ⟨1⟩ else ⟨0⟩, next, liquidity, price, x0, x1, x2] ++ R) mem aw rdata σ k C) :
    (swapStepDeltaFits price next liquidity input zeroForOne → ∃ k' C', C ≤ C' ∧
      RD (deployedRuntime v) I g s0 (if input then ⟨20684⟩ else ⟨19714⟩)
        ([x2, x0, x1, swapStepDeltaWord price next liquidity input zeroForOne] ++ R) mem aw rdata σ k' C') ∧
    (¬swapStepDeltaFits price next liquidity input zeroForOne → RDrev (deployedRuntime v) g s0) := by
  have hr := swapStepTailDeltaTrace v input zeroForOne hstack hp hn hl h
  constructor
  · intro hfit
    rwa [if_pos hfit] at hr
  · intro hfit
    rwa [if_neg hfit] at hr

end Benchmarks.UniswapV4PoolManager
