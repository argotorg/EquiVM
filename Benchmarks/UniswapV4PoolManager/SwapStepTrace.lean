import Benchmarks.UniswapV4PoolManager.SwapStepInputTrace
import Benchmarks.UniswapV4PoolManager.SwapStepOutputTrace

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables
open Benchmarks.UniswapV4PoolManager.Immutables
namespace Benchmarks.UniswapV4PoolManager
set_option maxRecDepth 5000

theorem swapStepTrace {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem rdata : ByteArray} {aw price target liquidity fee remaining j x1 x2 x3 x4 x6 x7 x8 : UInt256}
    {σ : AccountMap} {k C : Nat} {R : List UInt256}
    (v : PoolManagerImmutables) (hstack : R.length+34 ≤ 1024)
    (hp : price.toNat < 2^160) (ht : target.toNat < 2^160) (hl : liquidity.toNat < 2^128) (hf : fee.toNat < 2^24)
    (h : RD (deployedRuntime v) I g s0 (if swapStepExactInput remaining then ⟨19593⟩ else ⟨20607⟩)
      ([price, j, if swapStepDirection price target then ⟨1⟩ else ⟨0⟩, target, fee, liquidity,
        remaining, x1, x2, x3, x4, fee, x6, x7, x8, j] ++ R) mem aw rdata σ k C) :
    (swapStepFits price target liquidity remaining fee → ∃ k' C', C ≤ C' ∧
      RD (deployedRuntime v) I g s0 ⟨19714⟩
        ([(swapStepWord price target liquidity remaining fee).fee, j, ⟨160⟩,
          (swapStepWord price target liquidity remaining fee).amountOut,
          (swapStepWord price target liquidity remaining fee).amountIn,
          (swapStepWord price target liquidity remaining fee).next, solcAddrMask,
          remaining, x1, x2, x3, x4, fee, x6, x7, x8, j] ++ R) mem aw rdata σ k' C') ∧
    (¬swapStepFits price target liquidity remaining fee → RDrev (deployedRuntime v) g s0) := by
  cases he : swapStepExactInput remaining with
  | false =>
    simp only [swapStepFits, swapStepWord, he, Bool.false_eq_true, if_false] at h ⊢
    exact swapStepOutputTrace v (swapStepDirection price target) (by omega) hp ht hl hf h
  | true =>
    simp only [swapStepFits, swapStepWord, he, if_true] at h ⊢
    exact swapStepInputTrace v (swapStepDirection price target) hstack hp ht hl hf h

end Benchmarks.UniswapV4PoolManager
