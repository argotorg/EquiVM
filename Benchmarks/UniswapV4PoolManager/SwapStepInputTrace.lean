import Benchmarks.UniswapV4PoolManager.SwapStepInputSelectTrace
import Benchmarks.UniswapV4PoolManager.SwapStepInputDeltaTrace
import Benchmarks.UniswapV4PoolManager.SwapStepTailDeltaResultTrace
import Benchmarks.UniswapV4PoolManager.SwapStepWords

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables
open Benchmarks.UniswapV4PoolManager.Immutables
namespace Benchmarks.UniswapV4PoolManager
set_option maxRecDepth 5000

theorem swapStepInputTrace {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem rdata : ByteArray} {aw price target liquidity fee remaining j x1 x2 x3 x4 x6 x7 x8 : UInt256}
    {σ : AccountMap} {k C : Nat} {R : List UInt256}
    (v : PoolManagerImmutables) (zeroForOne : Bool) (hstack : R.length+34 ≤ 1024)
    (hp : price.toNat < 2^160) (ht : target.toNat < 2^160) (hl : liquidity.toNat < 2^128) (hf : fee.toNat < 2^24)
    (h : RD (deployedRuntime v) I g s0 ⟨19593⟩
      ([price, j, if zeroForOne then ⟨1⟩ else ⟨0⟩, target, fee, liquidity,
        remaining, x1, x2, x3, x4, fee, x6, x7, x8, j] ++ R) mem aw rdata σ k C) :
    (swapStepInputFits price target liquidity remaining fee zeroForOne → ∃ k' C', C ≤ C' ∧
      RD (deployedRuntime v) I g s0 ⟨19714⟩
        ([(swapStepInputWords price target liquidity remaining fee zeroForOne).fee, j, ⟨160⟩,
          (swapStepInputWords price target liquidity remaining fee zeroForOne).amountOut,
          (swapStepInputWords price target liquidity remaining fee zeroForOne).amountIn,
          (swapStepInputWords price target liquidity remaining fee zeroForOne).next, solcAddrMask,
          remaining, x1, x2, x3, x4, fee, x6, x7, x8, j] ++ R) mem aw rdata σ k' C') ∧
    (¬swapStepInputFits price target liquidity remaining fee zeroForOne → RDrev (deployedRuntime v) g s0) := by
  let available := swapStepAvailableWord remaining fee
  let desired := swapStepDeltaWord price target liquidity true zeroForOne
  have h0 := swapStepAvailableTrace v (by change R.length+26 ≤ 1024; omega) hf h
  by_cases h0fit : swapStepAvailableFits remaining fee
  · obtain ⟨k1, C1, hC1, rd1⟩ := h0.1 h0fit
    have h1 := swapStepInputDeltaTrace v zeroForOne (by change R.length+34 ≤ 1024; exact hstack) hp ht hl rd1
    by_cases h1fit : swapStepDeltaFits price target liquidity true zeroForOne
    · rw [if_pos h1fit] at h1
      obtain ⟨k2, C2, hC2, rd2⟩ := h1
      have h2 := swapStepInputSelectTrace v zeroForOne hstack hp hl hf rd2
      by_cases h2fit : swapStepInputSelectFits price liquidity available desired fee zeroForOne
      · obtain ⟨k3, C3, hC3, rd3⟩ := h2.1 h2fit
        have hnc : (swapStepSelectedPrice price target liquidity available desired true zeroForOne).toNat < 2^160 :=
          swapStepInputSelectedPrice_canonical (price := price) (target := target) (liquidity := liquidity)
            (available := available) (desired := desired) (fee := fee) hp ht h2fit
        have h3 := swapStepTailDeltaResultTrace (price := price)
          (next := swapStepSelectedPrice price target liquidity available desired true zeroForOne)
          v false zeroForOne (by change R.length+32 ≤ 1024; omega) hp hnc hl rd3
        constructor
        · intro hfit
          obtain ⟨k4, C4, hC4, rd4⟩ := h3.1 hfit.2.2.2
          exact ⟨k4, C4, by omega, rd4⟩
        · intro hfit
          exact h3.2 (fun hfinal => hfit ⟨h0fit, h1fit, h2fit, hfinal⟩)
      · constructor
        · intro hfit
          exact False.elim (h2fit hfit.2.2.1)
        · intro _
          exact h2.2 h2fit
    · rw [if_neg h1fit] at h1
      constructor
      · intro hfit
        exact False.elim (h1fit hfit.2.1)
      · intro _
        exact h1
  · constructor
    · intro hfit
      exact False.elim (h0fit hfit.1)
    · intro _
      exact h0.2 h0fit

end Benchmarks.UniswapV4PoolManager
