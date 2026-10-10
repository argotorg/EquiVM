import Benchmarks.UniswapV4PoolManager.SwapStepOutputSelectTrace
import Benchmarks.UniswapV4PoolManager.SwapStepOutputDeltaTrace
import Benchmarks.UniswapV4PoolManager.SwapStepTailDeltaResultTrace
import Benchmarks.UniswapV4PoolManager.SwapStepFeeTrace
import Benchmarks.UniswapV4PoolManager.SwapStepWords

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables
open Benchmarks.UniswapV4PoolManager.Immutables
namespace Benchmarks.UniswapV4PoolManager
set_option maxRecDepth 5000

theorem swapStepOutputTrace {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem rdata : ByteArray} {aw price target liquidity fee remaining j x1 x2 x3 x4 x6 x7 x8 : UInt256}
    {σ : AccountMap} {k C : Nat} {R : List UInt256}
    (v : PoolManagerImmutables) (zeroForOne : Bool) (hstack : R.length+33 ≤ 1024)
    (hp : price.toNat < 2^160) (ht : target.toNat < 2^160) (hl : liquidity.toNat < 2^128) (hf : fee.toNat < 2^24)
    (h : RD (deployedRuntime v) I g s0 ⟨20607⟩
      ([price, j, if zeroForOne then ⟨1⟩ else ⟨0⟩, target, fee, liquidity,
        remaining, x1, x2, x3, x4, fee, x6, x7, x8, j] ++ R) mem aw rdata σ k C) :
    (swapStepOutputFits price target liquidity remaining fee zeroForOne → ∃ k' C', C ≤ C' ∧
      RD (deployedRuntime v) I g s0 ⟨19714⟩
        ([(swapStepOutputWords price target liquidity remaining fee zeroForOne).fee, j, ⟨160⟩,
          (swapStepOutputWords price target liquidity remaining fee zeroForOne).amountOut,
          (swapStepOutputWords price target liquidity remaining fee zeroForOne).amountIn,
          (swapStepOutputWords price target liquidity remaining fee zeroForOne).next, solcAddrMask,
          remaining, x1, x2, x3, x4, fee, x6, x7, x8, j] ++ R) mem aw rdata σ k' C') ∧
    (¬swapStepOutputFits price target liquidity remaining fee zeroForOne → RDrev (deployedRuntime v) g s0) := by
  let desired := swapStepDeltaWord price target liquidity false zeroForOne
  have h0 := swapStepOutputDeltaTrace v zeroForOne (by change R.length+31 ≤ 1024; omega) hp ht hl h
  by_cases h0fit : swapStepDeltaFits price target liquidity false zeroForOne
  · rw [if_pos h0fit] at h0
    obtain ⟨k1, C1, hC1, rd1⟩ := h0
    have h1 := swapStepOutputSelectTrace v zeroForOne hstack hp hl rd1
    by_cases h1fit : swapStepOutputSelectFits price liquidity remaining desired zeroForOne
    · obtain ⟨k2, C2, hC2, rd2⟩ := h1.1 h1fit
      have hnc : (swapStepSelectedPrice price target liquidity remaining desired false zeroForOne).toNat < 2^160 :=
        swapStepOutputSelectedPrice_canonical (price := price) (target := target) (liquidity := liquidity)
          (remaining := remaining) (desired := desired) hp ht h1fit
      have h2 := swapStepTailDeltaResultTrace (price := price)
        (next := swapStepSelectedPrice price target liquidity remaining desired false zeroForOne)
        v true zeroForOne (by change R.length+31 ≤ 1024; omega) hp hnc hl rd2
      by_cases h2fit : swapStepDeltaFits price
          (swapStepSelectedPrice price target liquidity remaining desired false zeroForOne) liquidity true zeroForOne
      · obtain ⟨k3, C3, hC3, rd3⟩ := h2.1 h2fit
        have h3 := swapStepOutputFeeTrace v (by change R.length+30 ≤ 1024; omega) hf rd3
        constructor
        · intro hfit
          obtain ⟨k4, C4, hC4, rd4⟩ := h3.1 hfit.2.2.2
          refine ⟨k4, C4, by omega, ?_⟩
          simpa only [swapStepOutputWords, desired] using rd4
        · intro hfit
          exact h3.2 (fun hfinal => hfit ⟨h0fit, h1fit, h2fit, hfinal⟩)
      · constructor
        · intro hfit
          exact False.elim (h2fit hfit.2.2.1)
        · intro _
          exact h2.2 h2fit
    · constructor
      · intro hfit
        exact False.elim (h1fit hfit.2.1)
      · intro _
        exact h1.2 h1fit
  · rw [if_neg h0fit] at h0
    constructor
    · intro hfit
      exact False.elim (h0fit hfit.1)
    · intro _
      exact h0

end Benchmarks.UniswapV4PoolManager
