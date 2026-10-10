import Benchmarks.UniswapV4PoolManager.SwapStepSelectWords
import Benchmarks.UniswapV4PoolManager.NextPriceOutputTrace

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables
open Benchmarks.UniswapV4PoolManager.Immutables
namespace Benchmarks.UniswapV4PoolManager
set_option maxRecDepth 5000

theorem swapStepOutputSelectTrace {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem rdata : ByteArray} {aw price target liquidity remaining desired j x1 x2 x3 x4 x5 x6 x7 x8 : UInt256}
    {σ : AccountMap} {k C : Nat} {R : List UInt256}
    (v : PoolManagerImmutables) (zeroForOne : Bool) (hstack : R.length+33 ≤ 1024)
    (hp : price.toNat < 2^160) (hl : liquidity.toNat < 2^128)
    (h : RD (deployedRuntime v) I g s0 ⟨20631⟩
      ([target, price, desired, j, if zeroForOne then ⟨1⟩ else ⟨0⟩, liquidity,
        remaining, x1, x2, x3, x4, x5, x6, x7, x8, j] ++ R) mem aw rdata σ k C) :
    (swapStepOutputSelectFits price liquidity remaining desired zeroForOne → ∃ k' C', C ≤ C' ∧
      RD (deployedRuntime v) I g s0 ⟨20667⟩
        ([if zeroForOne then ⟨1⟩ else ⟨0⟩, swapStepSelectedPrice price target liquidity remaining desired false zeroForOne,
          liquidity, price, ⟨160⟩, swapStepSelectedAmount remaining desired, j,
          swapStepSelectedPrice price target liquidity remaining desired false zeroForOne,
          solcAddrMask, remaining, x1, x2, x3, x4, x5, x6, x7, x8, j] ++ R) mem aw rdata σ k' C') ∧
    (¬swapStepOutputSelectFits price liquidity remaining desired zeroForOne → RDrev (deployedRuntime v) g s0) := by
  by_cases ht : swapStepReachesTarget remaining desired
  · have rd1 := poolManagerBlocks.poolManager_block_20631_fallthrough
      (by change R.length+18 ≤ 1024; omega) (ult_zero ht) h
    have rd2 := poolManagerBlocks.poolManager_block_20639
      (by change R.length+19 ≤ 1024; omega) rd1
    simp only [poolManagerBlocks.poolManager_block_20639_stack] at rd2
    constructor
    · intro _
      refine ⟨k+6+7, C+23+21, by omega, ?_⟩
      simpa only [swapStepSelectedPrice, swapStepSelectedAmount, if_pos ht] using rd2
    · intro hfit
      exact False.elim (hfit (by simp only [swapStepOutputSelectFits, if_pos ht]))
  · have hlt : remaining.toNat < desired.toNat := Nat.lt_of_not_ge ht
    have rd1 := poolManagerBlocks.poolManager_block_20631_taken
      (by change R.length+18 ≤ 1024; omega) (by rw [ult_one hlt]; decide)
      (by rw [poolManagerPatchedValidJumpsRuntime v]; jump_dest) h
    have hr := nextPriceOutputTrace v zeroForOne hstack hp hl rd1
    constructor
    · intro hfit
      simp only [swapStepOutputSelectFits, if_neg ht] at hfit
      rw [if_pos hfit] at hr
      obtain ⟨k2, C2, hC2, rd2⟩ := hr
      have rd3 := poolManagerBlocks.poolManager_block_20872
        (by change R.length+20 ≤ 1024; omega)
        (by rw [poolManagerPatchedValidJumpsRuntime v]; jump_dest) rd2
      simp only [poolManagerBlocks.poolManager_block_20872_stack] at rd3
      refine ⟨k2+5, C2+18, by omega, ?_⟩
      simpa only [swapStepSelectedPrice, swapStepSelectedAmount, if_neg ht] using rd3
    · intro hfit
      have hn : ¬nextPriceFits price liquidity remaining false zeroForOne := by
        simpa only [swapStepOutputSelectFits, if_neg ht] using hfit
      rwa [if_neg hn] at hr

end Benchmarks.UniswapV4PoolManager
