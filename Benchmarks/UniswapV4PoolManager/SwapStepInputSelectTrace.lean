import Benchmarks.UniswapV4PoolManager.SwapStepSelectWords
import Benchmarks.UniswapV4PoolManager.SwapStepTargetFeeTrace
import Benchmarks.UniswapV4PoolManager.SwapStepRemainingTrace
import Benchmarks.UniswapV4PoolManager.NextPriceInputTrace

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables
open Benchmarks.UniswapV4PoolManager.Immutables
namespace Benchmarks.UniswapV4PoolManager
set_option maxRecDepth 5000

theorem swapStepInputSelectTrace {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem rdata : ByteArray} {aw price target liquidity available desired fee remaining j x1 x2 x3 x4 x5 x6 x7 x8 : UInt256}
    {σ : AccountMap} {k C : Nat} {R : List UInt256}
    (v : PoolManagerImmutables) (zeroForOne : Bool) (hstack : R.length+34 ≤ 1024)
    (hp : price.toNat < 2^160) (hl : liquidity.toNat < 2^128) (hf : fee.toNat < 2^24)
    (h : RD (deployedRuntime v) I g s0 ⟨19635⟩
      ([available, target, swapStepFeeComplement fee, price, j, if zeroForOne then ⟨1⟩ else ⟨0⟩,
        desired, fee, liquidity, remaining, x1, x2, x3, x4, x5, x6, x7, x8, j] ++ R) mem aw rdata σ k C) :
    (swapStepInputSelectFits price liquidity available desired fee zeroForOne → ∃ k' C', C ≤ C' ∧
      RD (deployedRuntime v) I g s0 ⟨19697⟩
        ([if zeroForOne then ⟨1⟩ else ⟨0⟩, swapStepSelectedPrice price target liquidity available desired true zeroForOne,
          liquidity, price, j, ⟨160⟩, swapStepSelectedFee remaining available desired fee,
          swapStepSelectedAmount available desired, swapStepSelectedPrice price target liquidity available desired true zeroForOne,
          solcAddrMask, remaining, x1, x2, x3, x4, x5, x6, x7, x8, j] ++ R) mem aw rdata σ k' C') ∧
    (¬swapStepInputSelectFits price liquidity available desired fee zeroForOne → RDrev (deployedRuntime v) g s0) := by
  by_cases ht : swapStepReachesTarget available desired
  · have rd1 := poolManagerBlocks.poolManager_block_19635_fallthrough
      (by change R.length+21 ≤ 1024; omega) (ult_zero ht) h
    have hr := swapStepTargetFeeTrace v (by change R.length+33 ≤ 1024; omega) hf rd1
    constructor
    · intro hfit
      simp only [swapStepInputSelectFits, if_pos ht] at hfit
      obtain ⟨k2, C2, hC2, rd2⟩ := hr.1 hfit
      refine ⟨k2, C2, by omega, ?_⟩
      simpa only [swapStepSelectedPrice, swapStepSelectedFee, swapStepSelectedAmount, if_pos ht] using rd2
    · intro hfit
      apply hr.2
      simpa only [swapStepInputSelectFits, if_pos ht] using hfit
  · have hlt : available.toNat < desired.toNat := Nat.lt_of_not_ge ht
    have rd1 := poolManagerBlocks.poolManager_block_19635_taken
      (by change R.length+21 ≤ 1024; omega) (by rw [ult_one hlt]; decide)
      (by rw [poolManagerPatchedValidJumpsRuntime v]; jump_dest) h
    have hr := nextPriceInputTrace v zeroForOne hstack hp hl rd1
    constructor
    · intro hfit
      simp only [swapStepInputSelectFits, if_neg ht] at hfit
      rw [if_pos hfit] at hr
      obtain ⟨k2, C2, hC2, rd2⟩ := hr
      obtain ⟨k3, C3, hC3, rd3⟩ := swapStepRemainingFeeTrace v
        (by change R.length+21 ≤ 1024; omega) rd2
      refine ⟨k3, C3, by omega, ?_⟩
      simpa only [swapStepSelectedPrice, swapStepSelectedFee, swapStepSelectedAmount, if_neg ht] using rd3
    · intro hfit
      have hn : ¬nextPriceFits price liquidity available true zeroForOne := by
        simpa only [swapStepInputSelectFits, if_neg ht] using hfit
      rwa [if_neg hn] at hr

end Benchmarks.UniswapV4PoolManager
