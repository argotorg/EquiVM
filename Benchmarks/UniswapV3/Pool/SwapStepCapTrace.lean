import Benchmarks.UniswapV3.Pool.SwapStepRecalcTraceModel
import Benchmarks.UniswapV3.Pool.SwapStepFinishModel
import Benchmarks.UniswapV3.Pool.RuntimeBlocks_043

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables Benchmarks.UniswapV3.Pool.Immutables
open uniswapV3PoolBlocks
namespace Benchmarks.UniswapV3.Pool
set_option maxRecDepth 10000

theorem swapStepCapGuardX {σ : AccountMap} {ee : ExecutionEnv} {g : Sat256}
    {s0 : EVM.State} {k C : Nat} {aw currentRaw targetRaw liquidityRaw feeRaw : UInt256}
    {mem rdata : ByteArray} {R : List UInt256} {v : UniswapV3PoolImmutables} (a : SwapStepArgs)
    (rd : RD (deployedRuntime v) ee g s0 ⟨12827⟩
      (swapStepCalcWords a currentRaw targetRaw liquidityRaw feeRaw
        (swapStepAmount a true) (swapStepAmount a false) ++ R) mem aw rdata σ k C)
    (hov : R.length + 15 ≤ 1024) :
    ∃ k' C', RD (deployedRuntime v) ee g s0 ⟨12843⟩
      ((swapStepCap a).toUInt256 :: swapStepCalcWords a currentRaw targetRaw liquidityRaw feeRaw
        (swapStepAmount a true) (swapStepAmount a false) ++ R) mem aw rdata σ k' C' := by
  cases hi : swapStepExactIn a
  · have r1 := uniswapV3Pool_block_12827_fallthrough (immWords := wordsOf (immStore v))
      (by change R.length + 10 + 5 ≤ 1024; omega) (by simp only [hi]; rfl) rd
    have r2 := uniswapV3Pool_block_12836 (immWords := wordsOf (immStore v))
      (by change R.length + 3 + 11 ≤ 1024; omega) r1
    have hg : UInt256.gt (swapStepAmount a false)
        (UInt256.sub (UInt256.ofNat 0) (EVM.wordOfInt a.remaining)) =
        (swapStepCap a).toUInt256 := by
      simp only [swapStepCap, swapStepAbsRemaining, hi, Bool.not_false, Bool.true_and]
      rfl
    simpa only [uniswapV3Pool_block_12836_stack, swapStepCalcWords, swapStepRawWords,
      List.cons_append, List.nil_append, hg] using RD.pack r2
  · have r1 := uniswapV3Pool_block_12827_taken (immWords := wordsOf (immStore v))
      (by change R.length + 10 + 5 ≤ 1024; omega) (by simp only [hi]; decide)
      (by rw [uniswapV3PoolPatchedValidJumpsRuntime v]; jump_dest) rd
    simpa only [uniswapV3Pool_block_12827_taken_stack, swapStepCap, hi, Bool.not_true,
      Bool.false_and, swapStepCalcWords, List.cons_append, List.nil_append] using RD.pack r1

theorem swapStepCapX {σ : AccountMap} {ee : ExecutionEnv} {g : Sat256}
    {s0 : EVM.State} {k C : Nat} {aw currentRaw targetRaw liquidityRaw feeRaw : UInt256}
    {mem rdata : ByteArray} {R : List UInt256} {v : UniswapV3PoolImmutables} (a : SwapStepArgs)
    (rd : RD (deployedRuntime v) ee g s0 ⟨12827⟩
      (swapStepCalcWords a currentRaw targetRaw liquidityRaw feeRaw
        (swapStepAmount a true) (swapStepAmount a false) ++ R) mem aw rdata σ k C)
    (hov : R.length + 15 ≤ 1024) :
    ∃ k' C', RD (deployedRuntime v) ee g s0 ⟨12855⟩
      (swapStepCalcWords a currentRaw targetRaw liquidityRaw feeRaw
        (swapStepAmount a true) (swapStepOutput a) ++ R) mem aw rdata σ k' C' := by
  obtain ⟨kg, Cg, rg⟩ := swapStepCapGuardX (v := v) a rd hov
  cases hh : swapStepCap a
  · simp only [hh] at rg
    have rr := uniswapV3Pool_block_12843_taken (immWords := wordsOf (immStore v))
      (by change R.length + 12 + 2 ≤ 1024; omega) (by decide)
      (by rw [uniswapV3PoolPatchedValidJumpsRuntime v]; jump_dest) rg
    simpa only [swapStepOutput, hh, Bool.false_eq_true, if_false] using RD.pack rr
  · simp only [hh] at rg
    have r1 := uniswapV3Pool_block_12843_fallthrough (immWords := wordsOf (immStore v))
      (by change R.length + 12 + 2 ≤ 1024; omega) rfl rg
    have r2 := uniswapV3Pool_block_12849 (immWords := wordsOf (immStore v))
      (by change R.length + 3 + 11 ≤ 1024; omega) r1
    simpa only [uniswapV3Pool_block_12849_stack, swapStepOutput, hh, if_true,
      swapStepCalcWords, swapStepRawWords, swapStepAbsRemaining,
      List.cons_append, List.nil_append] using RD.pack r2

end Benchmarks.UniswapV3.Pool
