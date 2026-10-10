import Benchmarks.UniswapV3.Pool.SwapStepRecalcTraceModel
import Benchmarks.UniswapV3.Pool.RuntimeBlocks_041

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables Benchmarks.UniswapV3.Pool.Immutables
open uniswapV3PoolBlocks
namespace Benchmarks.UniswapV3.Pool
set_option maxRecDepth 10000

theorem swapStepMaxX {σ : AccountMap} {ee : ExecutionEnv} {g : Sat256}
    {s0 : EVM.State} {k C : Nat} {aw currentRaw targetRaw liquidityRaw feeRaw : UInt256}
    {mem rdata : ByteArray} {R : List UInt256} {v : UniswapV3PoolImmutables} (a : SwapStepArgs)
    (rd : RD (deployedRuntime v) ee g s0 ⟨12654⟩
      (swapStepPriceWords a currentRaw targetRaw liquidityRaw feeRaw ++ R) mem aw rdata σ k C)
    (hc : UInt256.land currentRaw (UInt256.ofNat (2 ^ 160 - 1)) = a.current)
    (ht : UInt256.land targetRaw (UInt256.ofNat (2 ^ 160 - 1)) = a.target)
    (ha : a.Fits) (hv : swapStepPriceValid a) (hov : R.length + 14 ≤ 1024) :
    ∃ k' C', RD (deployedRuntime v) ee g s0 (swapStepRecalcEntry (swapStepZeroForOne a))
      (swapStepCalcWords a currentRaw targetRaw liquidityRaw feeRaw
        (swapStepBeforeAmount a true) (swapStepBeforeAmount a false) ++ R)
      mem aw rdata σ k' C' := by
  have hp := swapStepRawPrice_clean a currentRaw targetRaw hc ht ha hv.2.2
  have ht' : UInt256.land (UInt256.ofNat (2 ^ 160 - 1)) targetRaw = a.target := by
    rw [u256_land_comm, ht]
  simp only [swapStepPriceWords, swapStepRawWords, List.cons_append, List.nil_append] at rd
  cases hz : swapStepZeroForOne a
  · simp only [hz] at rd
    have rr := uniswapV3Pool_block_12654_taken (immWords := wordsOf (immStore v))
      (by evm_ov) (by decide)
      (by rw [uniswapV3PoolPatchedValidJumpsRuntime v]; jump_dest) rd
    have packed := RD.pack rr
    simpa only [swapStepRecalcEntry, swapStepCalcWords, swapStepRawWords,
      uniswapV3Pool_block_12654_taken_stack, amountDeltaMask160, hp, ht', swapStepMaxWord,
      hz, Bool.false_eq_true, if_false, List.cons_append, List.nil_append] using packed
  · simp only [hz] at rd
    have rr := uniswapV3Pool_block_12654_fallthrough (immWords := wordsOf (immStore v))
      (by evm_ov) rfl rd
    have packed := RD.pack rr
    simpa only [swapStepRecalcEntry, swapStepCalcWords, swapStepRawWords,
      uniswapV3Pool_block_12654_fallthrough_stack, amountDeltaMask160, hp, ht', swapStepMaxWord,
      hz, if_true, List.cons_append, List.nil_append] using packed

end Benchmarks.UniswapV3.Pool
