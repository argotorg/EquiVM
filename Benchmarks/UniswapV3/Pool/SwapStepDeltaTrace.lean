import Benchmarks.UniswapV3.Pool.SwapStepModel
import Benchmarks.UniswapV3.Pool.AmountDeltaRawRoutines

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables Benchmarks.UniswapV3.Pool.Immutables
namespace Benchmarks.UniswapV3.Pool
set_option maxRecDepth 1000

def swapStepDeltaRawWords (a : SwapStepArgs) (input : Bool)
    (currentRaw priceRaw liquidityRaw : UInt256) : List UInt256 :=
  [input.toUInt256, liquidityRaw,
   if swapStepZeroForOne a then currentRaw else priceRaw,
   if swapStepZeroForOne a then priceRaw else currentRaw]

theorem swapStepDeltaX {σ : AccountMap} {ee : ExecutionEnv} {g : Sat256}
    {s0 : EVM.State} {k C : Nat} {aw ret : UInt256} {mem rdata : ByteArray}
    {R : List UInt256} {v : UniswapV3PoolImmutables} (a : SwapStepArgs)
    (price : UInt256) (input : Bool) (currentRaw priceRaw liquidityRaw : UInt256)
    (rd : RD (deployedRuntime v) ee g s0
      (UInt256.ofNat (amountDeltaEntry (swapStepDeltaOne a input)))
      (swapStepDeltaRawWords a input currentRaw priceRaw liquidityRaw ++ ret :: R)
      mem aw rdata σ k C)
    (hc : UInt256.land currentRaw (UInt256.ofNat (2 ^ 160 - 1)) = a.current)
    (hp : UInt256.land priceRaw (UInt256.ofNat (2 ^ 160 - 1)) = price)
    (hl : UInt256.land liquidityRaw (UInt256.ofNat (2 ^ 128 - 1)) = a.liquidity)
    (ha : a.Fits) (hprice : price.toNat < 2 ^ 160)
    (hret : (D_J (deployedRuntime v) 0).contains ret = true) (hov : R.length + 30 ≤ 1024) :
    (¬amountDeltaValid (swapStepDeltaOne a input) (swapStepDeltaArgs a price input) ∧
      RDrev (deployedRuntime v) g s0) ∨
    (amountDeltaValid (swapStepDeltaOne a input) (swapStepDeltaArgs a price input) ∧
      ∃ k' C', RD (deployedRuntime v) ee g s0 ret
        (amountDeltaResult (swapStepDeltaOne a input) (swapStepDeltaArgs a price input) :: R)
        mem aw rdata σ k' C') := by
  have hA : UInt256.land (if swapStepZeroForOne a then priceRaw else currentRaw)
      (UInt256.ofNat (2 ^ 160 - 1)) = (swapStepDeltaArgs a price input).sqrtA := by
    cases hz : swapStepZeroForOne a <;>
      simp only [swapStepDeltaArgs, hz, Bool.false_eq_true, if_false, if_true, hp, hc]
  have hB : UInt256.land (if swapStepZeroForOne a then currentRaw else priceRaw)
      (UInt256.ofNat (2 ^ 160 - 1)) = (swapStepDeltaArgs a price input).sqrtB := by
    cases hz : swapStepZeroForOne a <;>
      simp only [swapStepDeltaArgs, hz, Bool.false_eq_true, if_false, if_true, hp, hc]
  exact amountDeltaRawX (v := v) (swapStepDeltaOne a input) (swapStepDeltaArgs a price input)
    _ _ liquidityRaw rd (swapStepDeltaArgs_fits a price input ha hprice) hA hB hl hret hov

end Benchmarks.UniswapV3.Pool
