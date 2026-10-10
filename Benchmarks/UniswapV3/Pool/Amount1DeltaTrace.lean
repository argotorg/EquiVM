import Benchmarks.UniswapV3.Pool.Amount1DeltaRawTrace
import Benchmarks.UniswapV3.Pool.AmountDeltaSortTrace
import Benchmarks.UniswapV3.Pool.FullMathRoundTrace

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables Benchmarks.UniswapV3.Pool.Immutables
open uniswapV3PoolBlocks
namespace Benchmarks.UniswapV3.Pool
set_option maxRecDepth 10000

theorem amount1DeltaComputeX {σ : AccountMap} {ee : ExecutionEnv} {g : Sat256}
    {s0 : EVM.State} {k C : Nat} {aw ret : UInt256} {mem rdata : ByteArray}
    {R : List UInt256} {v : UniswapV3PoolImmutables} (a : AmountDeltaArgs)
    (rd : RD (deployedRuntime v) ee g s0 ⟨18034⟩
      (amountDeltaSortedWords a ++ ret :: R) mem aw rdata σ k C)
    (hfit : a.Fits) (hret : (D_J (deployedRuntime v) 0).contains ret = true)
    (hov : R.length + 27 ≤ 1024) :
    ∃ k' C', RD (deployedRuntime v) ee g s0 ret
      (amountDeltaResult true a :: R) mem aw rdata σ k' C' := by
  have hs := amountDeltaSort a hfit
  exact amount1DeltaRawComputeX (v := v) a a.liquidity (amountDeltaUpper a) (amountDeltaLower a)
    rd hfit
    (u256LandMaskCleanOfToNat (bits := 128) _ _ (by decide) hfit.2.2)
    (u256LandMaskCleanOfToNat (bits := 160) _ _ (by decide) hs.2.2)
    (u256LandMaskCleanOfToNat (bits := 160) _ _ (by decide) hs.2.1) hret hov

theorem amount1DeltaX {σ : AccountMap} {ee : ExecutionEnv} {g : Sat256}
    {s0 : EVM.State} {k C : Nat} {aw ret : UInt256} {mem rdata : ByteArray}
    {R : List UInt256} {v : UniswapV3PoolImmutables} (a : AmountDeltaArgs)
    (rd : RD (deployedRuntime v) ee g s0 ⟨18002⟩
      (amountDeltaEntryWords a ++ ret :: R) mem aw rdata σ k C)
    (hfit : a.Fits) (hret : (D_J (deployedRuntime v) 0).contains ret = true)
    (hov : R.length + 27 ≤ 1024) :
    ∃ k' C', RD (deployedRuntime v) ee g s0 ret
      (amountDeltaResult true a :: R) mem aw rdata σ k' C' := by
  exact amount1DeltaRawX (v := v) a a.sqrtA a.sqrtB a.liquidity rd hfit
    (u256LandMaskCleanOfToNat (bits := 160) _ _ (by decide) hfit.1)
    (u256LandMaskCleanOfToNat (bits := 160) _ _ (by decide) hfit.2.1)
    (u256LandMaskCleanOfToNat (bits := 128) _ _ (by decide) hfit.2.2) hret hov

end Benchmarks.UniswapV3.Pool
