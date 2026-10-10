import Benchmarks.UniswapV3.Pool.Amount0DeltaRawTrace
import Benchmarks.UniswapV3.Pool.Amount0DeltaWords
import Benchmarks.UniswapV3.Pool.FullMathRoundTrace
import Benchmarks.UniswapV3.Pool.UnsafeDivRoundTrace
import Benchmarks.UniswapV3.Pool.RuntimeBlocks_061

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables Benchmarks.UniswapV3.Pool.Immutables
open uniswapV3PoolBlocks
namespace Benchmarks.UniswapV3.Pool
set_option maxRecDepth 10000

def amount0DeltaComputeWords (a : AmountDeltaArgs) : List UInt256 :=
  [amountDeltaDifference a, amountDeltaNumerator a, ⟨0⟩, a.roundUp.toUInt256,
    a.liquidity, amountDeltaUpper a, amountDeltaLower a]

theorem amount0DeltaComputeX {σ : AccountMap} {ee : ExecutionEnv} {g : Sat256}
    {s0 : EVM.State} {k C : Nat} {aw ret : UInt256} {mem rdata : ByteArray}
    {R : List UInt256} {v : UniswapV3PoolImmutables} (a : AmountDeltaArgs)
    (rd : RD (deployedRuntime v) ee g s0 ⟨18217⟩
      (amount0DeltaComputeWords a ++ ret :: R) mem aw rdata σ k C)
    (hfit : a.Fits) (hv : amountDeltaValid false a)
    (hret : (D_J (deployedRuntime v) 0).contains ret = true) (hov : R.length + 30 ≤ 1024) :
    ∃ k' C', RD (deployedRuntime v) ee g s0 ret
      (amountDeltaResult false a :: R) mem aw rdata σ k' C' := by
  have hs := amountDeltaSort a hfit
  exact amount0DeltaRawComputeX (v := v) a a.liquidity (amountDeltaUpper a) (amountDeltaLower a)
    rd (u256LandMaskCleanOfToNat (bits := 160) _ _ (by decide) hs.2.2)
    (u256LandMaskCleanOfToNat (bits := 160) _ _ (by decide) hs.2.1) hfit hv hret hov

theorem amount0DeltaX {σ : AccountMap} {ee : ExecutionEnv} {g : Sat256}
    {s0 : EVM.State} {k C : Nat} {aw ret : UInt256} {mem rdata : ByteArray}
    {R : List UInt256} {v : UniswapV3PoolImmutables} (a : AmountDeltaArgs)
    (rd : RD (deployedRuntime v) ee g s0 ⟨18125⟩
      (amountDeltaEntryWords a ++ ret :: R) mem aw rdata σ k C)
    (hfit : a.Fits) (hret : (D_J (deployedRuntime v) 0).contains ret = true)
    (hov : R.length + 30 ≤ 1024) :
    (¬amountDeltaValid false a ∧ RDrev (deployedRuntime v) g s0) ∨
      (amountDeltaValid false a ∧ ∃ k' C', RD (deployedRuntime v) ee g s0 ret
        (amountDeltaResult false a :: R) mem aw rdata σ k' C') := by
  exact amount0DeltaRawX (v := v) a a.sqrtA a.sqrtB a.liquidity rd hfit
    (u256LandMaskCleanOfToNat (bits := 160) _ _ (by decide) hfit.1)
    (u256LandMaskCleanOfToNat (bits := 160) _ _ (by decide) hfit.2.1)
    (u256LandMaskCleanOfToNat (bits := 128) _ _ (by decide) hfit.2.2) hret hov

end Benchmarks.UniswapV3.Pool
