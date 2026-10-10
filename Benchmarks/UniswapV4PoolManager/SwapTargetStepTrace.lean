import Benchmarks.UniswapV4PoolManager.SwapStepStartTrace
import Benchmarks.UniswapV4PoolManager.SwapStepTrace

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables
open Benchmarks.UniswapV4PoolManager.Immutables
namespace Benchmarks.UniswapV4PoolManager
set_option maxRecDepth 5000

theorem swapTargetStepTrace {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem rdata : ByteArray}
    {aw next limit price liquidity writeBase writeOffset liquidityOffset pricePtr paramsPtr fee remaining j x1 x3 x4 x6 x7 x8 : UInt256}
    {σ : AccountMap} {k C : Nat} {R : List UInt256}
    (v : PoolManagerImmutables) (zeroForOne : Bool) (hstack : R.length+34 ≤ 1024)
    (hn : next.toNat < 2^160) (hlim : limit.toNat < 2^160) (hf : fee.toNat < 2^24)
    (hp : UInt256.land (memLoad pricePtr (swapStepStartMemory mem next writeBase writeOffset))
      (UInt256.ofNat 1461501637330902918203684832716283019655932542975) = price)
    (ht : UInt256.land (memLoad (paramsPtr+UInt256.ofNat 96) (swapStepStartMemory mem next writeBase writeOffset))
      (UInt256.ofNat 1461501637330902918203684832716283019655932542975) = limit)
    (hl : UInt256.land (memLoad (pricePtr+liquidityOffset) (swapStepStartMemory mem next writeBase writeOffset))
      (UInt256.ofNat 340282366920938463463374607431768211455) = liquidity)
    (h : RD (deployedRuntime v) I g s0 ⟨19479⟩
      ([next, solcAddrMask, writeBase, writeOffset, ⟨1⟩, liquidityOffset,
        UInt256.ofNat 340282366920938463463374607431768211455, pricePtr, fee,
        if zeroForOne then ⟨0⟩ else ⟨1⟩, remaining, x1, paramsPtr, x3, x4, fee, x6, x7, x8, j] ++ R)
      mem aw rdata σ k C) :
    (swapStepFits price (swapTargetWord zeroForOne next limit) liquidity remaining fee → ∃ k' C', C ≤ C' ∧
      RD (deployedRuntime v) I g s0 ⟨19714⟩
        ([(swapStepWord price (swapTargetWord zeroForOne next limit) liquidity remaining fee).fee, j, ⟨160⟩,
          (swapStepWord price (swapTargetWord zeroForOne next limit) liquidity remaining fee).amountOut,
          (swapStepWord price (swapTargetWord zeroForOne next limit) liquidity remaining fee).amountIn,
          (swapStepWord price (swapTargetWord zeroForOne next limit) liquidity remaining fee).next, solcAddrMask,
          remaining, x1, paramsPtr, x3, x4, fee, x6, x7, x8, j] ++ R)
        (swapStepStartMemory mem next writeBase writeOffset)
        (swapStepStartAW aw writeBase writeOffset pricePtr paramsPtr liquidityOffset) rdata σ k' C') ∧
    (¬swapStepFits price (swapTargetWord zeroForOne next limit) liquidity remaining fee → RDrev (deployedRuntime v) g s0) := by
  obtain ⟨k1, C1, hC1, rd1⟩ := swapStepStartTrace v zeroForOne (by omega) hn hlim hp ht hl h
  have hpc : price.toNat < 2^160 := by
    rw [← hp]
    exact u256LandMaskToNatLtOfToNat _ (UInt256.ofNat 1461501637330902918203684832716283019655932542975) (bits := 160) rfl
  have hlc : liquidity.toNat < 2^128 := by
    rw [← hl]
    exact u256LandMaskToNatLtOfToNat _ (UInt256.ofNat 340282366920938463463374607431768211455) (bits := 128) rfl
  have hr := swapStepTrace (target := swapTargetWord zeroForOne next limit) v hstack hpc
    (swapTargetWord_canonical hn hlim) hlc hf rd1
  constructor
  · intro hfit
    obtain ⟨k2, C2, hC2, rd2⟩ := hr.1 hfit
    exact ⟨k2, C2, by omega, rd2⟩
  · exact hr.2

end Benchmarks.UniswapV4PoolManager
