import Benchmarks.UniswapV4PoolManager.SwapTargetStepTrace
import Benchmarks.UniswapV4PoolManager.PoolSwapComputeStoreTrace

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables
open Benchmarks.UniswapV4PoolManager.Immutables
namespace Benchmarks.UniswapV4PoolManager
set_option maxRecDepth 5000

def poolSwapComputeAW (aw step state params : UInt256) : UInt256 :=
  poolSwapComputeStoreAW (swapStepStartAW aw step ⟨96⟩ state params ⟨64⟩) step state params

theorem poolSwapComputeTrace {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem rdata : ByteArray}
    {aw next limit price liquidity step state params remaining x1 specified fee protocol amountToProtocol dir pool x3 x4 : UInt256}
    {σ : AccountMap} {k C : Nat} {R : List UInt256}
    (v : PoolManagerImmutables) (zeroForOne : Bool) (hstack : R.length+36 ≤ 1024)
    (hn : next.toNat < 2^160) (hlim : limit.toNat < 2^160) (hf : fee.toNat < 2^24)
    (hp : UInt256.land (memLoad state (swapStepStartMemory mem next step ⟨96⟩))
      (UInt256.ofNat 1461501637330902918203684832716283019655932542975) = price)
    (ht : UInt256.land (memLoad (params+UInt256.ofNat 96) (swapStepStartMemory mem next step ⟨96⟩))
      (UInt256.ofNat 1461501637330902918203684832716283019655932542975) = limit)
    (hl : UInt256.land (memLoad (state+UInt256.ofNat 64) (swapStepStartMemory mem next step ⟨96⟩))
      (UInt256.ofNat 340282366920938463463374607431768211455) = liquidity)
    (hs : memLoad params (poolSwapComputeStoreMemory (swapStepStartMemory mem next step ⟨96⟩) step state
      (swapStepWord price (swapTargetWord zeroForOne next limit) liquidity remaining fee)) = specified)
    (h : RD (deployedRuntime v) I g s0 ⟨19479⟩
      ([next, solcAddrMask, step, ⟨96⟩, ⟨1⟩, ⟨64⟩,
        UInt256.ofNat 340282366920938463463374607431768211455, state, fee,
        if zeroForOne then ⟨0⟩ else ⟨1⟩, remaining, x1, params, x3, x4, fee,
        protocol, amountToProtocol, dir, step, pool, state] ++ R)
      mem aw rdata σ k C) :
    (swapStepFits price (swapTargetWord zeroForOne next limit) liquidity remaining fee →
      ∃ k' C', C ≤ C' ∧ RD (deployedRuntime v) I g s0
        (if 0 < EVM.signed specified then ⟨19740⟩ else ⟨20320⟩)
        ([remaining, x1, params, x3, x4, fee, protocol, amountToProtocol, dir, step, pool, state] ++ R)
        (poolSwapComputeStoreMemory (swapStepStartMemory mem next step ⟨96⟩) step state
          (swapStepWord price (swapTargetWord zeroForOne next limit) liquidity remaining fee))
        (poolSwapComputeAW aw step state params) rdata σ k' C') ∧
    (¬swapStepFits price (swapTargetWord zeroForOne next limit) liquidity remaining fee → RDrev (deployedRuntime v) g s0) := by
  have hrun := swapTargetStepTrace (R := pool :: state :: R) v zeroForOne
    (by change R.length+2+34 ≤ 1024; omega) hn hlim hf hp ht hl h
  constructor
  · intro hfit
    obtain ⟨k1, C1, hC1, rd1⟩ := hrun.1 hfit
    have hpc : price.toNat < 2^160 := by
      rw [← hp]
      exact u256LandMaskToNatLtOfToNat _ (UInt256.ofNat 1461501637330902918203684832716283019655932542975) (bits := 160) rfl
    obtain ⟨C2, hC2, rd2⟩ := poolSwapComputeStoreTrace v (by omega)
      (swapStepWord_next_canonical hpc (swapTargetWord_canonical hn hlim) hfit) hs rd1
    exact ⟨_, _, by omega, rd2⟩
  · exact hrun.2

end Benchmarks.UniswapV4PoolManager
