import Benchmarks.UniswapV4PoolManager.PoolSwapAmountSource
import Benchmarks.UniswapV4PoolManager.PoolSwapInputAmountTrace
import Benchmarks.UniswapV4PoolManager.PoolSwapOutputAmountTrace

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Benchmarks.UniswapV4PoolManager.Immutables
namespace Benchmarks.UniswapV4PoolManager
set_option maxRecDepth 5000

def poolSwapAmountAW (aw step specified : UInt256) : UInt256 :=
  if 0 < EVM.signed specified then
    M (M (M aw (step+UInt256.ofNat 160) ⟨32⟩) (step+UInt256.ofNat 128) ⟨32⟩) (step+UInt256.ofNat 192) ⟨32⟩
  else M (M (M aw (step+UInt256.ofNat 128) ⟨32⟩) (step+UInt256.ofNat 192) ⟨32⟩) (step+UInt256.ofNat 160) ⟨32⟩

theorem poolSwapAmountTrace {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem rdata : ByteArray} {s : PoolSwapStepWords}
    {aw specified remaining calculated step x1 params tag fee protocol amountToProtocol dir : UInt256}
    {σ : AccountMap} {k C : Nat} {R : List UInt256}
    (v : PoolManagerImmutables) (hstack : R.length+15 ≤ 1024)
    (hi : memLoad (step+UInt256.ofNat 128) mem = s.amountIn)
    (ho : memLoad (step+UInt256.ofNat 160) mem = s.amountOut)
    (hf : memLoad (step+UInt256.ofNat 192) mem = s.feeAmount)
    (h : RD (deployedRuntime v) I g s0 (if 0 < EVM.signed specified then ⟨19740⟩ else ⟨20320⟩)
      ([remaining, x1, params, calculated, tag, fee, protocol, amountToProtocol, dir, step] ++ R) mem aw rdata σ k C) :
    if poolSwapAmountFits s specified calculated then ∃ k' C', C ≤ C' ∧
      RD (deployedRuntime v) I g s0 ⟨19794⟩
        ([tag, x1, params, poolSwapRemainingAfter s specified remaining, poolSwapCalculatedAfter s specified calculated,
          fee, protocol, amountToProtocol, dir, step] ++ R)
        mem (poolSwapAmountAW aw step specified) rdata σ k' C'
    else RDrev (deployedRuntime v) g s0 := by
  by_cases hpos : 0 < EVM.signed specified
  · rw [if_pos hpos] at h
    simpa only [poolSwapAmountFits, poolSwapRemainingAfter, poolSwapCalculatedAfter, poolSwapAmountAW, if_pos hpos] using
      poolSwapOutputAmountTrace v (by omega) hi ho hf h
  · rw [if_neg hpos] at h
    simpa only [poolSwapAmountFits, poolSwapRemainingAfter, poolSwapCalculatedAfter, poolSwapAmountAW, if_neg hpos] using
      poolSwapInputAmountTrace v hstack hi ho hf h

end Benchmarks.UniswapV4PoolManager
