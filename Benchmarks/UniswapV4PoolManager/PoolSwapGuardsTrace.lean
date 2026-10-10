import Benchmarks.UniswapV4PoolManager.PoolSwapModeTrace
import Benchmarks.UniswapV4PoolManager.PoolSwapZeroTrace
import Benchmarks.UniswapV4PoolManager.PoolSwapLimitTrace

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Benchmarks.UniswapV4PoolManager.Immutables
namespace Benchmarks.UniswapV4PoolManager
set_option maxRecDepth 5000

def poolSwapZeroAW (aw fee params : UInt256) : UInt256 := M (poolSwapModeAW aw fee params) params ⟨32⟩
def poolSwapGuardsAW (aw fee params : UInt256) : UInt256 := poolSwapLimitAW (poolSwapZeroAW aw fee params) params

theorem poolSwapGuardsTrace {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem rdata : ByteArray} {aw packed pool state ret params fee protocol : UInt256} {p : PoolSwapParamsWords}
    {σ : AccountMap} {k C : Nat} {R : List UInt256}
    (v : PoolManagerImmutables) (hstack : R.length+17 ≤ 1024)
    (hf : fee.toNat < 2^24) (hl : p.priceLimit.toNat < 2^160)
    (hs : memLoad params mem = p.amountSpecified) (hm : memLoad (params+UInt256.ofNat 96) mem = p.priceLimit)
    (hret : (D_J (deployedRuntime v) 0).contains ret = true)
    (h : RD (deployedRuntime v) I g s0 ⟨18951⟩
      ([fee, slot0SqrtPriceWord packed, ret, params, p.amountSpecified, ⟨0⟩, state, protocol, ⟨0⟩,
        UInt256.fromBool (!p.zeroForOne), packed, pool, state]++R) mem aw rdata σ k C) :
    if poolSwapModeValid fee p.amountSpecified then
      if p.amountSpecified = ⟨0⟩ then
        ∃ k' C', C ≤ C' ∧ RD (deployedRuntime v) I g s0 ret ([state, fee, ⟨0⟩, ⟨0⟩]++R)
          mem (poolSwapZeroAW aw fee params) rdata σ k' C'
      else if poolSwapLimitValid packed p.priceLimit p.zeroForOne then
        ∃ k' C', C ≤ C' ∧ RD (deployedRuntime v) I g s0 ⟨19061⟩
          ([ret, params, p.amountSpecified, ⟨0⟩, fee, protocol, ⟨0⟩, UInt256.fromBool (!p.zeroForOne),
            packed, pool, state]++R) mem (poolSwapGuardsAW aw fee params) rdata σ k' C'
      else RDrev (deployedRuntime v) g s0
    else RDrev (deployedRuntime v) g s0 := by
  have ht0 := poolSwapModeTrace v (by change R.length+6+11 ≤ 1024; omega) hf hs h
  by_cases hmode : poolSwapModeValid fee p.amountSpecified
  · rw [if_pos hmode] at ht0 ⊢
    obtain ⟨k1, C1, hc1, rd1⟩ := ht0
    have ht1 := poolSwapZeroTrace v (by change R.length+16 ≤ 1024; omega) hs hret rd1
    by_cases hz : p.amountSpecified = ⟨0⟩
    · rw [if_pos hz] at ht1 ⊢
      obtain ⟨k2, C2, hc2, rd2⟩ := ht1
      exact ⟨k2, C2, by omega, rd2⟩
    · rw [if_neg hz] at ht1 ⊢
      obtain ⟨k2, C2, hc2, rd2⟩ := ht1
      have ht2 := poolSwapLimitTrace v p.zeroForOne (by change R.length+3+14 ≤ 1024; omega) hl hm rd2
      by_cases hv : poolSwapLimitValid packed p.priceLimit p.zeroForOne
      · rw [if_pos hv] at ht2 ⊢
        obtain ⟨k3, C3, hc3, rd3⟩ := ht2
        exact ⟨k3, C3, by omega, rd3⟩
      · rw [if_neg hv] at ht2 ⊢
        exact ht2
  · rw [if_neg hmode] at ht0 ⊢
    exact ht0

end Benchmarks.UniswapV4PoolManager
