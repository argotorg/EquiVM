import Benchmarks.UniswapV4PoolManager.PoolSwapProtocolLoadTrace
import Benchmarks.UniswapV4PoolManager.PoolSwapResultLoadTrace
import Benchmarks.UniswapV4PoolManager.PoolSwapLPSelectTrace
import Benchmarks.UniswapV4PoolManager.PoolSwapFeeInitTrace
import Benchmarks.UniswapV4PoolManager.PoolSwapFeesSource
import Benchmarks.UniswapV4PoolManager.PoolSwapResultActiveWords

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Benchmarks.UniswapV4PoolManager.Immutables
namespace Benchmarks.UniswapV4PoolManager
set_option maxRecDepth 5000

theorem poolSwapFeesTrace {I : ExecutionEnv} {g : Sat256} {s0 evm : State}
    {mem rdata : ByteArray} {aw id state params ret : UInt256} {p : PoolSwapParamsWords}
    {k C : Nat} {R : List UInt256}
    (v : PoolManagerImmutables) (hstack : R.length+17 ≤ 1024) (hI : evm.executionEnv = I)
    (hfit : state.toNat+96 < UInt256.size) (hbefore : params.toNat+160 ≤ state.toNat)
    (hz : memLoad (params+UInt256.ofNat 64) (poolSwapResultZeroMem mem state) = UInt256.fromBool p.zeroForOne)
    (hs : memLoad params (poolSwapResultZeroMem mem state) = p.amountSpecified)
    (ho : memLoad (params+UInt256.ofNat 128) (poolSwapLoadedMem mem evm id state) = p.lpFeeOverride)
    (h : RD (deployedRuntime v) I g s0 ⟨18793⟩
      ([⟨0⟩, params, ret, poolSlot id, state]++R) mem aw rdata evm.accountMap k C) :
    if poolSwapLPFeeValid p.lpFeeOverride then
      ∃ k' C', C ≤ C' ∧ C+Cₘ (poolSwapLoadedAW aw state params) ≤ C'+Cₘ aw ∧
        RD (deployedRuntime v) I g s0 ⟨18951⟩
        ([poolSwapInitialFee evm id p, slot0SqrtPriceWord (poolSlot0Word evm id), ret, params, p.amountSpecified,
          ⟨0⟩, state, poolSwapProtocolWord (poolSlot0Word evm id) p.zeroForOne, ⟨0⟩,
          UInt256.fromBool (!p.zeroForOne), poolSlot0Word evm id, poolSlot id, state]++R)
        (poolSwapLoadedMem mem evm id state) (poolSwapLoadedAW aw state params) rdata evm.accountMap k' C'
    else RDrev (deployedRuntime v) g s0 := by
  obtain ⟨k1, C1, hc1, hp1, rd1⟩ := poolSwapProtocolLoadTrace v (by omega) hI hz h
  obtain ⟨k2, C2, hc2, rd2⟩ := poolSwapResultLoadTrace v (by omega) hI hs ho rd1
  have ht := poolSwapLPSelectTrace v (by change R.length+2+15 ≤ 1024; omega) rd2
  by_cases hv : poolSwapLPFeeValid p.lpFeeOverride
  · rw [if_pos hv] at ht ⊢
    obtain ⟨k3, C3, hc3, rd3⟩ := ht
    obtain ⟨k4, C4, hc4, rd4⟩ := poolSwapFeeInitTrace v (by change R.length+5+12 ≤ 1024; omega)
      (poolSwapProtocolWord_bound _ _) (poolSwapLPFeeWord_bound _ _) rd3
    refine ⟨k4, C4, by omega, ?_, rd4⟩
    rw [poolSwapLoadedAW_eq hfit hbefore]
    omega
  · rw [if_neg hv] at ht ⊢
    exact ht

end Benchmarks.UniswapV4PoolManager
