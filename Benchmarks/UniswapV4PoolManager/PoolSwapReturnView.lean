import Benchmarks.UniswapV4PoolManager.PoolSwapBodyReturn
import Benchmarks.UniswapV4PoolManager.PoolSwapReturnMemory

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Benchmarks.UniswapV4PoolManager.Immutables
namespace Benchmarks.UniswapV4PoolManager

theorem poolSwapBodyReturn_view {v : PoolManagerImmutables} {I : ExecutionEnv} {g : Sat256}
    {s0 evm post : State} {mem rdata : ByteArray} {id state params ret : UInt256}
    {p : PoolSwapParamsWords} {R : List UInt256} {C : Nat} {values : Option (List Value)}
    (hI : evm.executionEnv = I) (hσ0 : evm.σ₀ = s0.σ₀)
    (hl : 96 ≤ state.toNat) (hf : state.toNat+352 < UInt256.size)
    (h : poolSwapBodyReturn v I g s0 evm mem rdata id state params ret p R C post values) :
    ∃ r delta amount out free aw k' C', post.executionEnv = I ∧ post.σ₀ = s0.σ₀ ∧
      values = some (poolSwapReturnValues delta (poolSwapInitialFee evm id p) amount r) ∧ C ≤ C' ∧ Cₘ aw ≤ C' ∧
      RD (deployedRuntime v) I g s0 ret
        ([state, poolSwapInitialFee evm id p, amount, delta]++R) out aw rdata post.accountMap k' C' ∧
      PoolSwapReturnMemory mem out state free r ∧ r.price.toNat < 2^160 ∧ int24Canonical r.tick ∧
      r.liquidity.toNat < 2^128 := by
  rcases h with ⟨rfl, hv, aw, k', C', hc, hpaid, rd⟩ | h
  · exact ⟨_, ⟨0⟩, ⟨0⟩, _, state+UInt256.ofNat 96, aw, k', C', hI, hσ0, hv, hc, hpaid, rd,
      poolSwapAllocatedReturnMemory _ _ _ _ hl (by omega), solcAddrMask_result_canonical _,
      slot0TickWord_canonical _, poolLiquidity_bound _ id⟩
  · obtain ⟨s, r, delta, amount, out, aw, k', C', hI', hσ', hv, hc, hpaid, rd, hm, hp, ht, hliq, hw⟩ := h
    exact ⟨r, delta, amount, out, state+UInt256.ofNat 352, aw, k', C', hI', hσ', hv, hc, hpaid, rd,
      poolSwapLoopReturnMemory hl hf hm.resultFields hw, hp, ht, hliq⟩

end Benchmarks.UniswapV4PoolManager
