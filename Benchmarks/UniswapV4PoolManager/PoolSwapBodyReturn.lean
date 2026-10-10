import Benchmarks.UniswapV4PoolManager.PoolSwapPreludeTrace
import Benchmarks.UniswapV4PoolManager.PoolSwapLoopFinishCorrect

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Benchmarks.UniswapV4PoolManager.Immutables
namespace Benchmarks.UniswapV4PoolManager

def poolSwapBodyReturn (v : PoolManagerImmutables) (I : ExecutionEnv) (g : Sat256) (s0 evm : State)
    (mem rdata : ByteArray) (id state params ret : UInt256) (p : PoolSwapParamsWords) (R : List UInt256) (C : Nat)
    (post : State) (values : Option (List Value)) : Prop :=
  (post = evm ∧ values = some (poolSwapReturnValues ⟨0⟩ (poolSwapInitialFee evm id p) ⟨0⟩
      (poolSwapInitialResult (poolSlot0Word evm id) (poolLiquidityWord evm id))) ∧
    ∃ aw k' C', C ≤ C' ∧ Cₘ aw ≤ C' ∧ RD (deployedRuntime v) I g s0 ret
      ([state, poolSwapInitialFee evm id p, ⟨0⟩, ⟨0⟩]++R)
      (poolSwapAllocatedMem mem evm id state) aw rdata evm.accountMap k' C') ∨
  poolSwapLoopReturn v I g s0 rdata (poolSwapPreludeMem mem evm id state p.zeroForOne) p
    (state+UInt256.ofNat 96) state params ret (poolSwapInitialFee evm id p) R C post values

theorem poolSwapBodyReturn_of_loop {v : PoolManagerImmutables} {I : ExecutionEnv} {g : Sat256} {s0 evm post : State}
    {mem rdata : ByteArray} {id state params ret : UInt256} {p : PoolSwapParamsWords} {R : List UInt256}
    {C C1 : Nat} {values : Option (List Value)} (hc : C ≤ C1)
    (h : poolSwapLoopReturn v I g s0 rdata (poolSwapPreludeMem mem evm id state p.zeroForOne) p
      (state+UInt256.ofNat 96) state params ret (poolSwapInitialFee evm id p) R C1 post values) :
    poolSwapBodyReturn v I g s0 evm mem rdata id state params ret p R C post values := by
  right
  obtain ⟨s, r, delta, amount, out, aw, k', C', hI, hσ, hv, hC, hpaid, hr, hm, hp, ht, hl, hw⟩ := h
  exact ⟨s, r, delta, amount, out, aw, k', C', hI, hσ, hv, hc.trans hC, hpaid, hr, hm, hp, ht, hl, hw⟩

end Benchmarks.UniswapV4PoolManager
