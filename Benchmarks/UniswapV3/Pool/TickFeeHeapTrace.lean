import Benchmarks.UniswapV3.Pool.TickFeeTrace
import Benchmarks.UniswapV3.Pool.TickFeeMemory

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables Benchmarks.UniswapV3.Pool.Immutables
namespace Benchmarks.UniswapV3.Pool

theorem tickFeeHeapX {σ : AccountMap} {ee : ExecutionEnv} {g : Sat256}
    {s0 : EVM.State} {k C : Nat} {aw ret p : UInt256} {mem rdata : ByteArray}
    {R : List UInt256} {v : UniswapV3PoolImmutables} (a : TickFeeArgs)
    (rd : RD (deployedRuntime v) ee g s0 ⟨21387⟩
      (a.global1 :: a.global0 :: EVM.wordOfInt a.current :: EVM.wordOfInt a.upper ::
        EVM.wordOfInt a.lower :: ⟨5⟩ :: ret :: R) mem aw rdata σ k C)
    (hfit : a.Fits) (hm : HeapMemory mem aw p)
    (hret : (D_J (deployedRuntime v) 0).contains ret = true) (hov : R.length + 18 ≤ 1024) :
    ∃ k' C', RD (deployedRuntime v) ee g s0 ret
      (tickFeeInside a σ ee true :: tickFeeInside a σ ee false :: R)
      (tickFeeMemory mem a) aw rdata σ k' C' ∧ HeapMemory (tickFeeMemory mem a) aw p := by
  obtain ⟨k', C', r'⟩ := tickFeeExactX (v := v) a rd hfit hret hov
  rw [tickFeeMemoryWords_eq hm.active] at r'
  exact ⟨k', C', r', tickFeeMemory_heap hm a⟩

end Benchmarks.UniswapV3.Pool
