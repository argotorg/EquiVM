import Benchmarks.UniswapV4PoolManager.TickSqrtTrace
import Benchmarks.UniswapV4PoolManager.WordSignextend24

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Benchmarks.UniswapV4PoolManager.Immutables
namespace Benchmarks.UniswapV4PoolManager

theorem tickSqrtCanonicalTrace {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem rdata : ByteArray} {aw ret tick : UInt256} {σ : AccountMap} {k C : Nat} {R : List UInt256}
    (v : PoolManagerImmutables) (hstack : R.length+7 ≤ 1024)
    (hc : int24Canonical tick) (hb : (EVM.signed tick).natAbs ≤ 887272)
    (hret : (D_J (deployedRuntime v) 0).contains ret = true)
    (h : RD (deployedRuntime v) I g s0 ⟨16728⟩ (tick :: ret :: R) mem aw rdata σ k C) :
    ∃ k' C', RD (deployedRuntime v) I g s0 ret (tickSqrtPrice (EVM.signed tick) :: R) mem aw rdata σ k' C' := by
  have hr := tickSqrtTrace v hstack hret h
  have he : UInt256.signextend (UInt256.ofNat 2) tick = tick := (signextend24_eq_iff tick).mpr hc
  rw [he] at hr
  rcases hr with ⟨hbad, _⟩ | ⟨_, hr⟩
  · omega
  · exact hr

end Benchmarks.UniswapV4PoolManager
