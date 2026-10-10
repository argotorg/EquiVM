import Benchmarks.UniswapV3.Pool.TickSqrtInternal
import Benchmarks.UniswapV3.Pool.ReachRoutineReturnCost

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables Benchmarks.UniswapV3.Pool.Immutables
namespace Benchmarks.UniswapV3.Pool

theorem tickSqrtCanonicalMonoX {σ : AccountMap} {ee : ExecutionEnv} {g : Sat256}
    {s0 : EVM.State} {k C : Nat} {aw ret : UInt256} {mem rdata : ByteArray}
    {R : List UInt256} {v : UniswapV3PoolImmutables} (tick : Int)
    (rd : RD (deployedRuntime v) ee g s0 ⟨11629⟩
      (EVM.wordOfInt tick :: ret :: R) mem aw rdata σ k C)
    (hlo : -(2 ^ 23 : Int) ≤ tick) (hhi : tick < 2 ^ 23) (ht : tick.natAbs ≤ 887272)
    (hret : (D_J (deployedRuntime v) 0).contains ret = true) (hov : R.length + 9 ≤ 1024) :
    ∃ k' C', C ≤ C' ∧ RD (deployedRuntime v) ee g s0 ret
      (tickSqrtValue tick :: R) mem aw rdata σ k' C' := by
  apply rdRoutine_return_mono rd
  intro gas start rr
  exact tickSqrtCanonicalX tick rr hlo hhi ht hret hov

end Benchmarks.UniswapV3.Pool
