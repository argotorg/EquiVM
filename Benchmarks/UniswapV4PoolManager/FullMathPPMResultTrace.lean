import Benchmarks.UniswapV4PoolManager.FullMathPPMTrace

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables
open Benchmarks.UniswapV4PoolManager.Immutables
namespace Benchmarks.UniswapV4PoolManager

/-- A branch interface that does not reduce symbolic arithmetic when instantiated. -/
theorem fullMathPPMResultTrace {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem rdata : ByteArray} {aw a b ret : UInt256} {σ : AccountMap} {k C : Nat} {R : List UInt256}
    (v : PoolManagerImmutables) (hstack : R.length+9 ≤ 1024)
    (hret : (D_J (deployedRuntime v) 0).contains ret = true)
    (h : RD (deployedRuntime v) I g s0 ⟨22405⟩ (a :: b :: ret :: R) mem aw rdata σ k C) :
    (fullMathFits a b fullMathPPM → ∃ k' C', C ≤ C' ∧
      RD (deployedRuntime v) I g s0 ret (fullMathWord a b fullMathPPM :: R) mem aw rdata σ k' C') ∧
    (¬fullMathFits a b fullMathPPM → RDrev (deployedRuntime v) g s0) := by
  have hr := fullMathPPMTrace v hstack hret h
  constructor
  · intro hfit
    rwa [if_pos hfit] at hr
  · intro hfit
    rwa [if_neg hfit] at hr

end Benchmarks.UniswapV4PoolManager
