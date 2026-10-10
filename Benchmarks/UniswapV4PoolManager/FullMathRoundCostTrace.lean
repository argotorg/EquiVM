import Benchmarks.UniswapV4PoolManager.FullMathRoundTrace
import Benchmarks.UniswapV4PoolManager.ReachCost

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables
open Benchmarks.UniswapV4PoolManager.Immutables
namespace Benchmarks.UniswapV4PoolManager

theorem fullMathRoundCostTrace {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem rdata : ByteArray} {aw a b d ret : UInt256} {σ : AccountMap} {k C : Nat} {R : List UInt256}
    (v : PoolManagerImmutables) (hstack : R.length+14 ≤ 1024)
    (hret : (D_J (deployedRuntime v) 0).contains ret = true)
    (h : RD (deployedRuntime v) I g s0 ⟨23656⟩ (a :: b :: d :: ret :: R) mem aw rdata σ k C) :
    (fullMathRoundFits a b d → ∃ k' C', C ≤ C' ∧
      RD (deployedRuntime v) I g s0 ret (fullMathRoundWord a b d :: R) mem aw rdata σ k' C') ∧
    (¬fullMathRoundFits a b d → RDrev (deployedRuntime v) g s0) := by
  constructor
  · intro hf
    exact RD_retainCost (fun _ _ hin => by
      have hr := fullMathRoundTrace (a := a) (b := b) (d := d) v hstack hret hin
      simpa only [if_pos hf] using hr) h
  · intro hf
    have hr := fullMathRoundTrace (a := a) (b := b) (d := d) v hstack hret h
    simpa only [if_neg hf] using hr

end Benchmarks.UniswapV4PoolManager
