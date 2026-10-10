import Benchmarks.UniswapV4PoolManager.MemoryGas

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.UniswapV4PoolManager

-- LIBRARY CANDIDATE: a reached cursor whose memory has been paid for is bounded by the gas budget.
theorem memoryPaidBound {code : ByteArray} {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {pc aw bound : UInt256} {stack : List UInt256} {mem rdata : ByteArray} {σ : AccountMap}
    {k C : Nat} (hbudget : g.toNat < Cₘ bound) (hpaid : Cₘ aw ≤ C)
    (h : RD code I g s0 pc stack mem aw rdata σ k C) :
    X (g.toNat+1) (D_J code 0) s0 = .error .OutOfGass ∨ aw.toNat < bound.toNat := by
  by_cases hb : aw.toNat < bound.toNat
  · exact .inr hb
  · have hc := memoryCost_mono (Nat.le_of_not_gt hb)
    exact .inl (RD.oog_of_cost_gt h (by omega))

end Benchmarks.UniswapV4PoolManager
