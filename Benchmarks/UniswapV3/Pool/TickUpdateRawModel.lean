import Benchmarks.UniswapV3.Pool.TickUpdateModel

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.UniswapV3.Pool

def TickUpdateArgs.TraceFits (a : TickUpdateArgs) : Prop :=
  (-(2 ^ 23 : Int) ≤ a.tick ∧ a.tick < 2 ^ 23) ∧
  (-(2 ^ 23 : Int) ≤ a.current ∧ a.current < 2 ^ 23) ∧
  (-(2 ^ 127 : Int) ≤ a.delta ∧ a.delta < 2 ^ 127) ∧
  a.secondsPerLiquidity.toNat < 2 ^ 160 ∧
  (-(2 ^ 55 : Int) ≤ a.cumulative ∧ a.cumulative < 2 ^ 55)

theorem TickUpdateArgs.Fits.traceFits {a : TickUpdateArgs} (h : a.Fits) : a.TraceFits :=
  ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2.1⟩

end Benchmarks.UniswapV3.Pool
