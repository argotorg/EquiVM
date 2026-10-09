import Benchmarks.UniswapV3.Pool.Dispatch

/-!
# UniswapV3Pool `increaseObservationCardinalityNext(uint16)`

Per-function proof: calldata decode facts, the EVM trace from the dispatcher arm through the
body, the Solm body evaluation, and the `…Body` theorem `Correct.lean` consumes.
Dispatcher arm entry: pc 824; reach lemma `uniswapV3PoolReachIncreaseObservationCardinalityNextBody`.
-/

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables
open Benchmarks.UniswapV3.Pool.Immutables

namespace Benchmarks.UniswapV3.Pool

set_option maxRecDepth 2000000

/-- `increaseObservationCardinalityNext(uint16)`: the theorem `Correct.lean` routes selector 5 to. -/
theorem uniswapV3PoolIncreaseObservationCardinalityNextBody {σ σ₀ A I} {g : UInt256} (v : UniswapV3PoolImmutables)
    (hcode : I.code = deployedRuntime v) (hsize : I.calldata.size < UInt256.size)
    (hwv : I.weiValue = ⟨0⟩)
    (hsel : selIs I (uniswapV3PoolSelBytes 5)) :
    runtimeRefinementFor config contract σ σ₀ g A I (immStore v) := by
  have hsz : 4 ≤ I.calldata.size := calldata_size_ge_of_selIs I (uniswapV3PoolSelBytes 5) rfl hsel
  sorry

end Benchmarks.UniswapV3.Pool
