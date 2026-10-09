import Benchmarks.UniswapV3.Pool.Dispatch

/-!
# UniswapV3Pool `setFeeProtocol(uint8,uint8)`

Per-function proof: calldata decode facts, the EVM trace from the dispatcher arm through the
body, the Solm body evaluation, and the `…Body` theorem `Correct.lean` consumes.
Dispatcher arm entry: pc 1486; reach lemma `uniswapV3PoolReachSetFeeProtocolBody`.
-/

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables
open Benchmarks.UniswapV3.Pool.Immutables

namespace Benchmarks.UniswapV3.Pool

set_option maxRecDepth 2000000

/-- `setFeeProtocol(uint8,uint8)`: the theorem `Correct.lean` routes selector 14 to. -/
theorem uniswapV3PoolSetFeeProtocolBody {σ σ₀ A I} {g : UInt256} (v : UniswapV3PoolImmutables)
    (hcode : I.code = deployedRuntime v) (hsize : I.calldata.size < UInt256.size)
    (hwv : I.weiValue = ⟨0⟩)
    (hsel : selIs I (uniswapV3PoolSelBytes 14)) :
    runtimeRefinementFor config contract σ σ₀ g A I (immStore v) := by
  have hsz : 4 ≤ I.calldata.size := calldata_size_ge_of_selIs I (uniswapV3PoolSelBytes 14) rfl hsel
  sorry

end Benchmarks.UniswapV3.Pool
