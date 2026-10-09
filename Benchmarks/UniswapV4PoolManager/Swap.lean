import Benchmarks.UniswapV4PoolManager.Dispatch

/-!
# PoolManager `swap((address,address,uint24,int24,address),(bool,int256,uint160),bytes)`

Per-function proof: calldata decode facts, the EVM trace from the dispatcher arm through the
body, the Solm body evaluation, and the `…Body` theorem `Correct.lean` consumes.
Dispatcher arm entry: pc 1279; reach lemma `poolManagerReachSwapBody`.
-/

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables
open Benchmarks.UniswapV4PoolManager.Immutables

namespace Benchmarks.UniswapV4PoolManager

set_option maxRecDepth 2000000

/-- `swap((address,address,uint24,int24,address),(bool,int256,uint160),bytes)`: the theorem `Correct.lean` routes selector 24 to. -/
theorem poolManagerSwapBody {σ σ₀ A I} {g : UInt256} (v : PoolManagerImmutables)
    (hcode : I.code = deployedRuntime v) (hsize : I.calldata.size < UInt256.size)
    (hWF : Syntax.poolManagerWF σ I)
    (hGas : Syntax.poolManagerGasBound g)
    (hsel : selIs I (poolManagerSelBytes 24)) :
    runtimeRefinementFor config contract σ σ₀ g A I (immStore v) := by
  have hsz : 4 ≤ I.calldata.size := calldata_size_ge_of_selIs I (poolManagerSelBytes 24) rfl hsel
  sorry

end Benchmarks.UniswapV4PoolManager
