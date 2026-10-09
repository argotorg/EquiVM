import Benchmarks.UniswapV4PoolManager.Dispatch

/-!
# PoolManager `transferOwnership(address)`

Per-function proof: calldata decode facts, the EVM trace from the dispatcher arm through the
body, the Solm body evaluation, and the `…Body` theorem `Correct.lean` consumes.
Dispatcher arm entry: pc 2120; reach lemma `poolManagerReachTransferOwnershipBody`.
-/

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables
open Benchmarks.UniswapV4PoolManager.Immutables

namespace Benchmarks.UniswapV4PoolManager

set_option maxRecDepth 2000000

/-- `transferOwnership(address)`: the theorem `Correct.lean` routes selector 29 to. -/
theorem poolManagerTransferOwnershipBody {σ σ₀ A I} {g : UInt256} (v : PoolManagerImmutables)
    (hcode : I.code = deployedRuntime v) (hsize : I.calldata.size < UInt256.size)
    (hWF : Syntax.poolManagerWF σ I)
    (hGas : Syntax.poolManagerGasBound g)
    (hsel : selIs I (poolManagerSelBytes 29)) :
    runtimeRefinementFor config contract σ σ₀ g A I (immStore v) := by
  have hsz : 4 ≤ I.calldata.size := calldata_size_ge_of_selIs I (poolManagerSelBytes 29) rfl hsel
  sorry

end Benchmarks.UniswapV4PoolManager
