import Benchmarks.Morpho.MorphoBlue.Dispatch

/-!
# Morpho `setAuthorizationWithSig((address,address,bool,uint256,uint256),(uint8,bytes32,bytes32))`

Per-function proof: calldata decode facts, the EVM trace from the dispatcher arm through the
body, the Solm body evaluation, and the `…Body` theorem `Correct.lean` consumes.
Dispatcher arm entry: pc 5759; reach lemma `morphoReachSetAuthorizationWithSigBody`.
-/

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables
open Benchmarks.Morpho.MorphoBlue.Immutables

namespace Benchmarks.Morpho.MorphoBlue

set_option maxRecDepth 2000000

/-- `setAuthorizationWithSig((address,address,bool,uint256,uint256),(uint8,bytes32,bytes32))`: the theorem `Correct.lean` routes selector 27 to. -/
theorem morphoSetAuthorizationWithSigBody {σ σ₀ A I} {g : UInt256} (v : MorphoImmutables)
    (hcode : I.code = deployedRuntime v) (hsize : I.calldata.size < UInt256.size)
    (hsel : selIs I (morphoSelBytes 27)) :
    runtimeRefinementFor config contract σ σ₀ g A I (immStore v) := by
  have hsz : 4 ≤ I.calldata.size := calldata_size_ge_of_selIs I (morphoSelBytes 27) rfl hsel
  sorry

end Benchmarks.Morpho.MorphoBlue
