import Benchmarks.Morpho.MetaMorphoV1_1.Dispatch

/-!
# MetaMorphoV1_1 `convertToAssets(uint256)`

Per-function proof: calldata decode facts, the EVM trace from the dispatcher arm through the
body, the Solm body evaluation, and the `…Body` theorem `Correct.lean` consumes.
Dispatcher arm entry: pc 7734; reach lemma `metaMorphoV1_1ReachConvertToAssetsBody`.
-/

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables
open Benchmarks.Morpho.MetaMorphoV1_1.Immutables

namespace Benchmarks.Morpho.MetaMorphoV1_1

set_option maxRecDepth 2000000

/-- `convertToAssets(uint256)`: the theorem `Correct.lean` routes selector 2 to. -/
theorem metaMorphoV1_1ConvertToAssetsBody {σ σ₀ A I} {g : UInt256} (v : MetaMorphoV1_1Immutables)
    (hcode : I.code = deployedRuntime v) (hsize : I.calldata.size < UInt256.size)
    (hsel : selIs I (metaMorphoV1_1SelBytes 2)) :
    runtimeRefinementFor config contract σ σ₀ g A I (immStore v) := by
  have hsz : 4 ≤ I.calldata.size := calldata_size_ge_of_selIs I (metaMorphoV1_1SelBytes 2) rfl hsel
  sorry

end Benchmarks.Morpho.MetaMorphoV1_1
