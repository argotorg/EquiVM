import Benchmarks.CompoundIII.Comet.Dispatch

/-!
# CometWithExtendedAssetList `transferAssetFrom(address,address,address,uint256)`

Per-function proof: calldata decode facts, the EVM trace from the dispatcher arm through the
body, the Solm body evaluation, and the `…Body` theorem `Correct.lean` consumes.
Dispatcher arm entry: pc 916; reach lemma `cometWithExtendedAssetListReachTransferAssetFromBody`.
-/

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables
open Benchmarks.CompoundIII.Comet.Immutables

namespace Benchmarks.CompoundIII.Comet

set_option maxRecDepth 2000000

/-- `transferAssetFrom(address,address,address,uint256)`: the theorem `Correct.lean` routes selector 53 to. -/
theorem cometWithExtendedAssetListTransferAssetFromBody {σ σ₀ A I} {g : UInt256} (v : CometWithExtendedAssetListImmutables)
    (hcode : I.code = deployedRuntime v) (hsize : I.calldata.size < UInt256.size)
    (hsel : selIs I (cometWithExtendedAssetListSelBytes 53)) :
    runtimeRefinementFor config contract σ σ₀ g A I (immStore v) := by
  have hsz : 4 ≤ I.calldata.size := calldata_size_ge_of_selIs I (cometWithExtendedAssetListSelBytes 53) rfl hsel
  sorry

end Benchmarks.CompoundIII.Comet
