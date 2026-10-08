import Benchmarks.Morpho.MorphoBlue.Dispatch

/-!
# Morpho `DOMAIN_SEPARATOR()`

Per-function proof: calldata decode facts, the EVM trace from the dispatcher arm through the
body, the Solm body evaluation, and the `…Body` theorem `Correct.lean` consumes.
Dispatcher arm entry: pc 9347; reach lemma `morphoReachDOMAIN_SEPARATORBody`.
-/

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables
open Benchmarks.Morpho.MorphoBlue.Immutables

namespace Benchmarks.Morpho.MorphoBlue

set_option maxRecDepth 2000000

/-- `DOMAIN_SEPARATOR()`: the theorem `Correct.lean` routes selector 5 to. -/
theorem morphoDOMAIN_SEPARATORBody {σ σ₀ A I} {g : UInt256} (v : MorphoImmutables)
    (hcode : I.code = deployedRuntime v) (hsize : I.calldata.size < UInt256.size)
    (hsel : selIs I (morphoSelBytes 5)) :
    runtimeRefinementFor config contract σ σ₀ g A I (immStore v) := by
  have hsz : 4 ≤ I.calldata.size := calldata_size_ge_of_selIs I (morphoSelBytes 5) rfl hsel
  sorry

end Benchmarks.Morpho.MorphoBlue
